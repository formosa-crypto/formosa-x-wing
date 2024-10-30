require import AllCore KEM_ROM PROM Distr StdOrder SmtMap List.
require (****) NomGroup.

clone import NomGroup as NG.
import EH EU ZModField.

clone KEM.

type shkey.
op [full uniform lossless]dshkey : shkey distr.

type pkey = KEM.pkey * G.
type skey = KEM.skey * ehT * G.
type ciphertext = KEM.ciphertext * G.

type label.
op label : label.

clone import KEM_ROM as XWING_DEFS with
   type RO.in_t = label * KEM.key * G * G * G
   type RO.out_t <- shkey
   op RO.dout = fun _ => dshkey
   type key <- shkey
   type pkey <- pkey
   type skey <- skey
   type ciphertext <- ciphertext
   op dkey <- dshkey
   proof dkey_ll by apply dshkey_ll
   proof dkey_fu by apply dshkey_fu
   proof dkey_uni by apply dshkey_uni
   proof *.

import RO.

module XWING(KEMS : KEM.Scheme, O : POracle)  = {
  proc kg() : pkey * skey = {
    var sk1,pk1,sk2,pk2,pk,sk;
    (pk1,sk1) <@ KEMS.kg();
    sk2 <$ dH;
    pk2 <- exp g (val sk2);
    pk <- (pk1,pk2);
    sk <- (sk1,sk2,pk2);
    return(pk,sk);
  }

  proc enc(pk : pkey) : ciphertext * shkey = {
    var pk1,pk2,k1,c1,ske,c2,k2,k,c;
    (pk1,pk2) <- pk;
    (c1,k1) <@ KEMS.enc(pk1);
    ske <$ dH;
    c2 <- exp g (val ske);
    k2 <- exp pk2 (val ske);
    k <@ O.get(label,k1,k2,c2,pk2);
    c <- (c1,c2);
    return (c,k);
  }

  proc dec(sk : skey, c : ciphertext) : shkey option  = {
    var sk1,sk2,pk2,c1,c2,k1,k2,k;
    (sk1,sk2,pk2) <- sk;
    (c1,c2) <- c;
    k1 <@ KEMS.dec(sk1,c1);
    k2 <- exp c2 (val sk2);
    k <@ O.get(label,oget k1,k2,c2,pk2);
    return if k1 = None then None else Some k;
  }
}.

module XWING1(KEMS : KEM.Scheme, O : POracle) = {
  var _sk1 : KEM.skey (* fixed in key generation *)
  var _sk2 : euT      (* fixed in key generation *)
  var _pk2 : G        (* fixed in key generation *)
  var _rv2 : euT      (* fixed in enc *)
  var _c2  : G        (* fixed in enc *)
  var _kb1 : KEM.key  (* fixed in enc *)

  proc kg() : pkey * skey = {
    var pk1,pk;
    (pk1,_sk1) <@ KEMS.kg();
    _sk2 <$ dU;
    _pk2 <- g^_sk2;
    pk <- (pk1,_pk2);
    return(pk,witness);
  }

  proc enc(pk : pkey) : ciphertext * shkey = {
    var pk1,pk2,c1,k2,k,c;
    (pk1,pk2) <- pk;
    (c1,_kb1) <@ KEMS.enc(pk1);
    _rv2 <$ dU;
    _c2 <- g^_rv2;
    k2 <- _pk2^_rv2;
    k <@ O.get(label,_kb1,k2,_c2,_pk2);
    c <- (c1,_c2);
    return (c,k);
  }

  proc dec(sk : skey, c : ciphertext) : shkey option  = {
    var c1,c2,k1,k2,k;
    (c1,c2) <- c;
    k1 <@ KEMS.dec(_sk1,c1);
    k2 <- c2^_sk2;
    k <@ O.get(label,oget k1,k2,c2,_pk2);
    return if k1 = None then None else Some k;
  }

}.

clone SDist.Dist as SD with (* FIXME: Clear warnings *)
   type a <- int
   proof *.

clone SD.N1 as SDD with
   op N <- 2
   op d1 = dmap dH EH.val
   op d2 = dmap dU (asint \o EU.val)
   proof N_ge0 by auto
   proof d1_ll by (rewrite /d1;apply dmap_ll;apply dH_ll)
   proof d2_ll by (rewrite /d2;apply dmap_ll;apply dU_ll)
   proof *.

module XWING_EG(KEMS : KEM.Scheme, EG : SD.Oracle, O : POracle) = {
    var _sk1 : KEM.skey
    var _sk2 : int
    var _pk2 : G

    proc kg() : pkey * skey = {
      var pk1,pk;
      (pk1,_sk1) <@ KEMS.kg();
      _sk2 <@ EG.get();
      _pk2 <- exp g _sk2;
      pk <- (pk1,_pk2);
      return(pk,witness);
    }

    proc enc(pk : pkey) : ciphertext * shkey = {
      var pk1,k1,c1,ske,c2,k2,k,c;
      (pk1,_pk2) <- pk;
      (c1,k1) <@ KEMS.enc(pk1);
      ske <@ EG.get();

      c2 <- exp g ske;
      k2 <- exp _pk2 ske;
      k <@ O.get(label,k1,k2,c2,_pk2);
      c <- (c1,c2);
      return (c,k);
    }

   proc dec(sk : skey, c : ciphertext) : shkey option  = {
     var c1,c2,k1,k2,k;
     (c1,c2) <- c;
     k1 <@ KEMS.dec(_sk1,c1);
     k2 <- exp c2 _sk2;
     k <@ O.get(label,oget k1,k2,c2,_pk2);
     return if k1 = None then None else Some k;
   }
  }.

(* This is to avoid an anomaly when using submodules to
   instantiate lemmas *)
module CCAOO(H : Oracle, S : Scheme) = {
    proc dec(c : ciphertext) : shkey option = {
      var k : shkey option;
      k <- None;
      if (Some c <> CCA.cstar) {
        k <@ S(H).dec(CCA.sk, c);
      }
      return k;
    }
}.

module (SDAdv(KEMS : KEM.Scheme, H : Oracle, A : CCA_ADV) : SD.Adversary) (EG : SD.Oracle) = {

(*
   proc main() : bool = {
      var b;
      b <@ CCA(RO,XWING_EG(KEMS,EG),A).main();
      return b;
*)
  proc main() : bool = {
    var pk : pkey;
    var k1 : shkey;
    var ck0 : ciphertext * shkey;
    var b : bool;
    var b' : bool;

    H.init();
    CCA.cstar <- None;
    (pk, CCA.sk) <@ XWING_EG(KEMS,EG,H).kg();
    k1 <$ dshkey;
    b <$ {0,1};
    ck0 <@ XWING_EG(KEMS,EG,H).enc(pk);
    CCA.cstar <- Some ck0.`1;
    b' <@ A(H,CCAOO(H,XWING_EG(KEMS,EG))).guess(pk, ck0.`1, if b then k1 else ck0.`2);

    return b' = b;
  }
}.


section.

  declare module A <: CCA_ADV {-XWING_EG, -CCA, -SD.Os, -SD.Count, -SD.B1, -XWING1}.
  declare module KEMS <: KEM.Scheme {-A, -XWING_EG, -CCA, -SD.Os, -SD.Count, -SD.B1, -XWING1}.
  declare module RO <: Oracle {-A, -KEMS, -XWING_EG, -CCA, -SD.Os, -SD.Count, -SD.B1, -XWING1}.

  declare axiom RO_initll : islossless RO.init.
  declare axiom RO_getll : islossless RO.get.
  declare axiom KEMS_kgll : islossless KEMS.kg.
  declare axiom KEMS_encll : islossless KEMS.enc.
  declare axiom KEMS_decll : islossless KEMS.dec.
  declare axiom All (O <: POracle) (CCAO <: CCA_ORC):
      islossless O.get => islossless CCAO.dec =>  islossless A(O,CCAO).guess.

  local module Aux(O : SD.Oracle) = CCA(RO, XWING_EG(KEMS,O), A).O.

  lemma hop1 &m :
    `| Pr [ CCA(RO,XWING(KEMS),A).main() @ &m : res ] -
         Pr [ CCA(RO,XWING1(KEMS),A).main() @ &m : res ] | <= 2%r * sdist_dU_dH.
  have -> : Pr [ CCA(RO,XWING(KEMS),A).main() @ &m : res ] =
       Pr [ SD.Game(SDAdv(KEMS,RO,A),SD.Os).main(SDD.d1) @ &m : res ].
  + byequiv => //.
    proc.
    inline {2} 2;wp; conseq (: ={b',b});1: smt().
     call(: ={glob RO, glob KEMS, CCA.cstar}
          /\ CCA.sk{1}.`1 = XWING_EG._sk1{2}
          /\ val CCA.sk{1}.`2 = XWING_EG._sk2{2}
          /\ CCA.sk{1}.`3 = XWING_EG._pk2{2}).
     + proc;inline *.
       seq 1 1 : (#pre /\ ={k}); 1: by auto.
       if; 1,3: by auto.
       wp;   call(:true).
       wp;   call(:true).
       by auto => />.
     + by conseq />;sim.
     inline *.
     wp;   call(:true).
     swap {1} 4 -3; swap {1} 14 -12.
     swap {2} 3 -1; swap {2} 4 -1; swap {2} 9 -5; swap {2} 21 -16.
     seq 2 5: (#pre /\ val sk2{1} = r2{2} /\ val ske{1} = r3{2}).
     rnd (EH.val) (EH.insubd).
     rnd (EH.val) (EH.insubd).
     auto => /> *;do split; 1: by smt(EH.valP EH.insubdK supp_dmap).
     move => *; do split.
     + move => x;rewrite /SDD.d1 supp_dmap => H.
       by elim H => xx [H0 H1];apply in_dmap1E_can;
          smt(supp_dmap EH.valK).
     + move => *; do split; 1: by smt(EH.valP EH.insubdK supp_dmap).
       by move => *; do split; smt(EH.valK supp_dmap).
     wp;   call(:true).
     wp;rnd;rnd;wp;call(:true).
     wp;   call(:true).
     by auto => />.

  have -> : Pr [ CCA(RO,XWING1(KEMS),A).main() @ &m : res ] =
       Pr [ SD.Game(SDAdv(KEMS,RO,A),SD.Os).main(SDD.d2) @ &m : res ].
  + byequiv => //.
    proc.
    inline {2} 2;wp; conseq (: ={b',b});1: smt().
     call(: ={glob RO, glob KEMS, CCA.cstar}
          /\ XWING1._sk1{1} =  XWING_EG._sk1{2}
          /\ XWING1._pk2{1} = XWING_EG._pk2{2}
          /\ asint (val XWING1._sk2{1}) = XWING_EG._sk2{2}).
     + proc;inline *.
       seq 1 1 : (#pre /\ ={k}); 1: by auto.
       if; 1,3: by auto.
       wp;   call(:true).
       wp;   call(:true).
       by auto => />.
     + by conseq />;sim.
     inline *.
     wp;   call(:true).
     swap {1} 4 -3; swap {1} 13 -11.
     swap {2} 3 -1; swap {2} 4 -1;swap {2} 9 -5; swap {2} 21 - 16.
     seq 2 5: (#pre /\ asint (val XWING1._sk2{1}) = r2{2} /\ asint (val XWING1._rv2{1}) = r3{2}).
     rnd (asint \o EU.val) (EU.insubd \o inzmod).
     rnd (asint \o EU.val) (EU.insubd \o inzmod).
     auto => /> *;do split;
        1: by smt(supp_dmap asintK EU.valK).
      move => *; do split.
     + move => x;rewrite /SDD.d2 supp_dmap => H.
       elim H => xx [H0 H1].
       by have  -> := in_dmap1E_can dU (asint \o EU.val)
                      ((\o) EU.insubd inzmod) x; smt(supp_dmap asintK EU.valK).
     by move => *; do split; smt(supp_dmap asintK EU.valK).
     wp;   call(:true).
     wp;rnd;rnd;wp;call(:true).
     wp;   call(:true).
     by auto => />.

  apply (SDD.sdist_oracleN (SDAdv(KEMS,RO,A))).
  + move => O Oll;proc; islossless.
    + apply (All RO (CCAOO(RO, XWING_EG(KEMS, O)))).
      + by apply RO_getll.
      by islossless; [ apply RO_getll | apply KEMS_decll].
    + by apply RO_getll.
    + by apply KEMS_encll.
    + by apply KEMS_kgll.
    + by apply RO_initll.

  + move => O.
    proc;inline *.
    wp; call(: SD.Count.n <= 2); 1: by proc;conseq />;auto.
    + by conseq />.
    wp; call(: SD.Count.n <= 2).
    wp; call(: SD.Count.n <= 2).
    wp; call(: SD.Count.n <= 1).
    wp; rnd;rnd;wp;call(: SD.Count.n <= 1).
    wp; call(: SD.Count.n = 0).
    wp; call(: SD.Count.n = 0).
    by auto => /#.
  qed.

end section.


module ROBad(RO : Oracle) : Oracle = {

   var bad1 : bool
   var sol : G option

   include RO [-get]

   proc get(x : in_t) : shkey = {
     var rv;
     if (x.`3 = XWING1._pk2^XWING1._rv2) {
        sol <- Some x.`3;
        bad1 <- true;
        rv <@ RO.get(x);
     }
     else {
        rv <@ RO.get(x);
     }
     return rv;
   }
}.

module ROBadSilence(RO : Oracle) : Oracle = {

   include RO [-get]

   proc get(x : in_t) : shkey = {
     var rv;
     if (x.`3 = XWING1._pk2^XWING1._rv2) {
        ROBad.sol <- Some x.`3;
        ROBad.bad1 <- true;
        rv <- witness;
     }
     else {
        rv <@ RO.get(x);
     }
     return rv;
   }
}.


module CCABad(H : Oracle, S : Scheme, A : CCA_ADV) = {
  (* Note that CCA dec oracle does not depend on A
     so we can get it as below, and that it still
     uses H! *)
  module A = A(ROBad(H), CCA(H, S, A).O)

  proc main() : bool = {
    var pk : pkey;
    var k1 : shkey;
    var ck0 : ciphertext * shkey;
    var b : bool;
    var b' : bool;

    ROBad.bad1 <- false;
    ROBad.sol <- None;
    H.init();
    CCA.cstar <- None;
    (pk, CCA.sk) <@ S(H).kg();
    k1 <$ dshkey;
    b <$ {0,1};
    ck0 <@ S(H).enc(pk);
    CCA.cstar <- Some ck0.`1;
    b' <@ A.guess(pk, ck0.`1, if b then k1 else ck0.`2);

    return b' = b;
  }
}.

module CCABadSilence(H : Oracle, S : Scheme, A : CCA_ADV) = {
  (* Note that CCA dec oracle does not depend on A
     so we can get it as below, and that it still
     uses H! *)
  module A = A(ROBadSilence(H), CCA(H, S, A).O)

  proc main() : bool = {
    var pk : pkey;
    var k1 : shkey;
    var ck0 : ciphertext * shkey;
    var b : bool;
    var b' : bool;

    ROBad.bad1 <- false;
    ROBad.sol <- None;
    H.init();
    CCA.cstar <- None;
    (pk, CCA.sk) <@ S(H).kg();
    k1 <$ dshkey;
    b <$ {0,1};
    ck0 <@ S(H).enc(pk);
    CCA.cstar <- Some ck0.`1;
    b' <@ A.guess(pk, ck0.`1, if b then k1 else ck0.`2);

    return b' = b;
  }
}.

module ROBadSilenceB(DHO : SDHO_P) : Oracle = {

   include RO [-get]

   var holes : ((G * KEM.key) * shkey) list

   proc hole(x4 : G, k1 : KEM.key) : shkey = {
     var rv;
     if (assoc holes (x4,k1) = None) {
        rv <$ dshkey;
        holes <- ((x4,k1),rv) :: holes;
     }
     else {
        rv <- (oget (assoc holes (x4,k1)));
     }
     return rv;
   }

   proc get(x : in_t) : shkey = {
     var rv, chk;
     chk <@ DHO.dh(XWING1._c2,x.`3);
     if (chk) {
        ROBad.sol <- Some x.`3;
        ROBad.bad1 <- true;
        rv <- witness;
     }
     else {
        chk <@ DHO.dh(x.`4,x.`3);
        if (x.`1 = label && x.`5 = XWING1._pk2 && chk) {
           rv <@ hole(x.`4,x.`2);
        }
        else {
           rv <@ RO.get(x);
        }
     }
     return rv;
   }
}.

module XWING1B(KEMS : KEM.Scheme, DHO : SDHO_P, Ignore : POracle) = {
  proc kg() : pkey * skey = {
    var pk1,pk;
    (pk1,XWING1._sk1) <@ KEMS.kg();
    pk <- (pk1,XWING1._pk2);
    return(pk,witness);
  }

  proc enc(pk : pkey) : ciphertext * shkey = {
    var pk1,pk2,c1,k,c;
    (pk1,pk2) <- pk;
    (c1,XWING1._kb1) <@ KEMS.enc(pk1);
    c <- (c1,XWING1._c2);
    k <$ dshkey;
    ROBadSilenceB.holes <- ((XWING1._c2,XWING1._kb1),k) :: [];
    return (c,k);
  }

  proc dec(sk : skey, c : ciphertext) : shkey option  = {
    var c1,c2,k1,k;
    (c1,c2) <- c;
    k1 <@ KEMS.dec(XWING1._sk1,c1);
    (* Implicitly adding (label, oget k1, dh(c2,sk2), c2, pk2) *)
    k <@ ROBadSilenceB(DHO).hole(c2,oget k1);
    return if k1 = None then None else Some k;
  }
}.


module (SDHB(S : KEM.Scheme, A : CCA_ADV) : SDHAdv) (O : SDHO_P)  = {
  module A = A(ROBadSilenceB(O), CCA(RO, XWING1B(S,O), A).O)

  proc find(X : G, Y : G) : G = {
    var pk : pkey;
    var k1 : shkey;
    var ck0 : ciphertext * shkey;
    var b : bool;
    var b' : bool;

    ROBad.bad1 <- false;
    ROBad.sol <- None;
    RO.init();
    CCA.cstar <- None;
    XWING1._pk2 <- X;
    XWING1._c2 <- Y;
    (pk, CCA.sk) <@ XWING1B(S,O,RO).kg();
    k1 <$ dshkey;
    b <$ {0,1};
    ck0 <@ XWING1B(S,O,RO).enc(pk);
    CCA.cstar <- Some ck0.`1;
    b' <@ A.guess(pk, ck0.`1, if b then k1 else ck0.`2);

    return (oget ROBad.sol);
  }
}.

section.

  declare module A <: CCA_ADV {-RO, -XWING1, -CCA, -ROBad, -ROBadSilenceB, -SDHO}.
  declare module KEMS <: KEM.Scheme {-A, -RO, -XWING1, -CCA, -ROBad, -ROBadSilenceB, -SDHO}.

  declare axiom KEMS_kgll : islossless KEMS.kg.
  declare axiom KEMS_encll : islossless KEMS.enc.
  declare axiom KEMS_decll : islossless KEMS.dec.
  declare axiom All (O <: POracle) (CCAO <: CCA_ORC):
      islossless O.get => islossless CCAO.dec =>  islossless A(O,CCAO).guess.

  lemma uptobad1 &m :
    Pr [ CCA(RO,XWING1(KEMS),A).main() @ &m : res ] =
    Pr [ CCABad(RO,XWING1(KEMS),A).main() @ &m : res ].
  proof.
  byequiv => //;proc; inline *.
  wp;call(: ={glob RO, glob XWING1, glob CCA, glob KEMS}).
  + proc;sp;if;1,3: by auto.
    by inline *;conseq />; sim.

  proc*;inline *.
  case (x{2}.`3 = XWING1._pk2{2} ^ XWING1._rv2{2}).
  + rcondt{2} 2; 1: by move => *;auto.
    by auto => />.
  + rcondf{2} 2; 1: by move => *;auto.
    by auto => />.

  auto;call(: true).
  auto;call(:true).
  by auto => />.
  qed.

  lemma uptobad2 &m :
    `| Pr [ CCABad(RO,XWING1(KEMS),A).main() @ &m : res ] -
       Pr [ CCABadSilence(RO,XWING1(KEMS),A).main() @ &m : res ] | <=
        RealOrder.maxr Pr [ CCABad(RO,XWING1(KEMS),A).main() @ &m : ROBad.bad1 ]
                  Pr [ CCABadSilence(RO,XWING1(KEMS),A).main() @ &m : ROBad.bad1 ] by byupto.

  lemma uptobad3 &m :
    Pr [ CCABad(RO,XWING1(KEMS),A).main() @ &m : ROBad.bad1 ] =
    Pr [ CCABadSilence(RO,XWING1(KEMS),A).main() @ &m : ROBad.bad1 ].
  proof.
  byequiv => //.
  proc.
  wp;call(: ROBad.bad1, ={glob XWING1, ROBad.bad1, glob RO, glob KEMS,  glob RO, glob CCA},={ROBad.bad1}).
  + by move => H O Oll Hll; apply (All H O Hll Oll).
  + by proc; conseq />; sim.
  + move => *;proc;inline*;sp;if.
    + auto;call(:true); 1: by apply KEMS_decll.
      by auto;smt(dshkey_ll).
    by auto.
  + move => *;proc;inline*;sp;if.
    + auto;call(:true); 1: by apply KEMS_decll.
      by auto;smt(dshkey_ll).
    by auto.
  + by proc;inline *;if;auto.
  + by move => *;proc;inline*;sp;if;auto;smt(dshkey_ll).
  + by move => *;proc;inline*;sp;if;auto;smt(dshkey_ll).

  inline *;auto;call(: ={glob RO}).
  auto;call(: ={glob RO}).
  by auto => /#.
  qed.

  op in_hole(sk2 : euT, pk2 : G, x : in_t) = x.`1 = label && x.`3 = x.`4 ^ sk2 /\ x.`5 = pk2.

  lemma uptobad4 &m :
    Pr [ CCABadSilence(XWING_DEFS.RO.RO,XWING1(KEMS),A).main() @ &m : ROBad.bad1 ] <=
       Pr [ SDH(SDHB(KEMS,A)).main() @ &m : res].
  proof.
    byequiv => //.
    proc;inline *.
    swap{1} 6 -5; swap {1} 15 -13.
    wp.
    call(: ={glob KEMS, CCA.cstar,XWING1._pk2,XWING1._c2, XWING1._sk1}
           /\ eq_except (in_hole SDHO.x{2} XWING1._pk2{2}) XWING_DEFS.RO.RO.m{1} XWING_DEFS.RO.RO.m{2}
           /\ (forall x, x \in RO.m{1} => in_hole SDHO.x{2} XWING1._pk2{2} x => assoc ROBadSilenceB.holes{2} (x.`4,x.`2) <> None)
           /\ (forall xx, assoc ROBadSilenceB.holes{2} xx <> None => let xx1 = (label,xx.`2,xx.`1 ^ SDHO.x{2},xx.`1,XWING1._pk2{2}) in xx1 \in XWING_DEFS.RO.RO.m{1}  /\ assoc ROBadSilenceB.holes{2} xx = XWING_DEFS.RO.RO.m{1}.[xx1])
           /\ XWING1._sk2{1}= SDHO.x{2} /\ XWING1._pk2{2}= g ^ SDHO.x{2} /\ XWING1._rv2{1} = SDHO.y{2} /\ XWING1._c2{1} = g^SDHO.y{2}
           /\ (ROBad.bad1{1} => g ^ SDHO.y{2} ^ SDHO.x{2} = oget ROBad.sol{2})); last first.

    + auto;call(:true);auto;call(:true);auto => /> sk2L _ rv2L _ k1L _ bL _ R0 rL _;do split;
        by smt(mem_set mem_empty assoc_none assoc_head get_setE NG.ng_commute).

    + proc;inline *.
      sp;if; 1,3: by auto.
      seq 4 4 : (#pre /\ ={c0,c1,c2,k1});1: by conseq />;sim.
      sp;if{2};auto => /> &1 &2 ? H ???rL*;do split;
        by smt(mem_set mem_empty assoc_none assoc_head get_setE NG.ng_commute assoc_cons).

    + proc;inline *.
      sp;if;1,2: by auto => />; smt(NG.ng_commute).
      sp;if{2};last by auto => /> *;do split;
        by smt(mem_set mem_empty assoc_none assoc_head get_setE NG.ng_commute assoc_cons).

      by sp;if{2}; auto => /> *;do split;
        smt(mem_set mem_empty assoc_none assoc_head get_setE NG.ng_commute assoc_cons).

    qed.

    lemma hop2 &m :
      `| Pr [ CCA(RO,XWING1(KEMS),A).main() @ &m : res ] -
          Pr [ CCABadSilence(XWING_DEFS.RO.RO,XWING1(KEMS),A).main() @ &m : res ] | <=
         Pr [ SDH(SDHB(KEMS,A)).main() @ &m : res].
    proof.
    rewrite uptobad1.
    have := uptobad2 &m.
    rewrite uptobad3.
    have := uptobad4 &m.
    by smt().
    qed.

end section.

(* NOW WE NEED TO GUARANTEE THAT H IS NEVER CALLED TO REVEAL k2 VIA DECAPS.
  THIS IS KEM CCR *)

module CCACCRBad(H : Oracle, KEMS : KEM.Scheme, A : CCA_ADV) = {
  var bad2 : bool
  var cc : KEM.ciphertext option

  module O = {
    proc dec(c : ciphertext) : shkey option = {
      var k : shkey option;
      var kaux : KEM.key option;

      k <- None;
      if (Some c <> CCA.cstar) {
        kaux <@ KEMS.dec(XWING1._sk1,c.`1);
        if (c.`1 <> (oget CCA.cstar).`1 /\ kaux = Some XWING1._kb1) {
           cc <- Some c.`1;
           bad2 <- true;
           k <@ XWING1(KEMS,H).dec(CCA.sk, c);
        }
        else {
           k <@ XWING1(KEMS,H).dec(CCA.sk, c);
        }
      }

      return k;
    }
  }

  module A = A(ROBadSilence(H), O)

  proc main() : bool = {
    var pk : pkey;
    var k1 : shkey;
    var ck0 : ciphertext * shkey;
    var b : bool;
    var b' : bool;

    bad2 <- false;
    cc <- None;
    ROBad.bad1 <- false;
    ROBad.sol <- None;
    H.init();
    CCA.cstar <- None;
    (pk, CCA.sk) <@ XWING1(KEMS,H).kg();
    k1 <$ dshkey;
    b <$ {0,1};
    ck0 <@ XWING1(KEMS,H).enc(pk);
    CCA.cstar <- Some ck0.`1;
    b' <@ A.guess(pk, ck0.`1, if b then k1 else ck0.`2);

    return b' = b;
  }
}.

module CCACCRBadSilence(H : Oracle, KEMS : KEM.Scheme, A : CCA_ADV) = {
  module O = {
    proc dec(c : ciphertext) : shkey option = {
      var k : shkey option;
      var kaux : KEM.key option;

      k <- None;
      if (Some c <> CCA.cstar) {
        kaux <@ KEMS.dec(XWING1._sk1,c.`1);
        if (c.`1 <> (oget CCA.cstar).`1 /\ kaux = Some XWING1._kb1) {
           CCACCRBad.cc <- Some c.`1;
           CCACCRBad.bad2 <- true;
           k <-witness;
        }
        else {
           k <@ XWING1(KEMS,H).dec(CCA.sk, c);
        }
      }

      return k;
    }
  }

  module A = A(ROBadSilence(H), O)

  proc main() : bool = {
    var pk : pkey;
    var k1 : shkey;
    var ck0 : ciphertext * shkey;
    var b : bool;
    var b' : bool;

    CCACCRBad.bad2 <- false;
    CCACCRBad.cc <- None;
    ROBad.bad1 <- false;
    ROBad.sol <- None;
    H.init();
    CCA.cstar <- None;
    (pk, CCA.sk) <@ XWING1(KEMS,H).kg();
    k1 <$ dshkey;
    b <$ {0,1};
    ck0 <@ XWING1(KEMS,H).enc(pk);
    CCA.cstar <- Some ck0.`1;
    b' <@ A.guess(pk, ck0.`1, if b then k1 else ck0.`2);

    return b' = b;
  }
}.

module XWING1CCR(KEMS : KEM.Scheme, O : POracle) = {
  include XWING1(KEMS,O) [-kg,enc]
  var _pk1 : KEM.pkey
  var _c1 : KEM.ciphertext

  proc kg() : pkey * skey = {
    var pk;
    XWING1._sk2 <$ dU;
    XWING1._pk2 <- g^XWING1._sk2;
    pk <- (_pk1,XWING1._pk2);
    return(pk,witness);
  }
  proc enc(pk : pkey) : ciphertext * shkey = {
    var pk1,pk2,k2,k,c;
    (pk1,pk2) <- pk;
    XWING1._rv2 <$ dU;
    XWING1._c2 <- g^XWING1._rv2;
    k2 <- XWING1._pk2^XWING1._rv2;
    k <@ O.get(label,XWING1._kb1,k2,XWING1._c2,XWING1._pk2);
    c <- (_c1,XWING1._c2);
    return (c,k);
  }

}.

module CCRB(H : Oracle, KEMS : KEM.Scheme, A : CCA_ADV) = {

  module A = A(ROBadSilence(H), CCACCRBadSilence(H, KEMS, A).O)

  proc find(pk1 : KEM.pkey, sk1 : KEM.skey, c1 : KEM.ciphertext, kb1 : KEM.key) : KEM.ciphertext = {
    var pk : pkey;
    var ck0 : ciphertext * shkey;
    var k1 : shkey;
    var b : bool;
    var b' : bool;

    CCACCRBad.bad2 <- false;
    CCACCRBad.cc <- None;
    ROBad.bad1 <- false;
    ROBad.sol <- None;
    H.init();
    CCA.cstar <- None;
    XWING1CCR._pk1 <- pk1;
    XWING1._sk1 <- sk1;
    (pk, CCA.sk) <@ XWING1CCR(KEMS,H).kg();
    k1 <$ dshkey;
    b <$ {0,1};
    XWING1CCR._c1 <- c1;
    XWING1._kb1 <- kb1;
    ck0 <@ XWING1CCR(KEMS,H).enc(pk);
    CCA.cstar <- Some ck0.`1;
    b' <@ A.guess(pk, ck0.`1, if b then k1 else ck0.`2);

    return (oget CCACCRBad.cc);
  }
}.

op kemdec(sk : KEM.skey, c : KEM.ciphertext) : KEM.key option.

section.

  declare module A <: CCA_ADV {-RO, -XWING1,-XWING1CCR, -CCA, -CCACCRBad, -ROBadSilence, -CCACCRBadSilence}.
  declare module KEMS <: KEM.Scheme {-A, -RO, -XWING1, -XWING1CCR, -CCA, -CCACCRBad, -ROBadSilence, -CCACCRBadSilence}.

  declare axiom KEMS_kgll : islossless KEMS.kg.
  declare axiom KEMS_encll : islossless KEMS.enc.
  declare axiom KEMS_decdet st sk c : phoare [ KEMS.dec : glob KEMS = st /\ arg = (sk,c) ==> glob KEMS = st /\ res = kemdec sk c] = 1%r.
  declare axiom All (O <: POracle) (CCAO <: CCA_ORC):
      islossless O.get => islossless CCAO.dec =>  islossless A(O,CCAO).guess.

  lemma uptobadccr1 &m :
    Pr [ CCABadSilence(XWING_DEFS.RO.RO,XWING1(KEMS),A).main() @ &m : res ] =
    Pr [ CCACCRBad(RO,KEMS,A).main() @ &m : res ].
  proof.
  byequiv => //;proc; inline *.
  wp;call(: ={glob RO, glob XWING1, glob CCA, glob KEMS}).
  + proc;sp;if;1,3: by auto.
    seq 0 1 : #pre.
    + by  wp; ecall {2} (KEMS_decdet (glob KEMS){2} XWING1._sk1{2} c{2}.`1); auto => />.
    by if{2};inline *; wp;rnd;wp;call(: ={glob RO});auto.

  by proc*;inline *;sim.
  auto;call(: true).
  auto;call(:true).
  by auto => />.
  qed.

  lemma uptobadccr2 &m :
    `| Pr [ CCACCRBad(RO,KEMS,A).main() @ &m : res ] -
       Pr [ CCACCRBadSilence(RO,KEMS,A).main() @ &m : res ] | <=
        RealOrder.maxr Pr [ CCACCRBad(RO,KEMS,A).main() @ &m : CCACCRBad.bad2 ]
                  Pr [ CCACCRBadSilence(RO,KEMS,A).main() @ &m : CCACCRBad.bad2 ] by byupto.

  lemma uptobadccr3 &m :
    Pr [ CCACCRBad(RO,KEMS,A).main() @ &m : CCACCRBad.bad2 ] =
                  Pr [ CCACCRBadSilence(RO,KEMS,A).main() @ &m : CCACCRBad.bad2 ].
  proof.
  byequiv => //.
  proc.
  wp;call(: CCACCRBad.bad2, ={glob XWING1, ROBad.bad1, glob RO, glob KEMS,  glob RO, glob CCA, CCACCRBad.bad2},={CCACCRBad.bad2}).
  + by move => H O Oll Hll; apply (All H O Hll Oll).
  + proc;sp;if;1,3: by auto.
    seq 1 1 : (#pre /\ ={kaux}); 1: by conseq />; sim.
    if; [by auto | | by inline *;auto;call(: ={glob RO}); auto => />].
    inline *;auto;call {1} (:true ==> true).
    + by proc*; exists* (glob KEMS), sk, c; elim* => st _sk _c; call(KEMS_decdet st _sk _c).
    by auto => />.

  + move => *;proc;inline*;sp;if.
    seq 1  : #pre; 1: trivial.
    + by conseq />; exists* (glob KEMS), XWING1._sk1, c; elim* => st _sk1 _c; call(KEMS_decdet st _sk1 _c.`1).
    + by if;sp;auto; exists* (glob KEMS), XWING1._sk1, c; elim* => st _sk1 _c *; call(KEMS_decdet st _sk1 _c.`1); auto => />; smt(dshkey_ll).
    + by hoare; conseq />; trivial.
    + by smt().
    by trivial.

  + move => *;proc;inline*;sp;if.
    seq 1  : #pre; 1: trivial.
    + by conseq />; exists* (glob KEMS), XWING1._sk1, c; elim* => st _sk1 _c; call(KEMS_decdet st _sk1 _c.`1).
    + if;2: by sp;auto; exists* (glob KEMS), XWING1._sk1, c; elim* => st _sk1 _c *; call(KEMS_decdet st _sk1 _c.`1); auto => />; smt(dshkey_ll).
      by auto => />.
    + by hoare; conseq />; trivial.
    + by smt().
    by trivial.

  + by proc;inline *;if;auto.
  + by move => *;proc;inline*;sp;if;auto;smt(dshkey_ll).
  + by move => *;proc;inline*;sp;if;auto;smt(dshkey_ll).

  inline *;auto;call(: ={glob RO}).
  auto;call(: ={glob RO}).
  by auto => /> /#.
  qed.

  lemma uptobadccr4 &m :
   Pr [ CCACCRBadSilence(RO,KEMS,A).main() @ &m : CCACCRBad.bad2 ] <=
       Pr [ KEM.CCR(KEMS,CCRB(RO,KEMS,A)).main() @ &m : res].
  proof.
  byequiv => //.
  proc;inline *.
  swap{1} 7 -6; swap {2} [5..6] 14; swap{2} 2 16.
  ecall {2} (KEMS_decdet (glob KEMS){2} sk{2} c1{2}).
  wp; conseq />;1:by smt().
  call(: ={glob KEMS, glob CCA, glob XWING1, glob RO, CCACCRBad.bad2, CCACCRBad.cc}
         /\ (CCACCRBad.bad2{1} => oget CCACCRBad.cc{2} <> (oget CCA.cstar{2}).`1 /\
               kemdec XWING1._sk1{2} (oget CCACCRBad.cc{2}) = Some XWING1._kb1{2})); last by auto;call(:true);auto;call(:true);auto => />  /#.

  + proc;inline *.
    sp;if; 1,3: by auto.
    seq 1 1 : (#pre /\ ={kaux} /\ kaux{1} = kemdec XWING1._sk1{1} c{1}.`1).
    + ecall {1} (KEMS_decdet (glob KEMS){1} XWING1._sk1{1} c{1}.`1).
      ecall {2} (KEMS_decdet (glob KEMS){2} XWING1._sk1{2} c{2}.`1).
      by auto.
    if;1,2: by auto.
    by auto;call(:true);auto.

  by proc;inline *; conseq />; sim.

  qed.

  lemma hop3 &m :
    `| Pr [ CCABadSilence(XWING_DEFS.RO.RO,XWING1(KEMS),A).main() @ &m : res ] -
       Pr [ CCACCRBadSilence(RO,KEMS,A).main() @ &m : res ] | <=
       Pr [ KEM.CCR(KEMS,CCRB(RO,KEMS,A)).main() @ &m : res].
  proof.
    rewrite uptobadccr1.
    have := uptobadccr2 &m.
    rewrite uptobadccr3.
    have := uptobadccr4 &m.
    by smt().
  qed.

end section.

(* THEN, BECAUSE WE KNOW H IS NEVER CALLED ON THIS POINT, WE CAN
   MOVE TO A GAME WHERE WE JUST GIVE A RANDOM KEY TO ATTACKER AND
   PROVE THAT, INDEPENDENTLY OF b, IT WILL GIVE THE SAME OUTPUT *)

module NoAdv(H : Oracle, KEMS : KEM.Scheme, A : CCA_ADV) = {
  module A = A(ROBadSilence(H), CCACCRBadSilence(H,KEMS,A).O)

  proc main() : bool = {
    var pk : pkey;
    var kb : shkey;
    var ck0 : ciphertext * shkey;
    var b : bool;
    var b' : bool;

    CCACCRBad.bad2 <- false;
    CCACCRBad.cc <- None;
    ROBad.bad1 <- false;
    ROBad.sol <- None;
    H.init();
    CCA.cstar <- None;
    (pk, CCA.sk) <@ XWING1(KEMS,H).kg();
    kb <$ dshkey;
    b <$ {0,1};
    ck0 <@ XWING1(KEMS,H).enc(pk);
    CCA.cstar <- Some ck0.`1;
    b' <@ A.guess(pk, ck0.`1, kb);

    return b' = b;
  }
}.

section.

  declare module A <: CCA_ADV {-RO, -XWING1, -XWING1CCR, -CCA, -CCACCRBad}.
  declare module KEMS <: KEM.Scheme {-RO, -XWING1, -XWING1CCR, -CCA,-A, -CCACCRBad}.

  declare axiom KEMS_kgll : islossless KEMS.kg.
  declare axiom KEMS_encll : islossless KEMS.enc.
  declare axiom KEMS_decdet st sk c : phoare [ KEMS.dec : glob KEMS = st /\ arg = (sk,c) ==> glob KEMS = st /\ res = kemdec sk c] = 1%r.
  declare axiom All (O <: POracle) (CCAO <: CCA_ORC):
      islossless O.get => islossless CCAO.dec =>  islossless A(O,CCAO).guess.

  lemma hop4 &m :
       Pr [ CCACCRBadSilence(RO,KEMS,A).main() @ &m : res ] =
       Pr [ NoAdv(RO,KEMS,A).main() @ &m : res ].
  byequiv => //.
  proc.
  swap {1} 9 -8; swap {2} 9 -8.
  seq 1 1 : (#pre /\ ={b});1: by auto.
  case(b{1}).
  (* simple case: both keys are random anyway. *)
  + call(: ={glob RO, glob XWING1, glob KEMS, glob CCA}); last first.
    + inline *;auto;call(:true);auto;call(:true);auto => />.
    + by proc;conseq />;sim.
    by proc;conseq />;sim.

  + call(: ={glob XWING1, glob KEMS, glob CCA} /\
      eq_except (pred1 (label, XWING1._kb1, XWING1._pk2 ^ XWING1._rv2 , XWING1._c2, XWING1._pk2)){1} RO.m{1} RO.m{2} /\
      fdom RO.m{1} = fdom RO.m{2} /\
      (label, XWING1._kb1{1}, XWING1._pk2{1} ^ XWING1._rv2{1}, XWING1._c2{1}, XWING1._pk2{1}) \in RO.m{1} /\
     CCA.cstar{2} <> None /\ XWING1._c2{2} = (oget CCA.cstar{2}).`2); last first.
    + inline {1} 9; inline {2} 9.
      by inline *;wp;rnd{2}; swap {2} 12 7;auto;call(:true);auto;rnd{1};auto; call(:true);auto => />;
          by smt(fdom_set mem_set mem_empty assoc_none assoc_head get_setE NG.ng_commute).

    + proc;conseq />.
      sp;if;1,3: by auto.
      seq 1 1 : (#pre /\ ={kaux} /\ kaux{1} = kemdec XWING1._sk1{1} c{1}.`1).
      + ecall {1} (KEMS_decdet (glob KEMS){1} XWING1._sk1{1} c{1}.`1).
        ecall {2} (KEMS_decdet (glob KEMS){2} XWING1._sk1{2} c{2}.`1).
        by auto.
      if; 1,2: by auto.
      inline *;auto.
      ecall {1} (KEMS_decdet (glob KEMS){1} XWING1._sk1{1} c1{1}).
      ecall {2} (KEMS_decdet (glob KEMS){2} XWING1._sk1{2} c1{2}).
      auto => /> &1 &2 *;do split.
      + move => *;do split.
     by smt(fdom_set mem_set mem_empty assoc_none assoc_head get_setE NG.ng_commute).
      + move => *;do split.
        rewrite get_setE /=.
     by smt(fdom_set mem_set mem_empty assoc_none assoc_head get_setE NG.ng_commute).
     by smt(fdom_set mem_set mem_empty assoc_none assoc_head get_setE NG.ng_commute).
      smt(@SmtMap).

     + move => *;do split.
        rewrite get_setE /=.
     by smt(fdom_set mem_set mem_empty assoc_none assoc_head get_setE NG.ng_commute).
  by smt(@SmtMap).

  proc;inline *;if;1,2:by auto.
  by auto => />;
     by smt(fdom_set mem_set mem_empty assoc_none assoc_head get_setE NG.ng_commute).

qed.


end section.

(* FINALLY, THE ADV PROB OF SUCCESS IS EXACTLY 1/2 *)

section.

  declare module A <: CCA_ADV {-CCACCRBad, -RO}.
  declare module KEMS <: KEM.Scheme  {-CCACCRBad, -RO, -A}.

  declare axiom KEMS_kgll : islossless KEMS.kg.
  declare axiom KEMS_encll : islossless KEMS.enc.
  declare axiom KEMS_decll : islossless KEMS.dec.
  declare axiom All (O <: POracle) (CCAO <: CCA_ORC):
      islossless O.get => islossless CCAO.dec =>  islossless A(O,CCAO).guess.

  lemma noadv &m :
       Pr [ NoAdv(RO,KEMS,A).main() @ &m : res ] = 1%r/2%r.
  byphoare => //.
  proc.
  swap 9 3.
  seq 11  : true (1%r) (1%r/2%r) (0%r)(0%r).
  + call(: true); 1,2: by trivial.
    by wp;call(: true); trivial.
  + inline *;wp; call(:true).
    + by move => H O Oll Hll; apply (All H O Hll Oll ).
    + islossless;1,2:by apply KEMS_decll.
      by islossless.
    auto; call(:true);1: by apply KEMS_encll.
    auto; call(:true);1: by apply KEMS_kgll.
    by auto => />; smt(dshkey_ll dU_ll).

  + rnd (pred1 b').
    by auto => />;smt(DBool.dbool1E).

  + hoare.
    call(: true); 1,2: by trivial.
    by wp;call(: true); trivial.

  by smt().
  qed.

end section.

(* Putting it all together *)

section.

  declare module A <: CCA_ADV {-CCA, -XWING1, -SD.Count, -SD.B1, -SD.Os, -XWING_EG, -CCACCRBad, -RO,  -XWING1CCR, -SDHO, -ROBad, -ROBadSilenceB}.
  declare module KEMS <: KEM.Scheme  {-CCA, -XWING1, -SD.Count, -SD.B1, -SD.Os, -XWING_EG, -CCACCRBad, -RO, -A,  -XWING1CCR, -SDHO, -ROBad, -ROBadSilenceB}.

  declare axiom KEMS_kgll : islossless KEMS.kg.
  declare axiom KEMS_encll : islossless KEMS.enc.
  declare axiom KEMS_decll : islossless KEMS.dec.
  declare axiom KEMS_decdet st sk c : phoare [ KEMS.dec : glob KEMS = st /\ arg = (sk,c) ==> glob KEMS = st /\ res = kemdec sk c] = 1%r.
  declare axiom All (O <: POracle) (CCAO <: CCA_ORC):
      islossless O.get => islossless CCAO.dec =>  islossless A(O,CCAO).guess.

  lemma main_theorem &m :
    `| Pr [ CCA(RO,XWING(KEMS),A).main() @ &m : res ] - 1%r/2%r | <=
          2%r * sdist_dU_dH
        + Pr [ SDH(SDHB(KEMS,A)).main() @ &m : res]
        + Pr [ KEM.CCR(KEMS,CCRB(RO,KEMS,A)).main() @ &m : res].
  proof.
  have := (hop1 A KEMS RO _ _ KEMS_kgll KEMS_encll KEMS_decll All &m).
  + by islossless.
  + by islossless.

  have :=  (hop2 A KEMS KEMS_kgll KEMS_encll KEMS_decll All &m).
  have :=  (hop3 A KEMS KEMS_kgll KEMS_encll KEMS_decdet All &m).
  have :=  (hop4 A KEMS KEMS_kgll KEMS_encll KEMS_decdet All &m).

  rewrite -(noadv A KEMS KEMS_kgll KEMS_encll KEMS_decll All &m).

  by smt().
  qed.

end section.
