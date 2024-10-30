require import AllCore KEM_ROM PROM Distr StdOrder SmtMap List.
require (****) NomGroup PRF.

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

clone import KEM as XWING_DEFS with
   type key <- shkey,
   type pkey <- pkey,
   type skey <- skey,
   type ciphertext <- ciphertext,
   op dkey <- dshkey
   proof dkey_ll by apply dshkey_ll
   proof dkey_fu by apply dshkey_fu
   proof dkey_uni by apply dshkey_uni
   proof *.

clone import PRF as KDF with
  type D <- label * G * G * G,
  type R <- shkey
  proof *.

clone import RF as IdealKDF with
  op dR <- (fun _ => dshkey)
  proof dR_ll by smt(dshkey_ll)
  proof *.

clone import PseudoRF as RealKDF with
  type K <- KEM.key,
  op dK <- KEM.dkey
  proof dK_ll by smt(KEM.dkey_ll)
  proof *.

module XWING(KEMS : KEM.Scheme)  = {
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
    k <- F k1 (label,k2,c2,pk2);
    c <- (c1,c2);
    return (c,k);
  }
  
  proc dec(sk : skey, c : ciphertext) : shkey option  = {
    var sk1,sk2,pk2,c1,c2,k1,k2,k;
    (sk1,sk2,pk2) <- sk;
    (c1,c2) <- c;
    k1 <@ KEMS.dec(sk1,c1);
    k2 <- exp c2 (val sk2);
    k <- F (oget k1) (label,k2,c2,pk2);
    return if k1 = None then None else Some k;
  }
}.

module XWING1(KEMS : KEM.Scheme, O : PRF) = {
  var _sk1 : KEM.skey (* fixed in key generation *)
  var _sk2 : ehT      (* fixed in key generation *)
  var _pk2 : G        (* fixed in key generation *)
  var _rv2 : ehT      (* fixed in enc *)
  var _c1  : KEM.ciphertext  (* fixed in enc *)
  var _c2  : G        (* fixed in enc *)
  var _kb1 : KEM.key        (* fixed in enc *)
  var bad : bool

  proc kg() : pkey * skey = {
    var pk1,pk;
    (pk1,_sk1) <@ KEMS.kg();
    _sk2 <$ dH;
    _pk2 <- exp g (val _sk2);
    pk <- (pk1,_pk2);
    return(pk,(_sk1,_sk2,_pk2));
  } 
  
  proc enc(pk : pkey) : ciphertext * shkey = {
    var pk1,pk2,k2,k,c;
    (pk1,pk2) <- pk;
    (_c1,_kb1) <@ KEMS.enc(pk1);
    _rv2 <$ dH;
    _c2 <- exp g (val _rv2);
    k2 <- exp _pk2 (val _rv2);
    RF.m <- empty; (* This will be removed for the PRF hop, of course *)
    PRF.k <- _kb1; (* This will be removed for the PRF hop, of course *)
    k <@ O.f(label,k2,_c2,_pk2);
    c <- (_c1,_c2);
    return (c,k);
  }

  proc dec(sk : skey, c : ciphertext) : shkey option  = {
    var c1,c2,k1,k2,prek,k;
    (c1,c2) <- c;
    k2 <- exp c2 (val _sk2);
    if (c.`1 = _c1) {
       prek <@ O.f(label,k2,c2,_pk2);
       k <- Some prek;
    }
    else {
       k1 <@ KEMS.dec(_sk1,c1);
       prek <- F (oget k1) (label,k2,c2,_pk2);
       k <- if k1 = None then None else Some prek;
    }
    return k;
  }
}.



module XWING1BadL(KEMS : KEM.Scheme, O : PRF) = {
  include var XWING1(KEMS,O) [-dec]
  proc dec(sk : skey, c : ciphertext) : shkey option  = {
    var c1,c2,k1,k2,prek,k;
    (c1,c2) <- c;
    k2 <- exp c2 (val _sk2);
    if (c.`1 = _c1) {
       k1 <@ KEMS.dec(_sk1,c1);
       if (k1 <> Some _kb1) { 
          bad <- true; 
          prek <- F (oget k1) (label,k2,c2,_pk2);
          k <- if k1 = None then None else Some prek;
       }
       else {
          prek <@ O.f(label,k2,c2,_pk2);
          k <- Some prek;
       }
    }
    else {
       k1 <@ KEMS.dec(_sk1,c1);
       prek <- F (oget k1) (label,k2,c2,_pk2);
       k <- if k1 = None then None else Some prek;
    }
    return k;
  }  
}.

module XWING1BadR(KEMS : KEM.Scheme, O : PRF) = {
  include var XWING1(KEMS,O) [-dec]
  proc dec(sk : skey, c : ciphertext) : shkey option  = {
    var c1,c2,k1,k2,prek,k;
    (c1,c2) <- c;
    k2 <- exp c2 (val _sk2);
    if (c.`1 = _c1) {
       k1 <@ KEMS.dec(_sk1,c1);
       if (k1 <> Some _kb1) { 
          bad <- true; 
          prek <@ O.f(label,k2,c2,_pk2);
          k <- Some prek;
       }
       else {
          prek <@ O.f(label,k2,c2,_pk2);
          k <- Some prek;
       }
    }
    else {
       k1 <@ KEMS.dec(_sk1,c1);
       prek <- F (oget k1) (label,k2,c2,_pk2);
       k <- if k1 = None then None else Some prek;
    }
    return k;
  }  
}.

module CCABad(S : Scheme, A : CCA_ADV) = {
   include var CCA(S,A) [-mainL,mainR]

   proc mainL() : bool = {
      var bb;
      XWING1.bad <- false;
      bb <@ CCA(S,A).mainL();
      return bb;
   }
   proc mainR() : bool = {
      var bb;
      XWING1.bad <- false;
      bb <@ CCA(S,A).mainR();
      return bb;
   }

}.


section.

declare module A <: CCA_ADV  {-CCA, -KEM.CCA, -XWING1, -RF, -PRF}.
declare module KEMS <: KEM.Scheme {-A, -CCA, -KEM.CCA, -XWING1, -RF, -PRF}.

  
lemma hop1_up2bad &m :
  (forall (O <: CCA_ORC{-A} ), islossless O.dec => islossless A(O).guess) =>
  (forall _st, phoare [ KEMS.dec : (glob KEMS) = _st ==> (glob KEMS) = _st] = 1%r) =>
  `| Pr [ CCA(XWING(KEMS),A).mainL() @ &m : res ] - 
     Pr [ CCA(XWING1(KEMS,PRF),A).mainL() @ &m : res ] | <= 
      Pr [ CCABad(XWING1BadR(KEMS,PRF),A).mainL() @ &m : XWING1.bad ]. 
proof.
move => A_ll dec_pure.
have -> : Pr [ CCA(XWING(KEMS),A).mainL() @ &m : res ] = 
           Pr [ CCABad(XWING1BadL(KEMS,PRF),A).mainL() @ &m : res ].
+ byequiv => //. 
  proc;inline *;wp; call(: ={glob CCA, glob KEMS}
                       /\ CCA.sk.`1{1} = XWING1._sk1{2}
                       /\ CCA.sk.`2{1} = XWING1._sk2{2}
                       /\ CCA.sk.`3{1} = XWING1._pk2{2}
                       /\ XWING1._kb1{2} = PRF.k{2}). 
  + proc;inline *. 
    sp; if;1,3: by auto => />;smt().
    sp;if{2}; by wp;call(:true); auto. 
  by auto;call(:true);auto;call(:true);auto.
    

have -> : Pr [ CCA(XWING1(KEMS,PRF),A).mainL() @ &m : res ] = 
           Pr [ CCABad(XWING1BadR(KEMS,PRF),A).mainL() @ &m : res ].
+ byequiv => //. 
  proc;inline *;wp; call(: ={glob CCA, glob KEMS, XWING1._sk1, XWING1._sk2, XWING1._pk2, XWING1._kb1, XWING1._c1, glob PRF}). 
  + proc;inline *. 
    sp; if;1,3: by auto => />;smt().
    sp;if;1: by auto => />;smt().
    + by auto;ecall{2} (dec_pure (glob KEMS){2});auto => />.
    by wp;call(:true); auto. 
  by auto;call(:true);auto;call(:true);auto.
    
have : 
  `|Pr[CCABad(XWING1BadL(KEMS, PRF), A).mainL() @ &m : res] - Pr[CCABad(XWING1BadR(KEMS, PRF), A).mainL() @ &m : res]| <=
     RealOrder.maxr Pr[CCABad(XWING1BadL(KEMS, PRF), A).mainL() @ &m : XWING1.bad]
          Pr[CCABad(XWING1BadR(KEMS, PRF), A).mainL() @ &m : XWING1.bad] by byupto.

have -> : 
  Pr[CCABad(XWING1BadL(KEMS, PRF), A).mainL() @ &m : XWING1.bad] =
   Pr[CCABad(XWING1BadR(KEMS, PRF), A).mainL() @ &m : XWING1.bad]; last by smt(). 
+ byequiv => //. 
  proc;inline *;wp.
  call(: XWING1.bad, ={glob CCA, glob KEMS, glob XWING1, glob PRF},={XWING1.bad}). 
  + proc;inline *. 
    sp; if;1,3: by auto => />;smt().
    sp;if;1: by auto => />;smt().
    + by auto;call(:true);auto => />.
    by auto;call(:true);auto => />.
  + move => &hr bad;proc. 
    inline *;sp;if;2:by auto.
    sp;if;wp;call(:true). 
    + proc*;exists * (glob KEMS); elim* => _st;call (dec_pure _st);auto. 
    + by auto; smt().
    + proc*;exists * (glob KEMS); elim* => _st;call (dec_pure _st);auto. 
    by auto; smt().
  + move => &hr;proc. 
    inline *;sp;if;2:by auto.
    sp;if;wp;call(:true). 
    + proc*;exists * (glob KEMS); elim* => _st;call (dec_pure _st);auto. 
    + by auto; smt().
    + proc*;exists * (glob KEMS); elim* => _st;call (dec_pure _st);auto. 
    by auto; smt().
   
by auto;call(:true);auto;call(:true);auto => /#.
qed.

lemma hop6_up2bad &m :
  (forall (O <: CCA_ORC{-A} ), islossless O.dec => islossless A(O).guess) =>
  (forall _st, phoare [ KEMS.dec : (glob KEMS) = _st ==> (glob KEMS) = _st] = 1%r) =>
  `| Pr [ CCA(XWING(KEMS),A).mainR() @ &m : res ] - 
     Pr [ CCA(XWING1(KEMS,PRF),A).mainR() @ &m : res ] | <= 
      Pr [ CCABad(XWING1BadR(KEMS,PRF),A).mainR() @ &m : XWING1.bad ]. 
proof.
move => A_ll dec_pure.
have -> : Pr [ CCA(XWING(KEMS),A).mainR() @ &m : res ] = 
           Pr [ CCABad(XWING1BadL(KEMS,PRF),A).mainR() @ &m : res ].
+ byequiv => //. 
  proc;inline *;wp; call(: ={glob CCA, glob KEMS}
                       /\ CCA.sk.`1{1} = XWING1._sk1{2}
                       /\ CCA.sk.`2{1} = XWING1._sk2{2}
                       /\ CCA.sk.`3{1} = XWING1._pk2{2}
                       /\ XWING1._kb1{2} = PRF.k{2}). 
  + proc;inline *. 
    sp; if;1,3: by auto => />;smt().
    sp;if{2};by wp;call(:true); auto. 
  by auto;call(:true);auto;call(:true);auto.
    
have -> : Pr [ CCA(XWING1(KEMS,PRF),A).mainR() @ &m : res ] = 
           Pr [ CCABad(XWING1BadR(KEMS,PRF),A).mainR() @ &m : res ].
+ byequiv => //. 
  proc;inline *;wp; call(: ={glob CCA, glob KEMS, XWING1._sk1, XWING1._sk2, XWING1._pk2, XWING1._kb1, XWING1._c1, glob PRF}). 
  + proc;inline *. 
    sp; if;1,3: by auto => />;smt().
    sp;if;1: by auto => />;smt().
    by auto;ecall{2} (dec_pure (glob KEMS){2});auto => />.
    by wp;call(:true); auto. 
  by auto;call(:true);auto;call(:true);auto.
    
have : 
  `|Pr[CCABad(XWING1BadL(KEMS, PRF), A).mainR() @ &m : res] - Pr[CCABad(XWING1BadR(KEMS, PRF), A).mainR() @ &m : res]| <=
     RealOrder.maxr Pr[CCABad(XWING1BadL(KEMS, PRF), A).mainR() @ &m : XWING1.bad]
          Pr[CCABad(XWING1BadR(KEMS, PRF), A).mainR() @ &m : XWING1.bad] by byupto.

have -> : 
  Pr[CCABad(XWING1BadL(KEMS, PRF), A).mainR() @ &m : XWING1.bad] =
   Pr[CCABad(XWING1BadR(KEMS, PRF), A).mainR() @ &m : XWING1.bad]; last by smt(). 
+ byequiv => //. 
  proc;inline *;wp.
  call(: XWING1.bad, ={glob CCA, glob KEMS, glob XWING1, glob PRF},={XWING1.bad}). 
  + proc;inline *. 
    sp; if;1,3: by auto => />;smt().
    sp;if;1: by auto => />;smt().
    + by auto;call(:true);auto => />.
    by auto;call(:true);auto => />.
  + move => &hr bad;proc. 
    inline *;sp;if;2:by auto.
    sp;if;wp;call(:true). 
    + proc*;exists * (glob KEMS); elim* => _st;call (dec_pure _st);auto. 
    + by auto; smt().
    + proc*;exists * (glob KEMS); elim* => _st;call (dec_pure _st);auto. 
    by auto; smt().
  + move => &hr;proc. 
    inline *;sp;if;2:by auto.
    sp;if;wp;call(:true). 
    + proc*;exists * (glob KEMS); elim* => _st;call (dec_pure _st);auto. 
    + by auto; smt().
    + proc*;exists * (glob KEMS); elim* => _st;call (dec_pure _st);auto. 
    by auto; smt().
   
by auto;call(:true);auto;call(:true);auto => /#.
qed.

end section.

module B2O(O : KEM.CCA_ORC)  : CCA_ORC = {
   proc dec(c : ciphertext) : shkey option = {
    var c1,c2,k1,k2,prek,k;
    k <- None;
    if (c <> (XWING1._c1,XWING1._c2)) {
       (c1,c2) <- c;
       k2 <- exp c2 (val XWING1._sk2);
       if (c.`1 = XWING1._c1) {
          prek <- F XWING1._kb1 (label,k2,c2,XWING1._pk2);
          k <- Some prek;
       }
       else {
          k1 <@ O.dec(c1);
          prek <- F (oget k1) (label,k2,c2,XWING1._pk2);
          k <- if k1 = None then None else Some prek;
       }
    }
    return k;
   }
}.

module (B2(A : CCA_ADV) : KEM.CCA_ADV) (O : KEM.CCA_ORC) = {
  proc guess(pk1 : KEM.pkey, c1 : KEM.ciphertext, k1 : KEM.key) : bool = {
     var k2,k,b';
     PRF.k <- k1;
     XWING1._kb1 <- k1;
     XWING1._sk2 <$ dH;
     XWING1._pk2 <- exp g (val XWING1._sk2);
     XWING1._rv2 <$ dH;
     XWING1._c1 <- c1;
     XWING1._c2 <- exp g (val XWING1._rv2);
     k2 <- exp XWING1._pk2 (val XWING1._rv2);
     k <- F k1 (label,k2,XWING1._c2,XWING1._pk2);
     b' <@ A(B2O(O)).guess((pk1,XWING1._pk2),(c1,XWING1._c2),k);
     return b';
  }
}.

module (B4(A : CCA_ADV) : KEM.CCA_ADV) (O : KEM.CCA_ORC) = {
  proc guess(pk1 : KEM.pkey, c1 : KEM.ciphertext, k1 : KEM.key) : bool = {
     var k2,k,b';
     PRF.k <- k1;
     XWING1._kb1 <- k1;
     XWING1._sk2 <$ dH;
     XWING1._pk2 <- exp g (val XWING1._sk2);
     XWING1._rv2 <$ dH;
     XWING1._c1 <- c1;
     XWING1._c2 <- exp g (val XWING1._rv2);
     k2 <- exp XWING1._pk2 (val XWING1._rv2);
     k <$ dshkey;
     b' <@ A(B2O(O)).guess((pk1,XWING1._pk2),(c1,XWING1._c2),k);
     return b';
  }
}.

module XWING2(KEMS : KEM.Scheme, O : PRF) = {
  include var XWING1(KEMS,O) [-enc]
  
  proc enc(pk : pkey) : ciphertext * shkey = {
    var pk1,pk2,k2,k,c;
    (pk1,pk2) <- pk;
    (_c1,_kb1) <@ KEMS.enc(pk1);
    _rv2 <$ dH;
    _c2 <- exp g (val _rv2);
    k2 <- exp _pk2 (val _rv2);
    O.init();
    k <@ O.f(label,k2,_c2,_pk2);
    c <- (_c1,_c2);
    return (c,k);
  }
}.

module XWINGD0(KEMS : KEM.Scheme, O : PRF_Oracles) = {

  module OD = {
    proc init() = {}
    proc f = O.f
  }

  include var XWING1(KEMS,OD) [-enc]
  
  proc enc(pk : pkey) : ciphertext * shkey = {
    var pk1,pk2,k2,k,c;
    (pk1,pk2) <- pk;
    (_c1,_kb1) <@ KEMS.enc(pk1);
    _rv2 <$ dH;
    _c2 <- exp g (val _rv2);
    k2 <- exp _pk2 (val _rv2);
    k <@ O.f(label,k2,_c2,_pk2);
    c <- (_c1,_c2);
    return (c,k);
  }
}.

module (D0(KEMS : KEM.Scheme, A : CCA_ADV) : Distinguisher) (O : PRF_Oracles) = {
   proc distinguish = CCA(XWINGD0(KEMS,O),A).mainL
}.

module XWINGD1(KEMS : KEM.Scheme, O : PRF_Oracles) = {

  module OD = {
    proc init() = {}
    proc f = O.f
  }

  include var XWING1(KEMS,OD) [-enc]
  
  proc enc(pk : pkey) : ciphertext * shkey = {
    var pk1,pk2,k2,k,c;
    (pk1,pk2) <- pk;
    (_c1,_kb1) <@ KEMS.enc(pk1);
    _rv2 <$ dH;
    _c2 <- exp g (val _rv2);
    k2 <- exp _pk2 (val _rv2);
    k <$ dshkey;
    c <- (_c1,_c2);
    return (c,k);
  }
}.


module (D1(KEMS : KEM.Scheme, A : CCA_ADV) : Distinguisher) (O : PRF_Oracles) = {
   proc distinguish = CCA(XWINGD1(KEMS,O),A).mainR
}.


section.

declare module A <: CCA_ADV  {-CCA, -KEM.CCA, -XWING1, -RF}.
declare module KEMS <: KEM.Scheme {-A, -CCA, -KEM.CCA, -XWING1, -RF}.

lemma hop2_left &m :
  Pr [ CCA(XWING1(KEMS,PRF),A).mainL() @ &m : res ] = 
    Pr [ KEM.CCA(KEMS,B2(A)).mainL() @ &m : res ]. 
proof.
byequiv => //. 
proc;inline *.
wp;call(: ={glob KEMS,XWING1._sk2,XWING1._pk2, XWING1._c1} 
      /\ PRF.k{1} = XWING1._kb1{2} 
      /\ CCA.cstar{1} <> None 
      /\ XWING1._sk1{1} = CCA.sk{1}.`1
      /\ oget CCA.cstar{1} = (XWING1._c1, XWING1._c2){2} 
      /\ KEM.CCA.cstar{2} = Some XWING1._c1{2}
      /\ CCA.sk{1}.`1 =  KEM.CCA.sk{2} 
      /\ CCA.sk{1}.`2 = XWING1._sk2{2} 
      /\ CCA.sk{1}.`3 = XWING1._pk2{2}). 
+ proc;inline *.
  sp; if; 1,3: by auto => />;smt().
  sp;if;1,2: by auto => />;smt().
  rcondt{2} 3; 1: by auto => />.
  by wp;call(:true);auto  => />.

swap {2} 11 -8.
by auto;call(:true);wp;rnd{1};rnd{2};auto;call(:true);auto => />. 
qed.

  
lemma hop2_right &m :
  Pr [ CCA(XWING2(KEMS,PRF),A).mainL() @ &m : res ] = 
    Pr [ KEM.CCA(KEMS,B2(A)).mainR() @ &m : res ]. 
proof.
byequiv => //. 
proc;inline *.
wp;call(: ={glob KEMS,XWING1._sk2,XWING1._pk2, XWING1._c1} 
      /\ PRF.k{1} = XWING1._kb1{2} 
      /\ CCA.cstar{1} <> None 
      /\ XWING1._sk1{1} = CCA.sk{1}.`1
      /\ oget CCA.cstar{1} = (XWING1._c1, XWING1._c2){2} 
      /\ KEM.CCA.cstar{2} = Some XWING1._c1{2}
      /\ CCA.sk{1}.`1 =  KEM.CCA.sk{2} 
      /\ CCA.sk{1}.`2 = XWING1._sk2{2} 
      /\ CCA.sk{1}.`3 = XWING1._pk2{2}). 
+ proc;inline *.
  sp; if; 1,3: by auto => />;smt().
  sp;if;1,2: by auto => />;smt().
  rcondt{2} 3; 1: by auto => />.
  by wp;call(:true);auto  => />.

swap {2} 11 -8; swap {1} 14 -9.
by auto;call(:true);wp;rnd{1};auto;call(:true);auto. 
qed.

lemma hop3_left &m :
  Pr [ CCA(XWING2(KEMS,PRF),A).mainL() @ &m : res ] = 
    Pr [ IND(PRF,D0(KEMS,A)).main() @ &m : res ]. 
proof.
byequiv => //.
proc;inline *.
by swap {1} 14 -13;wp;sim.  
qed.

lemma hop3_right &m :
  Pr [ CCA(XWING2(KEMS,RF),A).mainL() @ &m : res ] = 
    Pr [ IND(RF,D0(KEMS,A)).main() @ &m : res ]. 
proof.
byequiv => //.
proc;inline *.
by wp;sim;auto;call (:true);auto;call(:true);auto => />.
qed.

lemma hop4_left &m :
  Pr [ CCA(XWING2(KEMS,RF),A).mainL() @ &m : res ] = 
    Pr [ IND(RF,D1(KEMS,A)).main() @ &m : res ]. 
proof.
byequiv => //.
proc;inline *.
wp;call(: ={glob CCA, XWING1._c1, XWING1._c2, XWING1._pk2, XWING1._sk2, XWING1._sk1, glob KEMS} 
     /\ eq_except (pred1 (label, exp XWING1._pk2 (val XWING1._rv2) , XWING1._c2, XWING1._pk2){1}) RF.m{1} RF.m{2}
     /\ (label, exp XWING1._pk2 (val XWING1._rv2) , XWING1._c2, XWING1._pk2){1} \in RF.m{1} /\
     CCA.cstar{1} = Some (XWING1._c1,XWING1._c2){1}); last first. 
+ rcondt{1} 16; 1: by auto;call(:true);auto;call(:true);auto => />;smt(mem_empty).
  swap{2} 8 8. swap {2} 14 -8. 
  by auto;call(:true);auto;call(:true);auto => />; smt(get_setE eq_exceptSm).  

proc;inline *.
sp;if;1,3: by auto.
sp;if;1: by auto.
+ case(c2{1} = XWING1._c2{1}).
  + rcondf{1} 2;1: by auto => />;smt(). 
    rcondf{2} 2;1: by auto => />;smt(). 
    by auto => />.
  by sp;if;auto => />;smt(get_setE eq_exceptSm).  

by wp;call(:true);auto.
qed.

lemma hop4_right &m :
  Pr [ CCA(XWING2(KEMS,PRF),A).mainR() @ &m : res ] = 
    Pr [ IND(PRF,D1(KEMS,A)).main() @ &m : res ]. 
proof.
byequiv => //.
proc;inline *.
swap {1} 14 -13;wp.
call(: ={glob CCA, XWING1._c1, XWING1._c2, XWING1._pk2, XWING1._sk2, XWING1._sk1, glob KEMS, glob PRF}).
+ proc;inline *.
  sp;if;1,3:by auto.
  sp;if;1:by auto.
  + by auto => />. 
  by auto;call(:true).

by auto;rnd{2};auto;call(:true);auto;call(:true);auto. 
qed.

lemma hop5_left &m :
  Pr [ CCA(XWING2(KEMS,PRF),A).mainR() @ &m : res ] = 
    Pr [ KEM.CCA(KEMS,B4(A)).mainR() @ &m : res ]. 
proof.
byequiv => //. 
proc;inline *.
wp;call(: ={glob KEMS,XWING1._sk2,XWING1._pk2, XWING1._c1} 
      /\ PRF.k{1} = XWING1._kb1{2} 
      /\ CCA.cstar{1} <> None 
      /\ XWING1._sk1{1} = CCA.sk{1}.`1
      /\ oget CCA.cstar{1} = (XWING1._c1, XWING1._c2){2} 
      /\ KEM.CCA.cstar{2} = Some XWING1._c1{2}
      /\ CCA.sk{1}.`1 =  KEM.CCA.sk{2} 
      /\ CCA.sk{1}.`2 = XWING1._sk2{2} 
      /\ CCA.sk{1}.`3 = XWING1._pk2{2}). 
+ proc;inline *.
  sp; if; 1,3: by auto => />;smt().
  sp;if;1,2: by auto => />;smt().
  rcondt{2} 3; 1: by auto => />.
  by wp;call(:true);auto  => />.

swap {1} 14 -11;swap {1} 8 6;swap {2} 11 -7.
by auto;call(:true);auto;call(:true);auto.
qed.

lemma hop5_right &m :
  Pr [ CCA(XWING1(KEMS,PRF),A).mainR() @ &m : res ] = 
    Pr [ KEM.CCA(KEMS,B4(A)).mainL() @ &m : res ]. 
proof.
byequiv => //. 
proc;inline *.
wp;call(: ={glob KEMS,XWING1._sk2,XWING1._pk2, XWING1._c1} 
      /\ PRF.k{1} = XWING1._kb1{2} 
      /\ CCA.cstar{1} <> None 
      /\ XWING1._sk1{1} = CCA.sk{1}.`1
      /\ oget CCA.cstar{1} = (XWING1._c1, XWING1._c2){2} 
      /\ KEM.CCA.cstar{2} = Some XWING1._c1{2}
      /\ CCA.sk{1}.`1 =  KEM.CCA.sk{2} 
      /\ CCA.sk{1}.`2 = XWING1._sk2{2} 
      /\ CCA.sk{1}.`3 = XWING1._pk2{2}). 
+ proc;inline *.
  sp; if; 1,3: by auto => />;smt().
  sp;if;1,2: by auto => />;smt().
  rcondt{2} 3; 1: by auto => />.
  by wp;call(:true);auto  => />.


swap {1} 7 4; swap {2} 11 -7. 
by auto;call(:true);auto;call(:true);auto. 
qed.

end section.

section.

declare module A <: CCA_ADV  {-CCA, -KEM.CCA, -XWING1, -RF}.
declare module KEMS <: KEM.Scheme {-A, -CCA, -KEM.CCA, -XWING1, -RF}.

declare op dec : KEM.skey -> KEM.ciphertext -> KEM.key option.

lemma bad0 &m :
  (forall (O <: CCA_ORC{-A} ), islossless O.dec => islossless A(O).guess) =>
  (forall _st _sk _c, phoare[ KEMS.dec : (glob KEMS) = _st /\ arg=(_sk,c) ==> (glob KEMS) = _st /\ res = dec _sk _c] = 1%r) =>
   Pr [ CCABad(XWING1BadR(KEMS,PRF),A).mainL() @ &m : XWING1.bad ] <= 
     Pr[ KEM.Correctness(KEMS).main() @ &m : res].
proof. 
move => A_ll dec_pure.
byequiv => //.
proc;inline*;wp. 
call{1} (: !XWING1.bad ==> XWING1.bad => dec XWING1._sk1 XWING1._c1 <> Some XWING1._kb1).
proc(XWING1.bad => dec XWING1._sk1 XWING1._c1 <> Some XWING1._kb1);1,2: by smt().
+ by apply A_ll.
+ proc;inline *.
  sp;if;2:by auto.
  sp;if; last first. 
  + auto;call(: true); last by auto.
    by proc*;exists * (glob KEMS), sk, c; elim* => _st _sk _c;call (dec_pure _st _sk _c);auto.  
  by wp;exists * (glob KEMS), XWING1._sk1, c1; elim* => _st _sk _c;call (dec_pure _st _sk _c);auto => />.

by wp;ecall{2} (dec_pure (glob KEMS){2} sk{2} c{2}); auto;call(:true); auto;call(:true);auto => />.
qed.

lemma bad1 &m :
  (forall (O <: CCA_ORC{-A} ), islossless O.dec => islossless A(O).guess) =>
  (forall _st _sk _c, phoare[ KEMS.dec : (glob KEMS) = _st /\ arg=(_sk,c) ==> (glob KEMS) = _st /\ res = dec _sk _c] = 1%r) =>
   Pr [ CCABad(XWING1BadR(KEMS,PRF),A).mainR() @ &m : XWING1.bad ]<= 
     Pr[ KEM.Correctness(KEMS).main() @ &m : res].
proof. 
move => A_ll dec_pure.
byequiv => //.
proc;inline*;wp. 
call{1} (: !XWING1.bad ==> XWING1.bad => dec XWING1._sk1 XWING1._c1 <> Some XWING1._kb1).
proc(XWING1.bad => dec XWING1._sk1 XWING1._c1 <> Some XWING1._kb1);1,2: by smt().
+ by apply A_ll.
+ proc;inline *.
  sp;if;2:by auto.
  sp;if; last first. 
  + auto;call(: true); last by auto.
    by proc*;exists * (glob KEMS), sk, c; elim* => _st _sk _c;call (dec_pure _st _sk _c);auto.  
  by wp;exists * (glob KEMS), XWING1._sk1, c1; elim* => _st _sk _c;call (dec_pure _st _sk _c);auto => />.

by wp;ecall{2} (dec_pure (glob KEMS){2} sk{2} c{2}); auto;call(:true); auto;call(:true);auto => />.
qed.

lemma pre_final &m : 
  (forall (O <: CCA_ORC{-A} ), islossless O.dec => islossless A(O).guess) =>
  (forall _st _sk _c, phoare[ KEMS.dec : (glob KEMS) = _st /\ arg=(_sk,c) ==> (glob KEMS) = _st /\ res = dec _sk _c] = 1%r) =>
 `| Pr [ CCA(XWING(KEMS),A).mainL() @ &m : res ] - 
       Pr [ CCA(XWING(KEMS),A).mainR() @ &m : res ] | <= 
         2%r * Pr[ KEM.Correctness(KEMS).main() @ &m : res] + 
         `| Pr [ KEM.CCA(KEMS,B2(A)).mainL() @ &m : res ] - Pr [ KEM.CCA(KEMS,B2(A)).mainR() @ &m : res ]| + 
         `| Pr [ KEM.CCA(KEMS,B4(A)).mainL() @ &m : res ] - Pr [ KEM.CCA(KEMS,B4(A)).mainR() @ &m : res ]| + 
         `| Pr [ IND(PRF,D0(KEMS,A)).main() @ &m : res ] - Pr [ IND(RF,D0(KEMS,A)).main() @ &m : res ]| +
         `| Pr [ IND(PRF,D1(KEMS,A)).main() @ &m : res ] - Pr [ IND(RF,D1(KEMS,A)).main() @ &m : res ]|.
proof.
move => All dec_pure.
have bad0 := bad0 &m All dec_pure.
have hop1 := hop1_up2bad A KEMS &m All _.
+ by move => _st;proc*;exists * sk, c; elim* => _sk _c;call (dec_pure _st _sk _c);auto => />.
have hop2l := hop2_left A KEMS &m.
have hop2r := hop2_right A KEMS &m.
have hop3l := hop3_left A KEMS &m.
have hop3r := hop3_right A KEMS &m.
have hop4l := hop4_left A KEMS &m.
have hop4r := hop4_right A KEMS &m.
have hop5l := hop5_left A KEMS &m.
have hop5r := hop5_right A KEMS &m.
have hop6 := hop6_up2bad A KEMS &m All _.
+ by move => _st;proc*;exists * sk, c; elim* => _sk _c;call (dec_pure _st _sk _c);auto => />.
have bad1 := bad1 &m All dec_pure.

rewrite -hop2l -hop2r -hop3l -hop3r -hop4l -hop4r -hop5l -hop5r.

by smt().
qed.


 
end section.

