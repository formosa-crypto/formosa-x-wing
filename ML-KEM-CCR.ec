require import AllCore Distr StdOrder SmtMap Real DProd.
require import KEM_ROM.

type pkey.
type skey.
type randomness.
type plaintext.
type ciphertext.
op randd : randomness distr.
op dplaintext : plaintext distr.

op kg : (pkey * skey) distr.
op enc : randomness -> pkey -> plaintext -> ciphertext.
op dec : skey -> ciphertext -> plaintext option.

type K.
op dK : K distr.

type key.
op [lossless uniform full] dkey : key distr.

type pkhash.
op pkh : pkey -> pkhash.

clone import KEM_ROM.KEM_ROM_x2 as KEMROMx2 with
   type pkey <- pkey,
   type skey = (pkey * skey) * K,
   type ciphertext <- ciphertext,
   type key <- key,
   op dkey <- dkey,
   type RO1.in_t <- plaintext * pkhash,
   type RO1.out_t <- key * randomness,
   op   RO1.dout <- fun _ => dkey `*` randd,
   type RO1.d_in_t <- unit,
   type RO1.d_out_t <- bool,
   type RO2.in_t <- K * ciphertext,
   type RO2.out_t <- key,
   op   RO2.dout <- fun _ => dkey,
   type RO2.d_in_t <- unit,
   type RO2.d_out_t <- bool
   proof dkey_ll by apply dkey_ll
   proof dkey_uni by apply dkey_uni
   proof dkey_fu by apply dkey_fu
   proof *.


module (FO_K_JRO : KEMROMx2.Scheme) (H : POracle_x2) = {
  var _m' : plaintext option
  var _c' : ciphertext
  var _c  : ciphertext

  proc kg() : pkey * skey = {
     var pk, sk, k;
     (pk,sk) <$ kg;
     k <$ dK;
     return (pk, ((pk,sk),k));
  }

  proc enc(pk : pkey) : ciphertext * key = {
     var m, r, c, k;
     m <$ dplaintext;
     (k,r) <@ H.get1(m, pkh pk);
     c <- enc r pk m;
     return (c,k);
  }

  proc dec(sk : skey, c : ciphertext) : key option = {
     var ks, r, kn;
     _c <- c;
     _m' <- dec sk.`1.`2 c;
     (ks,r) <@ H.get1(oget _m',pkh sk.`1.`1);
     kn <@ H.get2(sk.`2,c);
     _c' <- enc r sk.`1.`1 (oget _m');
     return if (_m' <> None /\ _c' = _c) then (Some ks) else (Some kn);
  }
}.

module CountHx2(H : KEMROMx2.POracle_x2) = {
  var c_1   : int
  var c_2   : int
  var skstar : key
  var xstar : plaintext * pkhash
  var bad_rej : bool
  var bad_acc : bool

  proc init (sk : key, x : plaintext * pkhash) = { c_1 <- 0; c_2 <- 0; bad_rej <- false; bad_acc <- false; skstar <- sk; xstar <- x; }

  proc get1(x) = {
    var r;
    r <@ H.get1(x);
    c_1 <- c_1 + 1;
    bad_acc <- bad_acc \/ (x.`2 = xstar.`2 /\ x.`1 <> xstar.`1 /\ r.`1 = skstar);
    return r;
  }
  proc get2(x) = {
    var r;
    r <@ H.get2(x);
    c_2 <- c_2 + 1;
    bad_rej <- bad_rej \/ (r = skstar);
    return r;
  }
}.

module CCR_instr(H : Oracle_x2, S:Scheme, A:CCR_ADV) = {
  var _c0 : ciphertext
  var _sk : skey
  var _pk : pkey
  proc main() : bool = {
    var k0 : key;
    var k1 : key option;
    var c1 : ciphertext;
    var m, r;
    H.init();
    (_pk, _sk) <@ S(H).kg();
     m <$ dplaintext;
     (k0,r) <@ H.get1(m, pkh _pk);
    _c0 <- enc r _pk m;
    CountHx2(H).init(k0,(m,pkh _pk));
    c1       <@ A(CountHx2(H)).find(_pk, _sk, _c0, k0);
    k1       <@ S(CountHx2(H)).dec(_sk,c1);
    return (c1 <> _c0 && k1 = Some k0);
  }
}.


section.

declare module A <: CCR_ADV {-CountHx2, -RO1.RO, -RO2.RO, -FO_K_JRO, -CCR_instr}.

declare op qH1 : { int | 0 <= qH1 } as ge0_qH1.
declare op qH2 : { int | 0 <= qH2 } as ge0_qH2.

lemma implicit &m :
  (forall (O <: POracle_x2), hoare [ A(CountHx2(O)).find : CountHx2.c_2 = 0  ==> CountHx2.c_2 <= qH2 ]) =>
  Pr[CCR_instr(RO_x2(RO1.RO, RO2.RO), FO_K_JRO, A).main() @ &m : res /\ ! (FO_K_JRO._m' <> None /\ FO_K_JRO._c' = FO_K_JRO._c)] <=
    (qH2 + 1)%r * mu1 dkey witness.
  move => Hcount2.
  rewrite Pr[ mu_split (CountHx2.c_2 <= qH2 + 1)].
  have -> /= : Pr[CCR_instr(RO_x2(RO1.RO, RO2.RO), FO_K_JRO, A).main() @ &m :
    (res /\ ! (FO_K_JRO._m' <> None /\ FO_K_JRO._c' = FO_K_JRO._c)) /\  !CountHx2.c_2 <= qH2 + 1 ] = 0%r.
  + byphoare => //;hoare;proc.
  conseq(: _ ==> CountHx2.c_2 <= qH2 + 1); 1: by smt().
  seq 7: (CountHx2.c_2 <= qH2); last by inline *;auto => /#.
  call (: CountHx2.c_2 = 0 ==> CountHx2.c_2 <= qH2); 1: by
    apply (Hcount2 (RO_x2(RO1.RO, RO2.RO))).
  by inline *;auto.

  apply: (StdOrder.RealOrder.ler_trans Pr[CCR_instr(RO_x2(RO1.RO, RO2.RO), FO_K_JRO, A).main() @ &m : CountHx2.bad_rej /\ CountHx2.c_2 <= qH2 + 1 ]).
  + byequiv => //=.
  proc.
  inline {1} 8;inline {2} 8; wp => /=.
  conseq (: _ ==> ={CountHx2.c_2} /\ ((c1{1} <> CCR_instr._c0{1} && kn{1} = k0{1}) => CountHx2.bad_rej{2})); 1: by smt().
  inline {1} 13; inline {2} 13; wp.
  conseq (: ={r1,CountHx2.c_2} /\ k0{1} = CountHx2.skstar{2}); 1: by smt().
  by inline *;sim;auto.

  fel 6 (CountHx2.c_2)
        (fun _ => mu1 dkey witness)
        (qH2 + 1)
        (CountHx2.bad_rej)
        []
        ((!CountHx2.bad_rej => (forall x, x \in RO2.RO.m => (oget RO2.RO.m.[x]) <> CountHx2.skstar))).
  + rewrite StdBigop.Bigreal.BRA.sumri_const /=;1:by smt(ge0_qH2).
    by rewrite RField.intmulr /#.
  + by auto.
  + by inline *;auto => />;smt(ge0_qH2 emptyE).
  + proc;inline *;wp.
    case (x \in  RO2.RO.m); 1: by hoare; auto => /#.
    rnd (pred1 CountHx2.skstar); auto => *.
    by rewrite (dkey_uni _ witness) 1,2:dkey_fu /=; smt(get_setE).
  + by move => c; proc; inline *;auto; smt(get_setE).
  + move => b c.
    by proc;inline *;auto.
qed.

lemma accept &m :
  (forall (O <: POracle_x2), hoare [ A(CountHx2(O)).find : CountHx2.c_1 = 0  ==> CountHx2.c_1 <= qH1 ]) =>
  Pr[CCR_instr(RO_x2(RO1.RO, RO2.RO), FO_K_JRO, A).main() @ &m : res /\ (FO_K_JRO._m' <> None /\ FO_K_JRO._c' = FO_K_JRO._c)] <=
    (qH1 + 1)%r * mu1 dkey witness.
move => Hcount1.
rewrite Pr[ mu_split (CountHx2.c_1 <= qH1 + 1)].
have -> /= : Pr[CCR_instr(RO_x2(RO1.RO, RO2.RO), FO_K_JRO, A).main() @ &m :
   (res /\ (FO_K_JRO._m' <> None /\ FO_K_JRO._c' = FO_K_JRO._c)) /\  !CountHx2.c_1 <= qH1 + 1 ] = 0%r.
+ byphoare => //;hoare;proc.
  conseq(: _ ==> CountHx2.c_1 <= qH1 + 1); 1: by smt().
  seq 7: (CountHx2.c_1 <= qH1); last by inline *;auto => /#.
  call (: CountHx2.c_1 = 0 ==> CountHx2.c_1 <= qH1); 1: by
    apply (Hcount1 (RO_x2(RO1.RO, RO2.RO))).
  by inline *;auto.

  apply: (StdOrder.RealOrder.ler_trans Pr[CCR_instr(RO_x2(RO1.RO, RO2.RO), FO_K_JRO, A).main() @ &m : CountHx2.bad_acc /\ CountHx2.c_1 <= qH1 + 1 ]).
+ byequiv => //=.
  proc.
  seq 7 7 : (={glob A, m, k0,r,glob CCR_instr,RO1.RO.m,RO2.RO.m,glob CountHx2,c1}
        /\ CountHx2.xstar{2}.`2 = pkh CCR_instr._sk{2}.`1.`1
        /\ enc ((oget RO1.RO.m{2}.[CountHx2.xstar{2}]).`2) CCR_instr._sk{2}.`1.`1 CountHx2.xstar{2}.`1 = CCR_instr._c0{2}
        /\ CountHx2.xstar{2} \in RO1.RO.m{2}
        /\  ((oget RO1.RO.m{2}.[CountHx2.xstar{2}]).`1 = CountHx2.skstar{2})
        /\  CountHx2.skstar{2} = k0{2}
        /\ (!CountHx2.bad_acc{2} => forall x, x \in RO1.RO.m{2} => x.`2 = CountHx2.xstar{2}.`2 => x.`1 <> CountHx2.xstar{2}.`1 => (oget RO1.RO.m{2}.[x]).`1 <> CountHx2.skstar{2})).
  + call(: ={RO1.RO.m,RO2.RO.m,glob CCR_instr,glob CountHx2}
        /\ enc ((oget RO1.RO.m{2}.[CountHx2.xstar{2}]).`2) CCR_instr._sk{2}.`1.`1 CountHx2.xstar{2}.`1 = CCR_instr._c0{2}
        /\ CountHx2.xstar{2}.`2 = pkh CCR_instr._sk{2}.`1.`1
        /\ CountHx2.xstar{2} \in RO1.RO.m{2}
        /\  ((oget RO1.RO.m{2}.[CountHx2.xstar{2}]).`1 = CountHx2.skstar{2})
        /\ (!CountHx2.bad_acc{2} => forall x, x \in RO1.RO.m{2} => x.`2 = CountHx2.xstar{2}.`2 => x.`1 <> CountHx2.xstar{2}.`1 => (oget RO1.RO.m{2}.[x]).`1 <> CountHx2.skstar{2})).
    + by proc;inline *;auto;smt(get_setE).
    + by proc;inline *;auto.
    by inline *;auto => />; smt(mem_empty get_setE).
  by inline *;auto => />;smt(get_setE).

  fel 6 (CountHx2.c_1)
        (fun _ => mu1 dkey witness)
        (qH1 + 1)
        (CountHx2.bad_acc)
        []
        ((!CountHx2.bad_acc =>
             (forall x, x \in RO1.RO.m =>
                        x.`2 = CountHx2.xstar.`2 =>
                        x.`1 <> CountHx2.xstar.`1 =>
                          (oget RO1.RO.m.[x]).`1 <> CountHx2.skstar))).
  + rewrite StdBigop.Bigreal.BRA.sumri_const /=;1:by smt(ge0_qH1).
    by rewrite RField.intmulr /#.
  + by auto.
  + by inline *; auto => /> *; smt(ge0_qH1 emptyE get_setE).
  + proc;inline *;wp.
    case (x \in  RO1.RO.m); 1: by hoare; auto => /#.
    rnd (fun r0 : _*_ => (pred1 CountHx2.skstar) r0.`1); auto => /> &hr *;split; 2: by smt(get_setE).
    rewrite (dprodEl dkey randd (pred1 CountHx2.skstar{hr})) (dkey_uni _ witness) 1,2:dkey_fu /=.
    by smt(mu_bounded RealOrder.ler_pimulr).
  + by move => c; proc; inline *;auto; smt(get_setE).
  + move => b c.
    by proc;inline *;auto.
qed.

lemma main &m :
  (forall (O <: POracle_x2), hoare [ A(CountHx2(O)).find : CountHx2.c_1 = 0  ==> CountHx2.c_1 <= qH1 ]) =>
  (forall (O <: POracle_x2), hoare [ A(CountHx2(O)).find : CountHx2.c_2 = 0  ==> CountHx2.c_2 <= qH2 ]) =>
   Pr [ CCR(RO_x2(RO1.RO,RO2.RO),FO_K_JRO,A).main() @ &m : res] <= (qH1 + qH2 + 2)%r * mu1 dkey witness.
proof.
  move => Hcount1 Hcount2.
  have -> : Pr [ CCR(RO_x2(RO1.RO,RO2.RO),FO_K_JRO,A).main() @ &m : res]  =
            Pr [ CCR_instr(RO_x2(RO1.RO,RO2.RO),FO_K_JRO,A).main() @ &m : res].
  + byequiv => //.
    proc.
    call(: ={glob RO1.RO, glob RO2.RO});
      1: by inline *; auto.
    call(: ={glob RO1.RO, glob RO2.RO});
     1,2: by proc;inline *; auto.
    inline {1} 3;inline {2} 6; wp => />;1: by smt().
    by inline *;auto.

  rewrite Pr[ mu_split (FO_K_JRO._m' <> None /\ FO_K_JRO._c' = FO_K_JRO._c)].
  have ? := implicit &m Hcount2.
  have ? := accept &m Hcount1.
  by smt().
qed.
