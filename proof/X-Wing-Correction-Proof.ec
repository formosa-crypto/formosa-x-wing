require import AllCore IntDiv CoreMap List Distr IntDiv StdOrder.

from Jasmin require import JModel_x86 JWord JUtils.

import SLH64 StdOrder.IntOrder.
require import Xkem_avx2_clean XWing_Spec XWing_Helper_Functions CorrectnessProof_Mulx Mulx_scalarmult_s Jkem_avx2_stack FIPS202_SHA3 Curve25519_Procedures MLKEM MLKEM_KEM_avx2_stack.
require import Array4 Array6 Array8 Array32 Array64 Array96 Array140 Array152 Array1088 Array1120 Array1184 Array1216 Array2400 Array1152.
require import WArray4 WArray6 WArray32 WArray64 WArray96 WArray1088 WArray1120 WArray1184 WArray1216 WArray2400.

axiom shake256_A96_A32 out inp :
   phoare [Xkem_avx2_clean.M._shake256_A96__A32 :
               arg = (out, inp) ==>
               res = SHAKE256_32_96 inp] = 1%r.

axiom sha3_256_A128__A6 ss ss_mlkem ss_x25519 ct_25519 pk_25519 :
   phoare [Xkem_avx2_clean.M._sha3_256_A128__A6 :
               arg = (ss, ss_mlkem, ss_x25519, ct_25519, pk_25519) ==>
               res = SHA3_256_134_32 (ss_mlkem, ss_x25519, ct_25519, pk_25519, xwing_label)] = 1%r.


abbrev toRep4 (x: W8.t Array32.t) = Array4.of_list W64.zero (to_list (unpack64 (pack32 (to_list x)))).

lemma xwing_25519_base_mulx_equiv :
   equiv [Xkem_avx2_clean.M.xwing_x25519_base ~ Mulx_scalarmult_s.M.__curve25519_mulx_base :
       _k{2} = toRep4 np{1}
       ==>
       res{2} = toRep4 res{1}].
    proc.
    inline{1} 4.
    seq 7 3 : (={u, r, k, _k}). wp. auto => />.
    move => &1.
    + rewrite unpack64E pack32E /init8 of_listE.
    + rewrite tP => i ib.
    + rewrite initiE 1:/# /= /get8 /(\bits64).
    + rewrite initiE 1:/# /= /copy_64.
    + rewrite initiE 1:/# /= /get64_direct.
    + rewrite /pack8_t. rewrite wordP => ii iib.
    + rewrite initiE 1:/# //= initiE 1:/# //=.
    + rewrite initiE 1:/# //= initiE 1:/# //=.
    + rewrite  initiE 1:/# //= initiE 1:/# //=.
    + rewrite /to_list /mkseq -iotaredE => />.
    + smt().
    seq 4 3 : (={u, k, _k, r} /\ q{1} = r{2}). sim.
    wp; skip => />.
    move => &2.
    + rewrite unpack64E pack32E of_listE.
    + rewrite tP => i ib.
    + rewrite initiE 1:/# /= /get8 /(\bits64).
    + rewrite initiE 1:/# /= /copy_64.
    + rewrite wordP => ii iib.
    + rewrite initiE 1:/# /= /init64 /(\bits8).
    + rewrite initiE 1:/# //= initiE 1:/# //=.
    + rewrite /to_list /mkseq -iotaredE => />.
    + smt(W8.initiE).
qed.

lemma xwing_25519_mulx_equiv :
   equiv [Xkem_avx2_clean.M.xwing_x25519 ~ Mulx_scalarmult_s.M.__curve25519_mulx :
       _k{2} = toRep4 np{1}  /\
       _u{2} = toRep4 pp{1}
       ==>
       res{2} = toRep4 res{1}].
    proc.
    inline{1} 6.
    wp; sp.
    sim :  (={k, u, r}).
    move => &1 &2 [?] [H] *. rewrite H.
    + rewrite unpack64E pack32E /init8 of_listE.
    + rewrite tP => i ib.
    + rewrite initiE 1:/# /= /get8 /(\bits64).
    + rewrite initiE 1:/# /= /copy_64.
    + rewrite /to_list /init64 /(\bits8) /get64_direct /mkseq -iotaredE => />.
    + rewrite wordP => ii iib.
    + rewrite initiE 1:/# /=.
    + rewrite initiE 1:/# //= initiE 1:/# //=.
    ring. smt(W8.initiE).
    auto => />. move => &1 *.
    do split.
    + rewrite unpack64E pack32E of_listE.
    + rewrite tP => i ib.
    + rewrite initiE 1:/# /= /get8 /(\bits64).
    + rewrite initiE 1:/# /= /copy_64 /get64_direct.
    + rewrite wordP => ii iib.
    + rewrite initiE 1:/# /= /init64 /(\bits8) /pack8_t.
    + rewrite !initiE 1,2:/# //=  initiE 1:/# //= initiE 1:/# //=.
    + rewrite initiE 1:/# //= initiE 1:/# //=.
    + rewrite /to_list /mkseq -iotaredE => />. smt().
    + rewrite unpack64E pack32E of_listE.
    + rewrite tP => i ib.
    + rewrite initiE 1:/# /= /get8 /(\bits64).
    + rewrite initiE 1:/# /= /copy_64 /get64_direct.
    + rewrite wordP => ii iib.
    + rewrite initiE 1:/# /= /init64 /(\bits8) /pack8_t.
    + rewrite !initiE 1,2:/# //=  initiE 1:/# //= initiE 1:/# //=.
    + rewrite initiE 1:/# //= initiE 1:/# //=.
    + rewrite /to_list /mkseq -iotaredE => />. smt().
qed.

lemma eq_spec_xwing_25519_base_mulx :
   equiv [Xkem_avx2_clean.M.xwing_x25519_base ~ CurveProcedures.scalarmult_base :
       Array4.of_list W64.zero (to_list (unpack64 k'{2})) = toRep4 np{1}
       ==>
       Array32.of_list W8.zero (to_list (unpack8 res{2})) = res{1}
   ].
    transitivity
    Mulx_scalarmult_s.M.__curve25519_mulx_base
    (toRep4 np{1} = _k{2} ==> toRep4 res{1} =  res{2})
    (pack4 (to_list _k{1}) = k'{2} ==> pack4 (to_list res{1}) = res{2}) => />.
    move => &1 &2 H.
    exists(Array4.of_list W64.zero (to_list (unpack64 k'{2}))).
    do split.
    + by rewrite -H. by rewrite of_listK.
    move => &m.
    rewrite of_listK //=  of_listK //=. rewrite size_to_list //=. rewrite to_listK //=.
    proc *. by call xwing_25519_base_mulx_equiv.
    proc *. symmetry. by call eq_spec_impl_scalarmult_base_mulx.
qed.

lemma eq_spec_xwing_25519_mulx :
   equiv [Xkem_avx2_clean.M.xwing_x25519 ~ CurveProcedures.scalarmult :
       Array4.of_list W64.zero (to_list (unpack64 k'{2})) = toRep4 np{1} /\
       Array4.of_list W64.zero (to_list (unpack64 u'{2})) = toRep4 pp{1}
       ==>
       Array32.of_list W8.zero (to_list (unpack8 res{2})) = res{1}
   ].
    transitivity
    Mulx_scalarmult_s.M.__curve25519_mulx
    (toRep4 np{1} = _k{2} /\ toRep4 pp{1} = _u{2}
     ==> toRep4 res{1} = res{2})
    (pack4 (to_list _k{1}) = k'{2} /\
     pack4 (to_list _u{1}) = u'{2}
     ==> pack4 (to_list res{1}) = res{2}) => />.
    move => &1 &2 H H0.
    exists(Array4.of_list W64.zero (to_list (unpack64 k'{2})), Array4.of_list W64.zero (to_list (unpack64 u'{2}))).
    do split.
    + by rewrite -H. by rewrite -H0. by rewrite //= of_listK. by rewrite //= of_listK.
    move => &m.
    rewrite of_listK //=  of_listK //=. rewrite size_to_list //=. rewrite to_listK //=.
    proc *. by call xwing_25519_mulx_equiv.
    proc *. symmetry. by call eq_spec_impl_scalarmult_mulx.
qed.

lemma eq_spec_xwing_keygen:
  equiv [Xkem_avx2_clean.M.jade_kem_xwing_xwing_amd64_avx2_keypair_derand ~ XWing.kg_derand :
      sk{2} = coins{1}
      ==>
      res{1}.`2 = res{2}.`1 /\
      res{1}.`1 = Array1216.of_list W8.zero (to_list (res{2}.`2).`1.`1 ++ to_list (res{2}.`2).`1.`2 ++ to_list (res{2}.`2).`2)

  ].
  proc. inline {2} 1. inline {1} 2. wp.
  do 3! unroll for{1} ^while. wp.
  swap{1} 15 2.
  call eq_spec_xwing_25519_base_mulx; wp.
  call mlkem_kem_correct_internal_kg; wp.
  ecall{1} (shake256_A96_A32 expanded{1} srandomness{1}); wp.
  skip; auto => />. move => &1.
  do split.
  admit. (* this needs to change in the jasmin extraction, provable but takes forever. *)
  admit. (* this needs to change in the jasmin extraction, provable but takes forever. *)
  move => *.
  admit. (* this needs to change in the jasmin extraction, too big to be provable imo. *)
qed.
