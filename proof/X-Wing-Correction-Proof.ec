require import AllCore IntDiv CoreMap List Distr IntDiv StdOrder.

from Jasmin require import JModel_x86 JWord JUtils.

import SLH64 StdOrder.IntOrder.
require import Jkem_avx2_clean XWing_Spec XWing_Helper_Functions CorrectnessProof_Mulx Mulx_scalarmult_s Jkem_avx2_stack FIPS202_SHA3 MLKEM Curve25519_Procedures.
require import Array4 Array6 Array8 Array32 Array64 Array96 Array140 Array152 Array1088 Array1120 Array1184 Array1216 Array2400.
require import WArray4 WArray6 WArray32 WArray64 WArray96 WArray1088 WArray1120 WArray1184 WArray1216 WArray2400.

op SHA3_256_A128_A6 : W8.t Array32.t -> W8.t Array32.t -> W8.t Array32.t -> W8.t Array32.t -> W8.t Array32.t -> W8.t Array32.t.
op SHAKE256_A96_A32 : W8.t Array96.t -> W8.t Array32.t -> W8.t Array96.t.


axiom sha3_256_A128__A6 ss ss_mlkem ss_x25519 ct_25519 pk_25519 :
   phoare [Jkem_avx2_clean.M._sha3_256_A128__A6 :
               arg = (ss, ss_mlkem, ss_x25519, ct_25519, pk_25519) ==>
               res = SHA3_256_A128_A6 ss ss_mlkem ss_x25519 ct_25519 pk_25519] = 1%r.

axiom shake256_A96_A32 out inp :
   phoare [Jkem_avx2_clean.M._shake256_A96__A32 :
               arg = (out, inp) ==>
               res = SHAKE256_A96_A32 out inp] = 1%r.

abbrev toRep4 (x: W8.t Array32.t) = Array4.init (fun (i : int) => get64 (WArray32.init8 (fun (i0 : int) => x.[i0])) i).
abbrev toRep32 (x: W64.t Array4.t) = Array32.init (fun (i : int) => get8 (WArray32.init64 (fun (i0 : int) => x.[i0])) i).

lemma xwing_25519_base_mulx_equiv :
   equiv [Jkem_avx2_clean.M.xwing_x25519_base ~ Mulx_scalarmult_s.M.__curve25519_mulx_base :
       _k{2} = toRep4 np{1}
       ==>
       res{1} = toRep32 res{2}].
    proc.
    inline{1} 4.
    seq 7 3 : (={u, r, k, _k}). wp. auto => />.
    seq 4 3 : (={u, k, _k, r} /\ q{1} = r{2}). sim.
    wp; skip => />.
qed.

lemma xwing_25519_mulx_equiv :
   equiv [Jkem_avx2_clean.M.xwing_x25519 ~ Mulx_scalarmult_s.M.__curve25519_mulx :
       _k{2} = toRep4 np{1}  /\
       _u{2} = toRep4 pp{1}
       ==>
       res{1} = toRep32 res{2}].
    proc.
    inline{1} 6.
    wp; sp.
    sim :  (={k, u, r}).
qed.

lemma eq_spec_xwing_25519_base_mulx :
   equiv [Jkem_avx2_clean.M.xwing_x25519_base ~ CurveProcedures.scalarmult_base :
       Array4.of_list W64.zero (to_list (unpack64 k'{2})) = toRep4 np{1}
       ==>
       pack32 (to_list res{1}) = res{2}
   ].
    transitivity
    Mulx_scalarmult_s.M.__curve25519_mulx_base
    (toRep4 np{1} = _k{2} ==> res{1} = toRep32 res{2})
    (pack4 (to_list _k{1}) = k'{2} ==> pack4 (to_list res{1}) = res{2}) => />.
    move => &1 &2 H.
    exists(Array4.of_list W64.zero (to_list (unpack64 k'{2}))).
    do split.
    + by rewrite -H. by rewrite of_listK.
    move => &m.
    rewrite of_listE /of_list pack32E pack4E /get8 /init64 !/to_list /(\bits8) /mkseq -iotaredE => />.
    congr. apply fun_ext => i. rewrite !initE => />.
    + case( 0 <= i %/ 8 && i %/ 8 < 32) => C. smt(W8.initiE). by rewrite ifF 1:/#.
   proc *. by call xwing_25519_base_mulx_equiv.
   proc *. symmetry. by call eq_spec_impl_scalarmult_base_mulx.
qed.

lemma eq_spec_xwing_25519_mulx :
   equiv [Jkem_avx2_clean.M.xwing_x25519 ~ CurveProcedures.scalarmult :
       Array4.of_list W64.zero (to_list (unpack64 k'{2})) = toRep4 np{1} /\
       Array4.of_list W64.zero (to_list (unpack64 u'{2})) = toRep4 pp{1}
       ==>
       pack32 (to_list res{1}) = res{2}
   ].
    transitivity
    Mulx_scalarmult_s.M.__curve25519_mulx
    (toRep4 np{1} = _k{2} /\ toRep4 pp{1} = _u{2}
     ==> res{1} = toRep32 res{2})
    (pack4 (to_list _k{1}) = k'{2} /\
     pack4 (to_list _u{1}) = u'{2}
     ==> pack4 (to_list res{1}) = res{2}) => />.
    move => &1 &2 H H0.
    exists(Array4.of_list W64.zero (to_list (unpack64 k'{2})), Array4.of_list W64.zero (to_list (unpack64 u'{2}))).
    do split.
    + by rewrite -H. by rewrite -H0. by rewrite //= of_listK. by rewrite //= of_listK.
    move => &m.
    rewrite of_listE /of_list pack32E pack4E /get8 /init64 /to_list /(\bits8) /mkseq -iotaredE => />.
    congr. apply fun_ext => i. rewrite !initE => />.
    + case( 0 <= i %/ 8 && i %/ 8 < 32) => C. smt(W8.initiE). by rewrite ifF 1:/#.

   proc *. by call xwing_25519_mulx_equiv.
   proc *. symmetry. by call eq_spec_impl_scalarmult_mulx.
qed.
