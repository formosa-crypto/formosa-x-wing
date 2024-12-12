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
      k'{2} =  pack32 (to_list np{1})
       ==>
      res{2} = pack32 (to_list res{1})
   ].
    transitivity
    Mulx_scalarmult_s.M.__curve25519_mulx_base
    (toRep4 np{1} = _k{2} ==> toRep4 res{1} =  res{2})
    (pack4 (to_list _k{1}) = k'{2} ==> pack4 (to_list res{1}) = res{2}) => />.
    move => &1.
    exists(toRep4 np{1}).
    do split.
    rewrite of_listK. rewrite size_to_list //=. rewrite to_listK. smt().
    move => &1. rewrite of_listK. rewrite size_to_list //=. smt().
    proc *. by call xwing_25519_base_mulx_equiv.
    proc *. symmetry. by call eq_spec_impl_scalarmult_base_mulx.
qed.

lemma eq_spec_xwing_25519_mulx :
   equiv [Xkem_avx2_clean.M.xwing_x25519 ~ CurveProcedures.scalarmult :
       k'{2} = pack32 (to_list np{1}) /\
       u'{2} = pack32 (to_list pp{1})
       ==>
       res{2} = pack32 (to_list res{1})
   ].
    transitivity
    Mulx_scalarmult_s.M.__curve25519_mulx
    (toRep4 np{1} = _k{2} /\ toRep4 pp{1} = _u{2}
     ==> toRep4 res{1} = res{2})
    (pack4 (to_list _k{1}) = k'{2} /\
     pack4 (to_list _u{1}) = u'{2}
     ==> pack4 (to_list res{1}) = res{2}) => />.
    move => &1 &2 H H0.
    exists(toRep4 np{1}, toRep4 pp{1}).
    do split.
    + rewrite -H. rewrite //= of_listK //=.
    + rewrite -H0. rewrite //= of_listK //=.
    move => &1.
    rewrite of_listK //=  of_listK //=.
    proc *. by call xwing_25519_mulx_equiv.
    proc *. symmetry. by call eq_spec_impl_scalarmult_mulx.
qed.

lemma eq_spec_xwing_keygen:
  equiv [Xkem_avx2_clean.M.jade_kem_xwing_xwing_amd64_avx2_keypair_derand ~ XWing.kg_derand :
      sk{2} = coins{1}
      ==>
      res{1}.`2 = res{2}.`1 /\
      let pk = res{2}.`2 in
            let (pk_mlkem, pk_x25519) = pk in
                let (t, rho) = pk_mlkem in
                    t = (init (fun (i : int) => res{1}.`1.[i]))%Array1152 /\
                    rho = (init (fun (i : int) => res{1}.`1.[i + 1152]))%Array32 /\
                pk_x25519 = (init (fun (i : int) => res{1}.`1.[i + 1184]))%Array32].
proof.
  proc => />. smt().
  inline {2} 1. inline {1} 2. wp.
  proc rewrite {1} 12 (copy32).
  while {1} (aux{1} = 4 /\
      skp{1} = srandomness{1} /\
      skp{1} = Array32.init (fun i => sk_X0{2}.[i]) /\
      Array1152.init (fun i => pkp{1}.[i]) = pk_M0{2}.`1 /\
      Array32.init (fun i => pkp{1}.[i + 1152]) = pk_M0{2}.`2 /\
      Array32.init (fun i => pkp{1}.[i + 1184]) = (of_list W8.zero ((to_list pk_X_256{2}))%W32u8)%Array32 /\
       0 <= i{1} <= 4)
          (4 - i{1}).
   auto => />. move => &hr H H0 H1 H2 H3 H4.
   do split.
   + rewrite tP => i ib. rewrite initiE 1:/#.
   + rewrite get8_set64_directE /get8 1,2:/# //=.
   + case:  (8 * i{!hr} <= i && i < 8 * i{!hr} + 8) => *.
   + rewrite WArray32.get64E pack8bE 1:/# initiE 1:/# /= initiE 1:/# //=.
   + rewrite /get8 initiE 1:/# initiE 1,2:/#. rewrite initiE 1:/# //=.
   + rewrite tP => i ib. rewrite initiE 1:/#.
   + rewrite get8_set64_directE /get8 1,2:/# //=.
   case:  (8 * i{!hr} <= i && i < 8 * i{!hr} + 8) => *.
   + rewrite WArray32.get64E pack8bE 1:/# initiE 1:/# /= initiE 1:/# //=.
   + rewrite /get8 initiE 1:/# initiE 1,2:/#. rewrite initiE 1,2:/# //=.
   + smt(). smt(). smt().
   wp.
   while {1} (aux{1} = 4 /\
      Array1152.init (fun i => pkp{1}.[i]) = pk_M0{2}.`1 /\
      Array32.init (fun i => pkp{1}.[i + 1152]) = pk_M0{2}.`2 /\
      Array32.init (fun i => pkp{1}.[i + 1184]) = pk_x25519{1} /\
      pk_x25519{1} = (of_list W8.zero ((to_list pk_X_256{2}))%W32u8)%Array32 /\
      0 <= i{1} <= 4)
          (4 - i{1}).
   auto => />. move => &hr H H0 H1 H2 H3 H4.
   do split.
   rewrite -H. congr. congr.
   + rewrite tP => i ib. rewrite initiE 1:/#.
   + rewrite get8_set64_directE /get8 1,2:/# //=.
   + case:  (8 * (148 + i{!hr}) <= i && i < 8 * (148 + i{!hr}) + 8) => *.
   + rewrite WArray32.get64E pack8bE 1:/# initiE 1:/# /= initiE 1:/# //=.
   + rewrite !initiE 1,2:/# //=. smt(WArray1216.initiE).

   + rewrite -H0. rewrite tP => i ib.
   + rewrite!initiE 1:/# //= initiE 1:/#. rewrite  get8_set64_directE 1,2:/#.
   + rewrite ifF 1:/#. rewrite /get8 /init8. smt(WArray1216.initiE).

   + rewrite tP => i ib. rewrite !initiE 1:/# //=.
   + rewrite !initiE 1:/# //=.
   + rewrite get8_set64_directE /get8 1,2:/# //=.
   + case: (8 * (148 + i{!hr}) <= i + 1184 && i + 1184 < 8 * (148 + i{!hr}) + 8) => *.
   + rewrite WArray32.get64E pack8bE 1:/# initiE 1:/# /= initiE 1:/# //= initiE 1:/# //=.
   + smt(). smt(WArray1216.initiE). smt(). smt(). smt().

  wp.
  while {1} (aux{1} = 4 /\
      Array1152.init (fun i => pkp{1}.[i]) = pk_M0{2}.`1 /\
      Array32.init (fun i => pkp{1}.[i + 1152]) = pk_M0{2}.`2 /\
      Array32.init (fun i => pkp{1}.[i + 1184]) = pk_x25519{1} /\
      Array1152.init (fun i => pk_mlkem{1}.[i]) = pk_M0{2}.`1 /\
      Array32.init (fun i => pk_mlkem{1}.[i]) = pk_M0{2}.`2 /\
      Array1184.init (fun i => pkp{1}.[i]) = pk_mlkem{1} /\
      0 <= i{1} <= 4)
          (4 - i{1}).
   auto => />. move => &hr H H0 H1 H2 H3 H4 H5.
   do split.
   rewrite -H. congr. congr.
   + rewrite tP => i ib. rewrite initiE 1:/#.
   + rewrite get8_set64_directE /get8 1,2:/# //=.
   + case:  (8 * i{!hr} <= i && i < 8 * i{!hr} + 8) => *.
   + rewrite get64E pack8bE 1:/# initiE 1:/# /= initiE 1:/# //= initiE 1,2:/# //= .
   + smt(WArray1216.initiE).

   + rewrite -H0. rewrite tP => i ib.
   + rewrite!initiE 1:/# //= initiE 1:/#. rewrite  get8_set64_directE 1,2:/#.
   + rewrite ifF 1:/#. rewrite /get8 /init8. smt(WArray1216.initiE).

   + rewrite tP => i ib. rewrite !initiE 1:/# //=.
   + rewrite !initiE 1:/# //=.
   + rewrite get8_set64_directE /get8 1,2:/# //=.
   case: (8 * i{!hr} <= i + 1184 && i + 1184 < 8 * i{!hr} + 8) => *.
   + rewrite get64E pack8bE 1:/# initiE 1:/# /= initiE 1:/# //= initiE 1:/# //=.
   + smt(). smt(WArray1216.initiE).

   + rewrite tP => i ib. rewrite initiE 1:/#. rewrite initE.
   case (0 <= i && i < 1216) => *.
   + rewrite get8_set64_directE /get8 1,2:/# //=.
   case: (8 * i{!hr} <= i && i  < 8 * i{!hr} + 8) => *.
   + rewrite get64E pack8bE 1:/# initiE 1:/# /= initiE 1:/# //= initiE 1:/# //= initiE 1:/# //=.
   + smt(). rewrite /init8. rewrite initiE 1:/# initiE 1:/# //=.
   + rewrite initiE. smt(). smt(). smt(). smt(). smt().

  wp.

  call mlkem_kem_correct_kg; wp.
  call eq_spec_xwing_25519_base_mulx; wp.
  ecall{1} (shake256_A96_A32 expanded{1} srandomness{1}); wp.
  skip => />. move => &1. do split.
  + rewrite tP => i ib. rewrite !initiE 1..6:/# //=.
  + rewrite tP => i ib. rewrite !initiE 1..2:/# //= !initiE 1..4:/#.
  move => H H0 H1 H2.
qed.
