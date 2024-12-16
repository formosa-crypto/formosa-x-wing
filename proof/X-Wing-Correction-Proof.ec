require import AllCore IntDiv CoreMap List Distr IntDiv StdOrder.

from Jasmin require import JModel_x86 JModel JWord JUtils.



import SLH64 StdOrder.IntOrder.
require import Xkem_avx2_clean  XWing_Spec XWing_Helper_Functions CorrectnessProof_Mulx Mulx_scalarmult_s Jkem_avx2_stack FIPS202_SHA3 Curve25519_Procedures MLKEM MLKEM_KEM_avx2_stack Symmetric.
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
  equiv [Xkem_avx2_clean.M._crypto_xkem_keypair_derand_jazz ~ XWing.kg_derand :
      sk{2} = randomness{1} (** in the rfc, the derand version uses sk to denote the coins **)
      ==>
         res{2}.`1 = Array32.init(fun i => res{1}.`2.[i])  /\
         res{2}.`2.`1.`1 = Array1152.init(fun i => res{1}.`1.[i]) /\
         res{2}.`2.`1.`2 = Array32.init(fun i => res{1}.`1.[i+1152]) /\
         res{2}.`2.`2 = Array32.init(fun i => res{1}.`1.[i+1184])].
proof.
  proc => />.
  proc rewrite {1} 8 (copy32). inline {2} 1. auto => />.
  seq 9 2 : (#pre /\ expanded{1} = SHAKE256_32_96 randomness{1}
                  /\ randomness{1} = srandomness{1}
                  /\ ={expanded}
                  /\ srandomness{1} = sk0{2}
                  /\ srandomness{1} = sk{2}).
  + ecall {1} (shake256_A96_A32 expanded{1} srandomness{1}); wp; skip => />.

  swap{1} 2 1. swap{2} 3 -2.
  seq 1 1 : (#pre /\ coins3{2} = expanded_x25519{1}
                  /\ coins3{2} = Array32.init(fun (i : int) => expanded{1}.[i + 64])
                  /\ coins3{2} = Array32.init(fun (i : int) => expanded{2}.[i + 64])).
  + auto => />. move => &1. smt(). auto => />.

  seq 1 2 : (#pre /\ coins1{2} = Array32.init (fun (i : int ) => expanded_mlkem{1}.[i])
                  /\ coins2{2} = Array32.init (fun (i : int ) => expanded_mlkem{1}.[32 + i])
                  /\ coins1{2} = Array32.init (fun (i : int ) => expanded{1}.[i])
                  /\ coins2{2} = Array32.init (fun (i : int ) => expanded{1}.[32 + i])
                  /\ coins1{2} = Array32.init (fun (i : int ) => expanded{2}.[i])
                  /\ coins2{2} = Array32.init (fun (i : int ) => expanded{2}.[32+i])).
  + auto => />. move => &1. do split.  rewrite tP => i ib. rewrite !initiE 1..5:/# //=.
  + rewrite tP => i ib. rewrite !initiE 1..2:/# //= !initiE 1..3:/# //=.

  auto => />.
  seq 0 1 : (#pre /\ expanded_x25519{1} = sk_X0{2}
                  /\ sk_X0{2} = coins3{2}).
  + auto => />.

  seq 1 1 : (#pre /\ pack32 (to_list pk_x25519{1}) = pk_X_256{2}).
  + call eq_spec_xwing_25519_base_mulx. auto => />.

  seq 0 1 : (#pre /\ pk_x25519{1} = pk_X0{2}
                  /\ pk_x25519{1} = Array32.of_list W8.zero (W32u8.to_list pk_X_256{2})). auto => />.
  + move => &1 &2 [#] *. rewrite !tP. do split.
  + move => i ib. rewrite !/to_list !/mkseq -!iotaredE => />. rewrite !/of_list initiE 1:/# //=. smt().
  + move => i ib. rewrite !/to_list !/mkseq -!iotaredE => />. rewrite !/of_list initiE 1:/# //=. smt().

  seq 1 1 : (#pre /\ pk_M0{2}.`1 = (init (fun (i : int) =>  pk_mlkem{1}.[i]))%Array1152
                  /\ pk_M0{2}.`2 = (init (fun (i : int) =>  pk_mlkem{1}.[i + 1152]))%Array32
                  /\ let (t,rho) = pk_M0{2} in
                     sk_M0{2}.`1 = Array1152.init(fun i => sk_mlkem{1}.[i])
                  /\ sk_M0{2}.`2.`1 = Array1152.init(fun i => sk_mlkem{1}.[i+1152])
                  /\ sk_M0{2}.`2.`2 = Array32.init(fun i => sk_mlkem{1}.[i+1152+1152])
                  /\ sk_M0{2}.`3 = Array32.init(fun i => sk_mlkem{1}.[i+1152+1152 + 32])
                  /\ sk_M0{2}.`4 = Array32.init(fun i => sk_mlkem{1}.[i+1152+1152 + 32 + 32])
                  /\ t = Array1152.init(fun i => pk_mlkem{1}.[i])
                  /\ rho = Array32.init(fun i => pk_mlkem{1}.[i+1152])).
  + call mlkem_kem_correct_kg. auto => />. smt(). auto => />.

  seq 9 0 : (#pre /\ sk0{2} = (init ("_.[_]" skp{1}))%Array32
                  /\ pk_M0{2}.`1 = (init ("_.[_]" pkp{1}))%Array1152
                  /\ pk_M0{2}.`2 = (init (fun (i0 : int) => pkp{1}.[i0 + 1152]))%Array32
                  /\ pk_X0{2} = (init (fun (i0 : int) => pkp{1}.[i0 + 1184]))%Array32).

  seq 3 0 : (#pre /\ pk_M0{2}.`1 = (init (fun (i : int) =>  pk_mlkem{1}.[i]))%Array1152
                  /\ pk_M0{2}.`2 = (init (fun (i : int) =>  pk_mlkem{1}.[i + 1152]))%Array32
                  /\ pk_M0{2}.`1 = (init (fun (i : int) =>  pkp{1}.[i]))%Array1152
                  /\ pk_M0{2}.`2 = (init (fun (i : int) =>  pkp{1}.[i + 1152]))%Array32).

  + while{1} ( #pre /\ aux{1} = 148
                   /\ 0 <= i{1} <= aux{1}
                   /\ pk_X0{2} = pk_x25519{1}
                   /\ pk_M0{2}.`1 = (init (fun (i : int) =>  pk_mlkem{1}.[i]))%Array1152
                   /\ pk_M0{2}.`2 = (init (fun (i : int) =>  pk_mlkem{1}.[i + 1152]))%Array32
                   /\ (forall k, 0<=k<min (8 * i{1}) 1184 => pkp{1}.[k] = pk_mlkem{1}.[k])
                   /\ (forall k, 0<=k<min (8 * i{1}) 1152 => pkp{1}.[k] = pk_M0{2}.`1.[k])
                   /\ (forall k, 1152<=k<min (8 * i{1}) 1184 => pkp{1}.[k] = pk_M0{2}.`2.[k-1152]))
              (148 - i{1}).
   + auto => />. move => &hr Z. rewrite !tP. move => H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9. do split.
   + smt(). smt(). move => i ib *. rewrite !initE.
   + case(0 <= i && i < 1184) => *. rewrite ifT 1:/#.
   + rewrite get8_set64_directE 1,2:/#. case (8 * i{!hr} <= i && i < 8 * i{!hr} + 8) => *.
   + rewrite get64E /get8 /init8 !pack8bE 1:/# !initiE 1:/# //= !initiE 1:/# /#.
   + rewrite /get8 /init8 !initiE 1:/#. smt(). smt().
   + move => i ib *.
   + case(0 <= i && i < 1152) => *. rewrite H1. smt().
   + rewrite !initiE 1,2:/#.
   + rewrite get8_set64_directE 1,2:/#. case (8 * i{!hr} <= i && i < 8 * i{!hr} + 8) => *.
   + rewrite get64E /get8 /init8 !pack8bE 1:/# !initiE 1:/# //= !initiE 1:/# /#.
   + rewrite /get8 /init8 !initiE 1:/#. smt(). rewrite !initiE 1,2:/#.
   + move => i ib *.
   + rewrite !initiE 1:/#.
   + rewrite get8_set64_directE 1,2:/#. case (8 * i{!hr} <= i && i < 8 * i{!hr} + 8) => *.
   + rewrite get64E /get8 /init8 !pack8bE 1:/# !initiE 1:/# //= !initiE 1:/# H2 1:/# !initiE 1:/# //= /#.
   + rewrite /get8 /init8 !initiE 1:/#. smt(). smt().

   + wp. auto => />.
   + move => &1 &2 [#] H H0 H1 H2 H3 H4. auto => />. do split.
   + smt(). smt(). smt(). move => ??. do split.
   + move => H5 H6 H7 H8 H9 H10. smt(). move => H11 H12 H13 H14 H15 H16. rewrite tP. do split.
   + move => H17 H18. rewrite -H15 1:/#. smt(Array1152.initiE).
   + rewrite H3. rewrite tP => i ib. rewrite !initiE 1,2:/# //= -H14 1,2:/#.

   seq 3 0 : (#pre /\ pk_X0{2} = (init (fun (i0 : int) => pkp{1}.[i0 + 1184]))%Array32
                   /\ pk_x25519{1} = (init (fun (i0 : int) => pkp{1}.[i0 + 1184]))%Array32
                   /\ pk_X0{2} = pk_x25519{1}).
   wp.
   while{1} (#pre /\ aux{1} = 4
                  /\ 0 <= i{1} <= aux{1}
                  /\ pk_X0{2} = pk_x25519{1}
                  /\ (forall k, 0<=k<min (8 * i{1}) 32 => pkp{1}.[k+1184] = pk_x25519{1}.[k])
                  /\ (forall k, 0<=k<min (8 * i{1}) 32 => pkp{1}.[k+1184] = pk_X0{2}.[k])
                  /\ (forall k, 1184<=k<min (8 * i{1}) 1216 => pkp{1}.[k] = pk_x25519{1}.[k-1216])
                  /\ (forall k, 1184<=k<min (8 * i{1}) 1216 => pkp{1}.[k] = pk_X0{2}.[k-1216]))
              (4 - i{1}).

   + auto => />. move => &hr Z. rewrite !tP. move => H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10. do split.
   + move => i ib. rewrite !initiE 1,2:/# /=.
   + rewrite get8_set64_directE 1,2:/# ifF 1:/#.
   + rewrite /get8 /init8 !initiE 1:/# H4 1:/#. smt(Array1152.initiE).
   + move => i ib. rewrite !initiE 1:/# /= !initiE 1:/#.
   + rewrite get8_set64_directE 1,2:/# ifF 1:/#.
   + rewrite /get8 /init8 !initiE 1:/# H5 1:/#. smt(Array32.initiE).
   smt(). smt().
   + move => k0 i ib. rewrite !initiE 1:/# /=.
   + rewrite get8_set64_directE 1,2:/#.
   + case (8 * (148 + i{!hr}) <= k0 + 1184 && k0 + 1184 < 8 * (148 + i{!hr}) + 8) => *.
   + rewrite get64E /get8 /init8 !pack8bE 1:/# !initiE 1:/# //= !initiE 1:/# /# //=.
   + rewrite /get8 /init8 !initiE 1:/# H8 1:/# /#.
   + move => k0 i ib. rewrite !initiE 1:/# /=.
   + rewrite get8_set64_directE 1,2:/#.
   + case (8 * (148 + i{!hr}) <= k0 + 1184 && k0 + 1184 < 8 * (148 + i{!hr}) + 8) => *.
   + rewrite get64E /get8 /init8 !pack8bE 1:/# !initiE 1:/# //= !initiE 1:/# /# //=.
   + rewrite /get8 /init8 !initiE 1:/# H8 1:/# /#.
   + move => k0 i ib. rewrite !initiE 1:/# /=.
   + rewrite get8_set64_directE 1,2:/#. rewrite ifF 1:/#.
   + rewrite /get8 /init8 !initiE 1:/# H9 1:/# /#.
   + move => k0 i ib. rewrite !initiE 1:/# /=.
   + rewrite get8_set64_directE 1,2:/#. rewrite ifF 1:/#.
   + rewrite /get8 /init8 !initiE 1:/# H9 1:/# /#. smt().

   + wp. auto => />. rewrite !tP. move => &1 &2 [#] H H0 H1 H2 H3 H4 H5 H6. do split.
   + smt(). smt(). smt(). smt().
   + move => H7 H8. do split. move => H9 H10 H11 H12 H13 H14. smt().
   + move => H15 H16 H17 H18 H19 H20 H21. rewrite tP. do split.
   + move => i ib. rewrite !initiE 1:/# //=. smt().
   + move => i ib. rewrite !initiE 1:/# //=. smt().

   seq 3 0 : (#pre /\ sk{2} = skp{1} /\ sk0{2} = skp{1} /\ skp{1} = srandomness{1}).
   while{1} (#pre /\ aux{1} = 4
                  /\ 0 <= i{1} <= aux{1}
                  /\ sk{2} = srandomness{1}
                  /\ sk0{2} = srandomness{1}
                  /\ (forall k, 0<=k<min (8 * i{1}) 32 => skp{1}.[k] = sk{2}.[k])
                  /\ (forall k, 0<=k<min (8 * i{1}) 32 => skp{1}.[k] = sk0{2}.[k]))
              (4 - i{1}).
   + auto => />. move => &hr Z. rewrite !tP. move => H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9. do split.
   + smt(). smt(). move => i ib *. rewrite !initiE 1:/#.
   + rewrite get8_set64_directE 1,2:/#. case(8 * i{!hr} <= i && i < 8 * i{!hr} + 8) => *.
   + rewrite get64E /get8 /init8 !pack8bE 1:/# !initiE 1:/# //= !initiE 1:/# /# //=.
   + rewrite /get8 /init8 !initiE 1:/# H8 1:/# /#.
   + move => i ib *. rewrite !initiE 1:/#.
   + rewrite get8_set64_directE 1,2:/#. case(8 * i{!hr} <= i && i < 8 * i{!hr} + 8) => *.
   + rewrite get64E /get8 /init8 !pack8bE 1:/# !initiE 1:/# //= !initiE 1:/# /# //=.
   + rewrite /get8 /init8 !initiE 1:/# H8 1:/# /#. smt().
   wp. auto => />.
   move => &1 &2 [#] *. do split. smt(). smt(). move => I I0. do split.
   smt(). move => [#] H H0 H1 H2. do split.
   rewrite tP => i ib. rewrite H2. smt(). smt().
   rewrite tP => i ib. rewrite H2. smt(). smt().
   rewrite tP => i ib. rewrite H2. smt(). smt().
   wp. auto => />. rewrite !tP.
   move => &1 &2 H H0 H1 H2 H3 H4 H5 H6. move => i ib. rewrite initiE 1,2:/#.
   wp. auto => />.
qed.
