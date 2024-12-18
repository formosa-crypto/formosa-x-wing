require import AllCore IntDiv CoreMap List Distr IntDiv StdOrder.

from Jasmin require import JModel_x86 JModel JWord JUtils.

import SLH64 StdOrder.IntOrder.
require import Xkem_avx2 Xkem_avx2_clean XWing_Spec XWing_Helper_Functions CorrectnessProof_Mulx Mulx_scalarmult_s Jkem_avx2_stack FIPS202_SHA3 Curve25519_Procedures MLKEM InnerPKE MLKEM_KEM_avx2_stack Symmetric.
require import Array4 Array6 Array8 Array32 Array64 Array96 Array140 Array152 Array128 Array960 Array1088 Array1120 Array1184 Array1216 Array2400 Array1152.
require import WArray4 WArray6 WArray32 WArray64 WArray96 WArray1088 WArray1120 WArray1184 WArray1216 WArray2400.

axiom shake256_A96_A32 out inp :
  phoare [Xkem_avx2_clean.M._shake256_A96__A32 :
               arg = (out, inp) ==>
               res = SHAKE256_32_96 inp] = 1%r.

axiom sha3_256_A128__A6 ss ss_mlkem ss_x25519 ct_25519 pk_25519 :
   phoare [Xkem_avx2_clean.M._sha3_256_A128__A6 :
               arg = (ss, ss_mlkem, ss_x25519, ct_25519, pk_25519) ==>
               res = SHA3_256_134_32 (ss_mlkem, ss_x25519, ct_25519, pk_25519, xwing_label)] = 1%r.

lemma copy1120 (a : W8.t Array1120.t) :
  Array1120.init (fun (i : int)  =>  WArray1120.get8 (WArray1120.init64
                 (fun (i0 : int) =>  copy_64 (Array140.init
                 (fun (i1 : int) =>  WArray1120.get64 (WArray1120.init8
                 (fun (i2 : int) =>  a.[i2]))  i1)).[i0])) i) = a.
proof.
  rewrite tP => k kb.
  rewrite initiE 1:/# /= /get8.
  rewrite initiE 1:/# /= /copy_64.
  rewrite initiE 1:/# /= /get64_direct.
  rewrite W8u8.pack8bE 1:/# /=.
  rewrite initiE 1:/# /=.
  rewrite initiE /#.
qed.

lemma copy1216 (a : W8.t Array1216.t) :
  Array1216.init (fun (i : int)  =>  WArray1216.get8 (WArray1216.init64
                 (fun (i0 : int) =>  copy_64 (Array152.init
                 (fun (i1 : int) =>  WArray1216.get64 (WArray1216.init8
                 (fun (i2 : int) =>  a.[i2]))  i1)).[i0])) i) = a.
proof.
  rewrite tP => k kb.
  rewrite initiE 1:/# /= /get8.
  rewrite initiE 1:/# /= /copy_64.
  rewrite initiE 1:/# /= /get64_direct.
  rewrite W8u8.pack8bE 1:/# /=.
  rewrite initiE 1:/# /=.
  rewrite initiE /#.
qed.

abbrev toRep4 (x: W8.t Array32.t) = Array4.of_list W64.zero (to_list (unpack64 (pack32 (to_list x)))).

equiv aux_buflen_dumpstate1_xkem :
Jkem_avx2_stack.M.aBUFLEN____dumpstate_array_avx2 ~ Xkem_avx2.M.aBUFLEN____dumpstate_array_avx2 : ={buf, offset, lEN, st}  ==> ={res}.
proc => /=.
  sp;if;1: by auto.
  seq 1 1 : (={buf, offset, lEN, st,buf, dELTA,_0}); 1: by sim.
  sp;seq 1 1 : (={buf, offset, lEN, st,buf, dELTA,_0}); 1: by sim.
  sp;if;1: by auto.
  sp;seq 1 1 : (={t,t128_0,t128_1,buf, offset, lEN, st,buf, dELTA,_0}); 1: by sim.
  sp;if;1: by auto.
  sp;seq 1 1 : (={t,t128_0,t128_1,buf, offset, lEN, st,buf, dELTA,_0,t256_0,t256_1,t256_2,t256_3}); by sim.
  by sim.
  sp;if;1: by auto.
  sp;seq 1 1 : (={t,t128_0,t128_1,buf, offset, lEN, st,buf, dELTA,_0,t256_0,t256_1,t256_2,t256_3}); by sim.
  by sim.
  seq 1 1 : (={buf, offset, lEN, st,buf, dELTA}); 1: by sim.
  sp;seq 1 1 : (={buf, offset, lEN, st,buf, dELTA}); 1: by sim.
  sp;if;1: by auto.
  sp;seq 1 1 : (={t,t128_0,t128_1,buf, offset, lEN, st,buf, dELTA}); 1: by sim.
  sp;if;1: by auto.
  sp;seq 1 1 : (={t,t128_0,t128_1,buf, offset, lEN, st,buf, dELTA,t256_0,t256_1,t256_2,t256_3}); by sim.
  by sim.
  sp;if;1: by auto.
  sp;seq 1 1 : (={t,t128_0,t128_1,buf, offset, lEN, st,buf, dELTA,t256_0,t256_1,t256_2,t256_3}); by sim.
  by sim.
qed.


equiv aux_dumpstate_xkem :
  Jkem_avx2_stack.M.a64____dumpstate_array_avx2 ~ Xkem_avx2.M.a64____dumpstate_array_avx2 :
   ={buf, offset, lEN, st} ==> ={res}.
proc => /=.
  sp;if;1: by auto.
  seq 1 1 : (={buf, offset, lEN, st,buf, dELTA,_0}); 1: by sim.
  sp;seq 1 1 : (={buf, offset, lEN, st,buf, dELTA,_0}); 1: by sim.
  sp;if;1: by auto.
  sp;seq 1 1 : (={t,t128_0,t128_1,buf, offset, lEN, st,buf, dELTA,_0}); 1: by sim.
  sp;if;1: by auto.
  sp;seq 1 1 : (={t,t128_0,t128_1,buf, offset, lEN, st,buf, dELTA,_0,t256_0,t256_1,t256_2,t256_3}); by sim.
  by sim.
  sp;if;1: by auto.
  sp;seq 1 1 : (={t,t128_0,t128_1,buf, offset, lEN, st,buf, dELTA,_0,t256_0,t256_1,t256_2,t256_3}); by sim.
  by sim.
  seq 1 1 : (={buf, offset, lEN, st,buf, dELTA}); 1: by sim.
  sp;seq 1 1 : (={buf, offset, lEN, st,buf, dELTA}); 1: by sim.
  sp;if;1: by auto.
  sp;seq 1 1 : (={t,t128_0,t128_1,buf, offset, lEN, st,buf, dELTA}); 1: by sim.
  sp;if;1: by auto.
  sp;seq 1 1 : (={t,t128_0,t128_1,buf, offset, lEN, st,buf, dELTA,t256_0,t256_1,t256_2,t256_3}); by sim.
  by sim.
  sp;if;1: by auto.
  sp;seq 1 1 : (={t,t128_0,t128_1,buf, offset, lEN, st,buf, dELTA,t256_0,t256_1,t256_2,t256_3}); by sim.
  by sim.
qed.

equiv aux_dumpstate32_xkem :
  Jkem_avx2_stack.M.a32____dumpstate_array_avx2 ~ Xkem_avx2.M.a32____dumpstate_array_avx2 :
   ={buf, offset, lEN, st} ==> ={res}.
proc => /=.
  sp;if;1: by auto.
  seq 1 1 : (={buf, offset, lEN, st,buf, dELTA,_0}); 1: by sim.
  sp;seq 1 1 : (={buf, offset, lEN, st,buf, dELTA,_0}); 1: by sim.
  sp;if;1: by auto.
  sp;seq 1 1 : (={t,t128_0,t128_1,buf, offset, lEN, st,buf, dELTA,_0}); 1: by sim.
  sp;if;1: by auto.
  sp;seq 1 1 : (={t,t128_0,t128_1,buf, offset, lEN, st,buf, dELTA,_0,t256_0,t256_1,t256_2,t256_3}); by sim.
  by sim.
  sp;if;1: by auto.
  sp;seq 1 1 : (={t,t128_0,t128_1,buf, offset, lEN, st,buf, dELTA,_0,t256_0,t256_1,t256_2,t256_3}); by sim.
  by sim.
  seq 1 1 : (={buf, offset, lEN, st,buf, dELTA}); 1: by sim.
  sp;seq 1 1 : (={buf, offset, lEN, st,buf, dELTA}); 1: by sim.
  sp;if;1: by auto.
  sp;seq 1 1 : (={t,t128_0,t128_1,buf, offset, lEN, st,buf, dELTA}); 1: by sim.
  sp;if;1: by auto.
  sp;seq 1 1 : (={t,t128_0,t128_1,buf, offset, lEN, st,buf, dELTA,t256_0,t256_1,t256_2,t256_3}); by sim.
  by sim.
  sp;if;1: by auto.
  sp;seq 1 1 : (={t,t128_0,t128_1,buf, offset, lEN, st,buf, dELTA,t256_0,t256_1,t256_2,t256_3}); by sim.
  by sim.
qed.

equiv aux_buflen_dumpstate1_xkem_clean :
Xkem_avx2_clean.M.aBUFLEN____dumpstate_array_avx2 ~ Xkem_avx2.M.aBUFLEN____dumpstate_array_avx2 : ={buf, offset, lEN, st}  ==> ={res}.
proc => /=.
  sp;if;1: by auto.
  seq 1 1 : (={buf, offset, lEN, st,buf, dELTA,_0}); 1: by sim.
  sp;seq 1 1 : (={buf, offset, lEN, st,buf, dELTA,_0}); 1: by sim.
  sp;if;1: by auto.
  sp;seq 1 1 : (={t,t128_0,t128_1,buf, offset, lEN, st,buf, dELTA,_0}); 1: by sim.
  sp;if;1: by auto.
  sp;seq 1 1 : (={t,t128_0,t128_1,buf, offset, lEN, st,buf, dELTA,_0,t256_0,t256_1,t256_2,t256_3}); by sim.
  by sim.
  sp;if;1: by auto.
  sp;seq 1 1 : (={t,t128_0,t128_1,buf, offset, lEN, st,buf, dELTA,_0,t256_0,t256_1,t256_2,t256_3}); by sim.
  by sim.
  seq 1 1 : (={buf, offset, lEN, st,buf, dELTA}); 1: by sim.
  sp;seq 1 1 : (={buf, offset, lEN, st,buf, dELTA}); 1: by sim.
  sp;if;1: by auto.
  sp;seq 1 1 : (={t,t128_0,t128_1,buf, offset, lEN, st,buf, dELTA}); 1: by sim.
  sp;if;1: by auto.
  sp;seq 1 1 : (={t,t128_0,t128_1,buf, offset, lEN, st,buf, dELTA,t256_0,t256_1,t256_2,t256_3}); by sim.
  by sim.
  sp;if;1: by auto.
  sp;seq 1 1 : (={t,t128_0,t128_1,buf, offset, lEN, st,buf, dELTA,t256_0,t256_1,t256_2,t256_3}); by sim.
  by sim.
qed.


equiv aux_dumpstate_xkem_clean :
  Xkem_avx2_clean.M.a64____dumpstate_array_avx2 ~ Xkem_avx2.M.a64____dumpstate_array_avx2 :
   ={buf, offset, lEN, st} ==> ={res}.
proc => /=.
  sp;if;1: by auto.
  seq 1 1 : (={buf, offset, lEN, st,buf, dELTA,_0}); 1: by sim.
  sp;seq 1 1 : (={buf, offset, lEN, st,buf, dELTA,_0}); 1: by sim.
  sp;if;1: by auto.
  sp;seq 1 1 : (={t,t128_0,t128_1,buf, offset, lEN, st,buf, dELTA,_0}); 1: by sim.
  sp;if;1: by auto.
  sp;seq 1 1 : (={t,t128_0,t128_1,buf, offset, lEN, st,buf, dELTA,_0,t256_0,t256_1,t256_2,t256_3}); by sim.
  by sim.
  sp;if;1: by auto.
  sp;seq 1 1 : (={t,t128_0,t128_1,buf, offset, lEN, st,buf, dELTA,_0,t256_0,t256_1,t256_2,t256_3}); by sim.
  by sim.
  seq 1 1 : (={buf, offset, lEN, st,buf, dELTA}); 1: by sim.
  sp;seq 1 1 : (={buf, offset, lEN, st,buf, dELTA}); 1: by sim.
  sp;if;1: by auto.
  sp;seq 1 1 : (={t,t128_0,t128_1,buf, offset, lEN, st,buf, dELTA}); 1: by sim.
  sp;if;1: by auto.
  sp;seq 1 1 : (={t,t128_0,t128_1,buf, offset, lEN, st,buf, dELTA,t256_0,t256_1,t256_2,t256_3}); by sim.
  by sim.
  sp;if;1: by auto.
  sp;seq 1 1 : (={t,t128_0,t128_1,buf, offset, lEN, st,buf, dELTA,t256_0,t256_1,t256_2,t256_3}); by sim.
  by sim.
qed.

equiv aux_dumpstate32_xkem_clean :
  Xkem_avx2_clean.M.a32____dumpstate_array_avx2 ~ Xkem_avx2.M.a32____dumpstate_array_avx2 :
   ={buf, offset, lEN, st} ==> ={res}.
proc => /=.
  sp;if;1: by auto.
  seq 1 1 : (={buf, offset, lEN, st,buf, dELTA,_0}); 1: by sim.
  sp;seq 1 1 : (={buf, offset, lEN, st,buf, dELTA,_0}); 1: by sim.
  sp;if;1: by auto.
  sp;seq 1 1 : (={t,t128_0,t128_1,buf, offset, lEN, st,buf, dELTA,_0}); 1: by sim.
  sp;if;1: by auto.
  sp;seq 1 1 : (={t,t128_0,t128_1,buf, offset, lEN, st,buf, dELTA,_0,t256_0,t256_1,t256_2,t256_3}); by sim.
  by sim.
  sp;if;1: by auto.
  sp;seq 1 1 : (={t,t128_0,t128_1,buf, offset, lEN, st,buf, dELTA,_0,t256_0,t256_1,t256_2,t256_3}); by sim.
  by sim.
  seq 1 1 : (={buf, offset, lEN, st,buf, dELTA}); 1: by sim.
  sp;seq 1 1 : (={buf, offset, lEN, st,buf, dELTA}); 1: by sim.
  sp;if;1: by auto.
  sp;seq 1 1 : (={t,t128_0,t128_1,buf, offset, lEN, st,buf, dELTA}); 1: by sim.
  sp;if;1: by auto.
  sp;seq 1 1 : (={t,t128_0,t128_1,buf, offset, lEN, st,buf, dELTA,t256_0,t256_1,t256_2,t256_3}); by sim.
  by sim.
  sp;if;1: by auto.
  sp;seq 1 1 : (={t,t128_0,t128_1,buf, offset, lEN, st,buf, dELTA,t256_0,t256_1,t256_2,t256_3}); by sim.
  by sim.
qed.

equiv aux_dumpstate96_xkem_clean :
  Xkem_avx2_clean.M.a96____dumpstate_array_avx2 ~ Xkem_avx2.M.a96____dumpstate_array_avx2 :
   ={buf, offset, lEN, st} ==> ={res}.
proc => /=.
  sp;if;1: by auto.
  seq 1 1 : (={buf, offset, lEN, st,buf, dELTA,_0}); 1: by sim.
  sp;seq 1 1 : (={buf, offset, lEN, st,buf, dELTA,_0}); 1: by sim.
  sp;if;1: by auto.
  sp;seq 1 1 : (={t,t128_0,t128_1,buf, offset, lEN, st,buf, dELTA,_0}); 1: by sim.
  sp;if;1: by auto.
  sp;seq 1 1 : (={t,t128_0,t128_1,buf, offset, lEN, st,buf, dELTA,_0,t256_0,t256_1,t256_2,t256_3}); by sim.
  by sim.
  sp;if;1: by auto.
  sp;seq 1 1 : (={t,t128_0,t128_1,buf, offset, lEN, st,buf, dELTA,_0,t256_0,t256_1,t256_2,t256_3}); by sim.
  by sim.
  seq 1 1 : (={buf, offset, lEN, st,buf, dELTA}); 1: by sim.
  sp;seq 1 1 : (={buf, offset, lEN, st,buf, dELTA}); 1: by sim.
  sp;if;1: by auto.
  sp;seq 1 1 : (={t,t128_0,t128_1,buf, offset, lEN, st,buf, dELTA}); 1: by sim.
  sp;if;1: by auto.
  sp;seq 1 1 : (={t,t128_0,t128_1,buf, offset, lEN, st,buf, dELTA,t256_0,t256_1,t256_2,t256_3}); by sim.
  by sim.
  sp;if;1: by auto.
  sp;seq 1 1 : (={t,t128_0,t128_1,buf, offset, lEN, st,buf, dELTA,t256_0,t256_1,t256_2,t256_3}); by sim.
  by sim.
qed.

equiv aux_invntt_xkem :
  Jkem_avx2_stack.M._poly_invntt ~ Xkem_avx2.M._poly_invntt : ={arg} ==> ={res}.
proc.
  by unroll for {1} ^while; unroll for {2} ^while; sim.
qed.

equiv aux_invntt_xkem_clean :
  Xkem_avx2_clean.M._poly_invntt ~ Xkem_avx2.M._poly_invntt : ={arg} ==> ={res}.
proc.
  by unroll for {1} ^while; unroll for {2} ^while; sim.
qed.

lemma mlkem_kg_equiv:
  equiv [Jkem_avx2_stack.M.jade_kem_mlkem_mlkem768_amd64_avx2_keypair_derand ~ Xkem_avx2.M.jade_kem_mlkem_mlkem768_amd64_avx2_keypair_derand: ={arg} ==> ={res}].
proof.
    proc => />. inline __crypto_kem_keypair_jazz __indcpa_keypair.
    sim (Jkem_avx2_stack.M.a32____dumpstate_array_avx2 ~ Xkem_avx2.M.a32____dumpstate_array_avx2 : true)
    (Jkem_avx2_stack.M.aBUFLEN____dumpstate_array_avx2 ~ Xkem_avx2.M.aBUFLEN____dumpstate_array_avx2 : true) (Jkem_avx2_stack.M.a64____dumpstate_array_avx2 ~ Xkem_avx2.M.a64____dumpstate_array_avx2 : true)
    (Jkem_avx2_stack.M.aBUFLEN____dumpstate_array_avx2 ~ Xkem_avx2.M.aBUFLEN____dumpstate_array_avx2 : true) => /=.
    apply aux_dumpstate_xkem. apply aux_buflen_dumpstate1_xkem. apply aux_dumpstate32_xkem.
qed.

lemma mlkem_enc_equiv:
  equiv [Jkem_avx2_stack.M.jade_kem_mlkem_mlkem768_amd64_avx2_enc_derand ~ Xkem_avx2.M.jade_kem_mlkem_mlkem768_amd64_avx2_enc_derand: ={arg} ==> ={res}].
proof.
    proc => />. inline __crypto_kem_enc_jazz __indcpa_enc.
    sim (Jkem_avx2_stack.M._poly_invntt ~ Xkem_avx2.M._poly_invntt : (true))
    (Jkem_avx2_stack.M.a32____dumpstate_array_avx2 ~ Xkem_avx2.M.a32____dumpstate_array_avx2 : true)
    (Jkem_avx2_stack.M.a64____dumpstate_array_avx2 ~ Xkem_avx2.M.a64____dumpstate_array_avx2 : true)
    (Jkem_avx2_stack.M.aBUFLEN____dumpstate_array_avx2 ~ Xkem_avx2.M.aBUFLEN____dumpstate_array_avx2 : true) => /=.
    apply aux_dumpstate32_xkem. apply aux_dumpstate_xkem. apply aux_buflen_dumpstate1_xkem. apply aux_invntt_xkem.
qed.

lemma mlkem_dec_equiv:
  equiv [Jkem_avx2_stack.M.jade_kem_mlkem_mlkem768_amd64_avx2_dec ~ Xkem_avx2.M.jade_kem_mlkem_mlkem768_amd64_avx2_dec: ={arg} ==> ={res}].
proof.
  proc => />. inline __crypto_kem_dec_jazz __indcpa_dec.
  sim (Jkem_avx2_stack.M._poly_invntt ~ Xkem_avx2.M._poly_invntt : (true))
  (Jkem_avx2_stack.M.a32____dumpstate_array_avx2 ~ Xkem_avx2.M.a32____dumpstate_array_avx2 : true)
  (Jkem_avx2_stack.M.a64____dumpstate_array_avx2 ~ Xkem_avx2.M.a64____dumpstate_array_avx2 : true)
  (Jkem_avx2_stack.M.aBUFLEN____dumpstate_array_avx2 ~ Xkem_avx2.M.aBUFLEN____dumpstate_array_avx2 : true) => /=.
  apply aux_dumpstate_xkem. apply aux_buflen_dumpstate1_xkem. apply aux_invntt_xkem. apply aux_dumpstate32_xkem.
qed.

lemma eq_xwing_clean_kg:
  equiv [Xkem_avx2_clean.M.jade_kem_xwing_xwing_amd64_avx2_keypair_derand ~ Xkem_avx2.M.jade_kem_xwing_xwing_amd64_avx2_keypair_derand : ={arg} ==> ={res}].
proof.
    proc => />. wp; sp.
    inline {1} 1. inline {2} 1.
    sim (Jkem_avx2_stack.M.jade_kem_mlkem_mlkem768_amd64_avx2_keypair_derand ~ Xkem_avx2.M.jade_kem_mlkem_mlkem768_amd64_avx2_keypair_derand : true)
   (Xkem_avx2_clean.M.a32____dumpstate_array_avx2 ~ Xkem_avx2.M.a32____dumpstate_array_avx2 : true)
   (Xkem_avx2_clean.M.a96____dumpstate_array_avx2 ~ Xkem_avx2.M.a96____dumpstate_array_avx2 : true)
   (Xkem_avx2_clean.M.a64____dumpstate_array_avx2 ~ Xkem_avx2.M.a64____dumpstate_array_avx2 : true)
   (Xkem_avx2_clean.M.aBUFLEN____dumpstate_array_avx2 ~ Xkem_avx2.M.aBUFLEN____dumpstate_array_avx2 : true) => /=. apply aux_dumpstate96_xkem_clean. proc *. call mlkem_kg_equiv. auto => />.
qed.

lemma eq_xwing_clean_enc:
  equiv [Xkem_avx2_clean.M.jade_kem_xwing_xwing_amd64_avx2_enc_derand ~ Xkem_avx2.M.jade_kem_xwing_xwing_amd64_avx2_enc_derand : ={arg} ==> ={res}].
proof.
    proc => />. wp; sp.
    inline {1} 1. inline {2} 1.
    sim (Jkem_avx2_stack.M.jade_kem_mlkem_mlkem768_amd64_avx2_enc_derand ~ Xkem_avx2.M.jade_kem_mlkem_mlkem768_amd64_avx2_enc_derand : true)
   (Xkem_avx2_clean.M.a32____dumpstate_array_avx2 ~ Xkem_avx2.M.a32____dumpstate_array_avx2 : true)
   (Xkem_avx2_clean.M.a96____dumpstate_array_avx2 ~ Xkem_avx2.M.a96____dumpstate_array_avx2 : true)
   (Xkem_avx2_clean.M.a64____dumpstate_array_avx2 ~ Xkem_avx2.M.a64____dumpstate_array_avx2 : true)
   (Xkem_avx2_clean.M.aBUFLEN____dumpstate_array_avx2 ~ Xkem_avx2.M.aBUFLEN____dumpstate_array_avx2 : true) => /=. proc *. call mlkem_enc_equiv. auto => />.  apply aux_dumpstate32_xkem_clean.
qed.

lemma eq_xwing_clean_dec:
  equiv [Xkem_avx2_clean.M.jade_kem_xwing_xwing_amd64_avx2_dec ~ Xkem_avx2.M.jade_kem_xwing_xwing_amd64_avx2_dec : ={arg} ==> ={res}].
proof.
    proc => />. wp; sp.
    inline {1} 1. inline {2} 1.
    sim (Jkem_avx2_stack.M.jade_kem_mlkem_mlkem768_amd64_avx2_dec ~ Xkem_avx2.M.jade_kem_mlkem_mlkem768_amd64_avx2_dec : true)
    (Jkem_avx2_stack.M.jade_kem_mlkem_mlkem768_amd64_avx2_keypair_derand ~ Xkem_avx2.M.jade_kem_mlkem_mlkem768_amd64_avx2_keypair_derand : true)
   (Xkem_avx2_clean.M.a32____dumpstate_array_avx2 ~ Xkem_avx2.M.a32____dumpstate_array_avx2 : true)
   (Xkem_avx2_clean.M.a96____dumpstate_array_avx2 ~ Xkem_avx2.M.a96____dumpstate_array_avx2 : true)
   (Xkem_avx2_clean.M.a64____dumpstate_array_avx2 ~ Xkem_avx2.M.a64____dumpstate_array_avx2 : true)
   (Xkem_avx2_clean.M.aBUFLEN____dumpstate_array_avx2 ~ Xkem_avx2.M.aBUFLEN____dumpstate_array_avx2 : true) => /=. apply aux_dumpstate96_xkem_clean. proc *. call mlkem_kg_equiv. auto => />. proc *. call mlkem_dec_equiv. auto => />. apply aux_dumpstate32_xkem_clean.
qed.

lemma xwing_25519_base_mulx_equiv :
  equiv [Xkem_avx2_clean.M.xwing_x25519_base ~ Mulx_scalarmult_s.M.__curve25519_mulx_base :
    _k{2} = toRep4 np{1}
    ==>
    res{2} = toRep4 res{1}].
proof.
  proc.
  inline{1} 4.
  seq 7 3 : (={u, r, k, _k}). wp. auto => />.
  move => &1.
  + rewrite /copy64 tP => i ib.
  + rewrite unpack64E pack32E /init8 of_listE /get8 /(\bits64).
  + rewrite !initiE 1,2:/# /=.
  + rewrite get64E pack8E !initiE 1:/# //=.
  + rewrite /to_list /mkseq -iotaredE => />.
  + rewrite wordP => ii iib.
  rewrite !initiE 1,2:/# //= !initiE 1,2:/# //= !initiE 1,2:/# //= /#.

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
proof.
  proc.
  inline{1} 6.
  wp; sp.
  sim :  (={k, u, r}).
  move => &1 &2 [?] [H] *. rewrite H.
  + rewrite unpack64E pack32E /init8 of_listE.
  + rewrite tP => i ib. rewrite /get8 /(\bits64) /copy_64.
  + rewrite initiE 1:/# /= initiE 1:/# /=.
  + rewrite /to_list /init64 /(\bits8) /get64_direct /mkseq -iotaredE => />.
  + rewrite wordP => ii iib.
  + rewrite initiE 1:/# /= initiE 1:/# //= initiE 1:/# //=.
  + ring. smt(W8.initiE).
  auto => />. move => &1 *.
  do split.
  + rewrite unpack64E pack32E of_listE.
  + rewrite tP => i ib.
  + rewrite /get8 /(\bits64) /copy_64 /get64_direct /init64 /(\bits8) /pack8_t.
  + rewrite !initiE 1,2:/# /= !initiE 1:/# /=.
  + rewrite wordP => ii iib.
  + rewrite !initiE 1,2:/# /= !initiE 1,2:/# //=  initiE 1:/# //= initiE 1:/# //=.
  + rewrite /to_list /mkseq -iotaredE => /> /#.
  + rewrite unpack64E pack32E of_listE.
  + rewrite tP => i ib.
  + rewrite /get8 /(\bits64) /copy_64 /get64_direct /init64 /(\bits8) /pack8_t.
  + rewrite !initiE 1,2:/# /= !initiE 1:/# /=.
  + rewrite wordP => ii iib.
  + rewrite !initiE 1,2:/# /= !initiE 1,2:/# //=  initiE 1:/# //= initiE 1:/# //=.
  + rewrite /to_list /mkseq -iotaredE => /> /#.
qed.

lemma eq_spec_xwing_25519_base_mulx :
  equiv [Xkem_avx2_clean.M.xwing_x25519_base ~ CurveProcedures.scalarmult_base :
    k'{2} =  pack32 (to_list np{1})
    ==>
    res{2} = pack32 (to_list res{1})].
proof.
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
       res{2} = pack32 (to_list res{1})].
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
  seq 9 2 : (#pre /\ ={expanded}
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
  + auto => />. move => &1. do split.  rewrite tP => i ib. rewrite !initiE 1..3:/# //=.
  + rewrite tP => i ib. rewrite !initiE 1..2:/# //= !initiE 1..2:/# //=.

  auto => />.
  seq 0 1 : (#pre /\ expanded_x25519{1} = sk_X0{2}
                  /\ sk_X0{2} = coins3{2}). auto => />.

  seq 1 1 : (#pre /\ pack32 (to_list pk_x25519{1}) = pk_X_256{2}).
  + call eq_spec_xwing_25519_base_mulx. auto => />.

  seq 0 1 : (#pre /\ pk_x25519{1} = pk_X0{2}). auto => />.
  + move => &1 &2 [#] *. rewrite !tP.
  + move => i ib. rewrite !/to_list !/mkseq -!iotaredE => />. rewrite !/of_list initiE 1:/# //= /#.

  seq 1 1 : (#pre /\ pk_M0{2}.`1 = Array1152.init (fun (i : int) =>  pk_mlkem{1}.[i])
                  /\ pk_M0{2}.`2 = Array32.init(fun (i : int) =>  pk_mlkem{1}.[i + 1152])
                  /\ sk_M0{2}.`1 = Array1152.init(fun i => sk_mlkem{1}.[i])
                  /\ sk_M0{2}.`2.`1 = Array1152.init(fun i => sk_mlkem{1}.[i+1152])
                  /\ sk_M0{2}.`2.`2 = Array32.init(fun i => sk_mlkem{1}.[i+1152+1152])
                  /\ sk_M0{2}.`3 = Array32.init(fun i => sk_mlkem{1}.[i+1152+1152 + 32])
                  /\ sk_M0{2}.`4 = Array32.init(fun i => sk_mlkem{1}.[i+1152+1152 + 32 + 32])).
  + call mlkem_kem_correct_kg. auto => />. smt(). auto => />.

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
   + auto => />. move => &hr Z. rewrite !tP. move => H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.
   + do split; 1,2:smt().
   + move => i ib *. rewrite !initE.
   + case(0 <= i && i < 1184) => *. rewrite ifT 1:/#.
   + rewrite get8_set64_directE 1,2:/#. case (8 * i{!hr} <= i && i < 8 * i{!hr} + 8) => *.
   + rewrite get64E /get8 /init8 !pack8bE 1:/# !initiE 1:/# //= !initiE 1:/# /#.
   + rewrite /get8 /init8 !initiE 1:/#. smt(). smt().
   + move => i ib *.
   + case(0 <= i && i < 1152) => *.
   + rewrite !initiE 1:/#.
   + rewrite get8_set64_directE 1,2:/#. case (8 * i{!hr} <= i && i < 8 * i{!hr} + 8) => *.
   + rewrite get64E /get8 /init8 !pack8bE 1:/# !initiE 1:/# //= !initiE 1:/# H0 1:/#.
   + rewrite /get8 /init8 !initiE 1:/# /#.
   + rewrite /get8 /init8 !initiE 1:/# /#.
   + rewrite /get8 /init8 !initiE 1:/# /#.
   + move => i ib *.
   + rewrite !initiE 1:/#.
   + rewrite get8_set64_directE 1,2:/#. case (8 * i{!hr} <= i && i < 8 * i{!hr} + 8) => *.
   + rewrite get64E /get8 /init8 !pack8bE 1:/# !initiE 1:/# //= !initiE 1:/# H1 1:/# !initiE 1:/# //= /#.
   + rewrite /get8 /init8 !initiE 1:/# /#. smt().

   + wp. auto => />.
   + move => &1 &2 [#] H H0 H1 H2 H3 H4 H5 H6 H7. auto => />. do split;1..3:smt().
   + move => ??. do split.
   + move => H8 H9 H10 H11 H12 /#. move => H11 H12 H13 H14 H15 H16. rewrite tP. do split.
   + move => H17 H18. rewrite -H15 1:/#. smt(Array1152.initiE).
   + rewrite H2  tP => i ib. rewrite !initiE 1,2:/# //= -H14 1,2:/#.

   seq 3 0 : (#pre /\ pk_X0{2} = Array32.init (fun (i0 : int) => pkp{1}.[i0 + 1184])
                   /\ pk_x25519{1} = Array32.init (fun (i0 : int) => pkp{1}.[i0 + 1184])).
   + wp.
   + while{1} (#pre /\ aux{1} = 4
                  /\ 0 <= i{1} <= aux{1}
                  /\ pk_X0{2} = pk_x25519{1}
                  /\ (forall k, 0<=k<min (8 * i{1}) 32 => pkp{1}.[k+1184] = pk_x25519{1}.[k])
                  /\ (forall k, 0<=k<min (8 * i{1}) 32 => pkp{1}.[k+1184] = pk_X0{2}.[k])
                  /\ (forall k, 1184<=k<min (8 * i{1}) 1216 => pkp{1}.[k] = pk_x25519{1}.[k-1216])
                  /\ (forall k, 1184<=k<min (8 * i{1}) 1216 => pkp{1}.[k] = pk_X0{2}.[k-1216]))
              (4 - i{1}).
   + auto => />. move => &hr Z. rewrite !tP.
   move => [#] H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13. do split.
   + move => i ib. rewrite !initiE 1,2:/# /=.
   + rewrite get8_set64_directE 1,2:/# ifF 1:/#.
   + rewrite /get8 /init8 !initiE 1:/# H7 1:/#. smt(Array1152.initiE).
   + move => i ib. rewrite !initiE 1:/# /= !initiE 1:/#.
   + rewrite get8_set64_directE 1,2:/# ifF 1:/#.
   + rewrite /get8 /init8 !initiE 1:/# H8 1:/#. smt(Array32.initiE).
   + smt(). smt().
   + move => k0 i ib. rewrite !initiE 1:/# /=.
   + rewrite get8_set64_directE 1,2:/#.
   + case (8 * (148 + i{!hr}) <= k0 + 1184 && k0 + 1184 < 8 * (148 + i{!hr}) + 8) => *.
   + rewrite get64E /get8 /init8 !pack8bE 1:/# !initiE 1:/# //= !initiE 1:/# /# //=.
   + rewrite /get8 /init8 !initiE 1:/# H11 1:/# /#.
   + move => k0 i ib. rewrite !initiE 1:/# /=.
   + rewrite get8_set64_directE 1,2:/#.
   + case (8 * (148 + i{!hr}) <= k0 + 1184 && k0 + 1184 < 8 * (148 + i{!hr}) + 8) => *.
   + rewrite get64E /get8 /init8 !pack8bE 1:/# !initiE 1:/# //= !initiE 1:/# /# //=.
   + rewrite /get8 /init8 !initiE 1:/# H11 1:/# /#.
   + move => k0 i ib. rewrite !initiE 1:/# /=.
   + rewrite get8_set64_directE 1,2:/#. rewrite ifF 1:/#.
   + rewrite /get8 /init8 !initiE 1:/# H12 1:/# /#.
   + move => k0 i ib. rewrite !initiE 1:/# /=.
   + rewrite get8_set64_directE 1,2:/#. rewrite ifF 1:/#.
   + rewrite /get8 /init8 !initiE 1:/# H12 1:/# /#. smt().

   + wp. auto => />. rewrite !tP. move => &1 &2 [#] H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9.
   + do split;1..4:smt().
   + move => H10 H11. do split. move => H12 H13 H14 H15 H16 H17 H18. smt().
   + move => H15 H16 H17 H18 H19 H20 H21. rewrite tP. do split.
   + move => i ib. rewrite !initiE 1:/# //=. smt().
   + move => i ib. rewrite !initiE 1:/# //=. smt().

   seq 3 0 : (#pre /\ sk{2} = skp{1}).
   + while{1} (#pre /\ aux{1} = 4
                  /\ 0 <= i{1} <= aux{1}
                  /\ sk{2} = srandomness{1}
                  /\ sk0{2} = srandomness{1}
                  /\ (forall k, 0<=k<min (8 * i{1}) 32 => skp{1}.[k] = sk{2}.[k])
                  /\ (forall k, 0<=k<min (8 * i{1}) 32 => skp{1}.[k] = sk0{2}.[k]))
              (4 - i{1}).
   + auto => />. move => &hr Z. rewrite !tP. move => H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.
   + do split; 1,2:smt().
   + move => i ib *. rewrite !initiE 1:/#.
   + rewrite get8_set64_directE 1,2:/#. case(8 * i{!hr} <= i && i < 8 * i{!hr} + 8) => *.
   + rewrite get64E /get8 /init8 !pack8bE 1:/# !initiE 1:/# //= !initiE 1:/# /# //=.
   + rewrite /get8 /init8 !initiE 1:/# H11 1:/# /#.
   + move => i ib *. rewrite !initiE 1:/#.
   + rewrite get8_set64_directE 1,2:/#. case(8 * i{!hr} <= i && i < 8 * i{!hr} + 8) => *.
   + rewrite get64E /get8 /init8 !pack8bE 1:/# !initiE 1:/# //= !initiE 1:/# /# //=.
   + rewrite /get8 /init8 !initiE 1:/# H11 1:/# /#. smt().

   + wp. auto => />.
   + move => &1 &2 [#] *. do split. smt(). smt(). move => I I0. do split.
   + smt(). move => [#] H H0 H1 H2.
   + rewrite tP => i ib. rewrite H2 1,2:/#.

   wp. auto => />. rewrite !tP.
   move => &1 &2 H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.
   rewrite initiE 1,2:/#.
qed.


lemma eq_spec_xwing_enc:
  equiv [Xkem_avx2_clean.M._crypto_xkem_enc_derand_jazz ~ XWing.enc_derand :
      coins{2}.`1 = Array32.init (fun (i:int) => eseed{1}.[i])
   /\ coins{2}.`2 = Array32.init (fun (i:int) => eseed{1}.[i + 32])
   /\ pk{2}.`1.`1 = Array1152.init(fun i => pkp{1}.[i])
   /\ pk{2}.`1.`2 = Array32.init(fun i => pkp{1}.[i+1152])
   /\ pk{2}.`2    = Array32.init(fun i => pkp{1}.[i+1184])
      ==>
      res{2}.`1.`1.`1 = Array960.init(fun i => res{1}.`1.[i])
   /\ res{2}.`1.`1.`2 = Array128.init(fun i => res{1}.`1.[i+960])
   /\ res{2}.`1.`2    = Array32.init(fun i => res{1}.`1.[i+1088])
   /\ res{2}.`2 = res{1}.`2].
proof.
    proc => />.
    proc rewrite {1} 12 (copy1216).
    proc rewrite {1} 13 (copy64).

    seq 13 0 : (#pre /\ spkp{1} = pkp{1} /\ spkp{1} = pkp{1} /\ seseed{1} = eseed{1}).
    + auto => />.

    seq 1 1  : (#pre /\ pk_M{2}.`1 = Array1152.init (fun (i:int) => pk_mlkem{1}.[i])
                     /\ pk_M{2}.`2 = Array32.init (fun (i:int) => pk_mlkem{1}.[i+1152])
                     /\ pk_M{2}.`1 = Array1152.init (fun (i:int) => pkp{1}.[i])
                     /\ pk_M{2}.`2 = Array32.init (fun (i:int) => pkp{1}.[i+1152])).
    + auto => />. rewrite !tP. move => &1 &2 [#] H H0 H1 H2 H3. do split.
    + move => i ib. rewrite !initiE 1,2:/# H1 1:/#. rewrite !initiE 1,2:/#.
    + move => i ib. rewrite !initiE 1:/# //= H2 1:/#. rewrite !initiE 1,2:/# //=.

    seq 1 1  : (#pre /\ pk_X{2} = Array32.init (fun (i:int) => pk_x25519{1}.[i])
                     /\ pk_X{2} = Array32.init (fun (i:int) => pkp{1}.[i+1184])).
    + auto => />. rewrite !tP. move => &1 &2 [#] H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9.
    + rewrite !initiE 1,2:/# //= H3 1:/#. rewrite !initiE 1,2:/#.

    seq 1 1  : (#pre /\ ek_X{2} = Array32.init (fun (i:int) => ek_x25519{1}.[i])
                     /\ ek_X{2} = Array32.init (fun (i:int) => seseed{1}.[i+32])).
    + auto => />. rewrite !tP. move => &1 &2 [#] H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
    + rewrite !initiE 1,2:/# //= H0 1:/#. rewrite !initiE 1,2:/#.
    swap{1} 3 -2.
    seq 1 1  : (#pre /\ c_M{2} = seed_mlkem{1}
                     /\ c_M{2} = Array32.init (fun (i:int) => seseed{1}.[i])).
    + auto => />.

    seq 1 1 : (#pre /\ pack32 (to_list ct_x25519{1}) = ct_X_256{2}).
    + call eq_spec_xwing_25519_base_mulx. auto => />.
    + move => &1 &2 H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9.
    + congr. congr. congr. rewrite tP => *. smt(Array32.initiE).

    seq 1 1 : (#pre /\ pack32 (to_list ss_x25519{1}) = ss_X_256{2}).
    + call eq_spec_xwing_25519_mulx. auto => />.
    + move => &1 &2 H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9. do split.
    + congr. congr. congr. rewrite tP => *. smt(Array32.initiE).
    + congr. congr. congr. rewrite tP => *. smt(Array32.initiE).

    seq 0 1 : (#pre /\ ct_X{2} = ct_x25519{1}).
    + auto => />. move => &1 &2 H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9.
    + rewrite !/of_list !/to_list !/mkseq -iotaredE => />.
    + rewrite tP => i ib. rewrite initiE 1,2:/#.

    seq 0 1 : (#pre /\ ss_X{2} = ss_x25519{1}).
    + auto => />. move => &1 &2 H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9.
    + rewrite !/of_list !/to_list !/mkseq -iotaredE => />.
    + rewrite tP => i ib. rewrite initiE 1,2:/#.

   seq 2 3 : (#pre /\ ct_M{2}.`1 = Array960.init(fun i => ct_mlkem{1}.[i])
                   /\ ct_M{2}.`2 = Array128.init(fun i => ct_mlkem{1}.[i+960])
                   /\ ct{2}.`1.`1 = Array960.init(fun i => ct_mlkem{1}.[i])
                   /\ ct{2}.`1.`2 = Array128.init(fun i => ct_mlkem{1}.[i+960])
                   /\ ct{2}.`2 = Array32.init (fun i => ct_X{2}.[i])
                   /\ ct{2}.`2 = ct_x25519{1}
                   /\ ct_x25519{1} = ct_X{2}
                   /\ ct_M{2}.`1 = ct{2}.`1.`1
                   /\ ct_M{2}.`2 = ct{2}.`1.`2
                   /\ ss_M{2} = ss_mlkem{1}
                   /\ ={ss}).
    + inline {2} 2. wp; sp.
    + ecall {1} (sha3_256_A128__A6 ss{1} ss_mlkem{1} ss_x25519{1} ct_x25519{1} pk_x25519{1}).
    + call mlkem_kem_correct_enc. auto => />.
    + move => &1 &2 H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.
    + do split;1..4:smt(). rewrite tP => i ib. smt(Array32.initiE). smt().
    + congr. congr. smt(). + rewrite tP => i ib. smt(Array32.initiE).

    wp. auto => />.
    + seq 3 0 : (#pre  /\ ct{2}.`1.`1 = Array960.init(fun i => ctp{1}.[i])
                       /\ ct{2}.`1.`2 = Array128.init(fun i => ctp{1}.[i+960])
                       /\ ct{2}.`1.`1 = Array960.init(fun i => ct_mlkem{1}.[i])
                       /\ ct{2}.`1.`2 = Array128.init(fun i => ct_mlkem{1}.[i+960])
                       /\ ct_M{2}.`1 = Array960.init(fun i => ctp{1}.[i])
                       /\ ct_M{2}.`2 = Array128.init(fun i => ctp{1}.[i+960])
                       /\ ct_M{2}.`1 = ct{2}.`1.`1
                       /\ ct_M{2}.`2 = ct{2}.`1.`2
                       /\ ct_X{2} = ct{2}.`2).
    + while{1} (#pre /\ aux{1} = 136
                     /\ ct{2}.`1.`1 = Array960.init(fun i => ct_mlkem{1}.[i])
                     /\ ct{2}.`1.`2 = Array128.init(fun i => ct_mlkem{1}.[i+960])
                     /\ ct_M{2}.`1 = Array960.init(fun i => ct_mlkem{1}.[i])
                     /\ ct_M{2}.`2 = Array128.init(fun i => ct_mlkem{1}.[i+960])
                     /\ ct_X{2} = ct_x25519{1}
                     /\ (forall k, 0<=k<min (8 * i{1}) 960 => ctp{1}.[k] = ct_mlkem{1}.[k])
                     /\ (forall k, 960<=k<min (8 * i{1}) 1088 => ctp{1}.[k] = ct_mlkem{1}.[k])
                     /\ (forall k, 0<=k<min (8 * i{1}) 960 => ctp{1}.[k] = ct{2}.`1.`1.[k])
                     /\ (forall k, 960<=k<min (8 * i{1}) 1088 => ctp{1}.[k] = ct{2}.`1.`2.[k-960])
                     /\ (forall k, 0<=k<min (8 * i{1}) 960 => ctp{1}.[k] = ct_M{2}.`1.[k])
                     /\ (forall k, 960<=k<min (8 * i{1}) 1088 => ctp{1}.[k] = ct_M{2}.`2.[k-960]))
              (136 - i{1}).
    + auto => />. move => &hr Z. rewrite !tP.
    + move => H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 *. do split.
    + move => i b *. rewrite !initiE 1:/# get8_set64_directE 1,2:/#.
    + case(8 * i{!hr} <= i && i < 8 * i{!hr} + 8) => *.
    + rewrite get64E /init8 pack8bE 1:/# !initiE 1:/# //= !initiE 1:/# //= /#.
    + rewrite /get8 /init8  -H16 1:/# !initiE 1:/# //=.
    + move => i b *. rewrite !initiE 1:/# get8_set64_directE 1,2:/#.
    + case(8 * i{!hr} <= i && i < 8 * i{!hr} + 8) => *.
    + rewrite get64E /init8 pack8bE 1:/# !initiE 1:/# //= !initiE 1:/# //= /#.
    + rewrite /get8 /init8. rewrite -H17 1:/# !initiE 1:/# //=.
    + move => i b *. rewrite H11 1:/#.
    + rewrite !initiE 1,2:/# get8_set64_directE 1,2:/#.
    + case(8 * i{!hr} <= i && i < 8 * i{!hr} + 8) => *.
    + rewrite get64E /init8 pack8bE 1:/# !initiE 1:/# //= !initiE 1:/# //= /#.
    + rewrite /get8 /init8. rewrite -H16 1:/# !initiE 1:/# //=.
    + move => i b *. rewrite H12 1:/#.
    + rewrite !initiE 1,2:/# get8_set64_directE 1,2:/#.
    + case(8 * i{!hr} <= i && i < 8 * i{!hr} + 8) => *.
    + rewrite get64E /init8 pack8bE 1:/# !initiE 1:/# //= !initiE 1:/# //= /#.
    + rewrite /get8 /init8. rewrite -H17 1:/# !initiE 1:/# //=.
    + move => i b *. rewrite H9 1:/#.
    + rewrite !initiE 1,2:/# get8_set64_directE 1,2:/#.
    + case(8 * i{!hr} <= i && i < 8 * i{!hr} + 8) => *.
    + rewrite get64E /init8 pack8bE 1:/# !initiE 1:/# //= !initiE 1:/# //= /#.
    + rewrite /get8 /init8. rewrite -H16 1:/# !initiE 1:/# //=.
    + move => i b *. rewrite H10 1:/#.
    + rewrite !initiE 1,2:/# get8_set64_directE 1,2:/#.
    + case(8 * i{!hr} <= i && i < 8 * i{!hr} + 8) => *.
    + rewrite get64E /init8 pack8bE 1:/# !initiE 1:/# //= !initiE 1:/# //= /#.
    + rewrite /get8 /init8. rewrite -H17 1:/# !initiE 1:/# //=. smt().

    + wp. auto => />. move => &1 &2 H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16.
    + do split;1..6:smt().
    + move => H17 H18. do split. move => *. smt(). move => *. do split. rewrite tP => i ib.
    + rewrite initiE 1:/#. smt(). rewrite tP => i ib. rewrite initiE 1:/#. smt(). rewrite tP => i ib.
    + rewrite initiE 1:/#. smt(). rewrite tP => i ib. rewrite initiE 1:/#. smt().

    wp. auto => />.
    + seq 3 0 : (#pre /\ ct_X{2} = Array32.init(fun i => ctp{1}.[i+1088])
                      /\ ct_x25519{1} = Array32.init(fun i => ctp{1}.[i+1088])).

    + while{1} (#pre /\ aux{1} = 4
                     /\ 0 <= i{1} <= 4
                     /\ (forall k, 0<=k<min (8 * i{1}) 32 => ctp{1}.[k+1088] = ct_x25519{1}.[k]))
              (4 - i{1}).
    + auto => />. move => &hr Z. rewrite !tP.
    + move => H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.
    + move => H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23.
    + do split.
    + move => i b *. rewrite H16 1:/# !initiE 1..3:/#.
    + rewrite get8_set64_directE 1,2:/# ifF 1:/#.
    + rewrite /get8 /init8 !initiE 1,2:/# /=.
    + move => i b *. rewrite H17 1:/# !initiE 1,2:/# //= !initiE 1:/#.
    + rewrite get8_set64_directE 1,2:/# ifF 1:/#.
    + rewrite /get8 /init8 !initiE 1,2:/#.
    + move => i b *. rewrite H18 1:/# !initiE 1..3:/# //=.
    + rewrite get8_set64_directE 1,2:/# ifF 1:/#.
    + rewrite /get8 /init8 !initiE 1,2:/#.
    + move => i b *. rewrite H19 1:/# !initiE 1..2:/# //= !initiE 1:/#.
    + rewrite get8_set64_directE 1,2:/# ifF 1:/#.
    + rewrite /get8 /init8 !initiE 1,2:/#.
    + smt(). smt().
    + move => i b *. rewrite !initiE 1:/# //=.
    + rewrite get8_set64_directE 1,2:/#.
    + case (8 * (136 + i{!hr}) <= i + 1088 && i + 1088 < 8 * (136 + i{!hr}) + 8) => *.
    + rewrite get64E /init8 pack8bE 1:/# !initiE 1:/# //= !initiE 1:/# //= /#.
    + rewrite /get8 /init8. rewrite -H22 1:/# !initiE 1,2:/# //= /#. smt().

    + wp. simplify. skip => />.
    + move => &1 &2 [#] H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20.
    + do split. smt(). move => [#] H21 H22. do split. move => [#] H23 H24 H25 H26 H27 H28 H29 H30.
    + smt(). move => [#] H31 H32 H33 H34 H35 H36 H37 H38. do split. rewrite tP => i ib.
    + rewrite !initiE 1:/# //=. smt(). rewrite tP => i ib. rewrite !initiE 1:/# //=. smt().

    wp. auto => />.
    + seq 3 0 : (#pre  /\ ss{2} = shkp{1} /\ ={ss} /\ shkp{1} = ss{1}).

    + while{1} (#pre /\ aux{1} = 4
                     /\ 0 <= i{1} <= 4
                     /\ ={ss}
                     /\ (forall k, 0<=k<min (8 * i{1}) 32 => shkp{1}.[k] = ss{1}.[k])
                     /\ (forall k, 0<=k<min (8 * i{1}) 32 => shkp{1}.[k] = ss{2}.[k])) (4 - i{1}).
    + auto => />. move => &hr Z. rewrite !tP.
    + move => [#] H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17.
    + move => [#] H18 H19 H20 H21 H22 H23 H24.
    + do split. smt(). smt().
    + move => i ib *.  rewrite !initiE 1:/#.
    + rewrite get8_set64_directE 1,2:/#. case(8 * i{!hr} <= i && i < 8 * i{!hr} + 8) => *.
    + rewrite get64E /init8 pack8bE 1:/# !initiE 1:/# //= !initiE 1:/# //= /#.
    + rewrite /get8 /init8 -H23 1:/#. smt(WArray32.initiE).
    + move => i ib *.  rewrite !initiE 1:/#.
    + rewrite get8_set64_directE 1,2:/#. case(8 * i{!hr} <= i && i < 8 * i{!hr} + 8) => *.
    + rewrite get64E /init8 pack8bE 1:/# !initiE 1:/# //= !initiE 1:/# //= /#.
    + rewrite /get8 /init8 -H23 1:/#. smt(WArray32.initiE). smt().
    + wp. simplify. skip => />.
    + move => &1 &2 [#] H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21.
    + do split. smt(). move => [#] H22 H23 H24. smt(). move => [#] H24 H25. do split. smt().
    + move => [#] H28 H29 H30 H31. do split. rewrite tP => i ib. smt(). rewrite tP => i ib. smt().
    auto => />.
qed.

lemma eq_spec_xwing_dec:
  equiv [Xkem_avx2_clean.M._crypto_xkem_dec_jazz ~ XWing.dec :
      skp{1} = sk{2}
   /\ cph{2}.`1.`1 = Array960.init(fun i => ctp{1}.[i])
   /\ cph{2}.`1.`2 = Array128.init(fun i => ctp{1}.[i+960])
   /\ cph{2}.`2    = Array32.init(fun i => ctp{1}.[i+1088])
      ==>
   ={res}].
proof.
    proc => />.
    proc rewrite {1} 14 (copy1120).
    proc rewrite {1} 15 (copy32).
    inline {2} 1. auto => />.
    seq 16 2 : (#pre /\ expanded{1} = SHAKE256_32_96 sskp{1}
                  /\ skp{1} = sskp{1}
                  /\ sctp{1} = ctp{1}
                  /\ ={expanded}
                  /\ sskp{1} = sk0{2}
                  /\ sskp{1} = sk{2}).
  + ecall {1} (shake256_A96_A32 expanded{1} sskp{1}); wp; skip => />.

  swap{1} 3 -2. swap{2} 3 -2.
  seq 1 1 : (#pre /\ coins3{2} = expanded_x25519{1}
                  /\ coins3{2} = Array32.init(fun (i : int) => expanded{1}.[i + 64])
                  /\ coins3{2} = Array32.init(fun (i : int) => expanded{2}.[i + 64])).
  + auto => />. move => &1 &2 [#] H H0 H1. rewrite !tP. do split.
  + move => i ib. rewrite !initiE 1,2:/# //= /#. + move => i ib. rewrite !initiE 1,2:/# //= /#.

  seq 1 2 : (#pre /\ coins1{2} = Array32.init (fun (i : int ) => expanded_mlkem{1}.[i])
                  /\ coins2{2} = Array32.init (fun (i : int ) => expanded_mlkem{1}.[32 + i])
                  /\ coins1{2} = Array32.init (fun (i : int ) => expanded{1}.[i])
                  /\ coins2{2} = Array32.init (fun (i : int ) => expanded{1}.[32 + i])
                  /\ coins1{2} = Array32.init (fun (i : int ) => expanded{2}.[i])
                  /\ coins2{2} = Array32.init (fun (i : int ) => expanded{2}.[32+i])).
  + auto => />. move => &1 &2 [#] H H0 H1. do split.  rewrite tP => i ib. rewrite !initiE 1..5:/# //=.
  + rewrite tP => i ib. rewrite !initiE 1..2:/# //= !initiE 1..3:/# //=.

  auto => />.
  seq 0 1 : (#pre /\ expanded_x25519{1} = sk_X0{2}
                  /\ sk_X0{2} = coins3{2}). auto => />.
  swap{1} 1 1.
  seq 1 1 : (#pre /\ pack32 (to_list pk_x25519{1}) = pk_X_256{2}).
  + call eq_spec_xwing_25519_base_mulx. auto => />.

  seq 0 1 : (#pre /\ pk_x25519{1} = pk_X0{2}
                  /\ pk_x25519{1} = Array32.of_list W8.zero (W32u8.to_list pk_X_256{2})). auto => />.
  + move => &1 &2 [#] *. rewrite !tP. do split.
  + move => i ib. rewrite !/to_list !/mkseq -!iotaredE => />. rewrite !/of_list initiE 1:/# //=. smt().
  + move => i ib. rewrite !/to_list !/mkseq -!iotaredE => />. rewrite !/of_list initiE 1:/# //=. smt().

  seq 1 1 : (#pre /\ pk_M0{2}.`1 = (init (fun (i : int) =>  pk_mlkem{1}.[i]))%Array1152
                  /\ pk_M0{2}.`2 = (init (fun (i : int) =>  pk_mlkem{1}.[i + 1152]))%Array32
                  /\ sk_M0{2}.`1 = Array1152.init(fun i => sk_mlkem{1}.[i])
                  /\ sk_M0{2}.`2.`1 = Array1152.init(fun i => sk_mlkem{1}.[i+1152])
                  /\ sk_M0{2}.`2.`2 = Array32.init(fun i => sk_mlkem{1}.[i+1152+1152])
                  /\ sk_M0{2}.`3 = Array32.init(fun i => sk_mlkem{1}.[i+1152+1152 + 32])
                  /\ sk_M0{2}.`4 = Array32.init(fun i => sk_mlkem{1}.[i+1152+1152 + 32 + 32])
                  /\ let (t,rho) = pk_M0{2} in
                     sk_M0{2}.`1 = Array1152.init(fun i => sk_mlkem{1}.[i])
                  /\ sk_M0{2}.`2.`1 = Array1152.init(fun i => sk_mlkem{1}.[i+1152])
                  /\ sk_M0{2}.`2.`2 = Array32.init(fun i => sk_mlkem{1}.[i+1152+1152])
                  /\ sk_M0{2}.`3 = Array32.init(fun i => sk_mlkem{1}.[i+1152+1152 + 32])
                  /\ sk_M0{2}.`4 = Array32.init(fun i => sk_mlkem{1}.[i+1152+1152 + 32 + 32])
                  /\ t = Array1152.init(fun i => pk_mlkem{1}.[i])
                  /\ rho = Array32.init(fun i => pk_mlkem{1}.[i+1152])).
  + call mlkem_kem_correct_kg. auto => />. smt(). auto => />.

  seq 0 2 : (#pre /\ sk_M{2} = sk_M0{2}
                  /\ sk_X{2} = sk_X0{2}
                  /\ pk_M{2} = pk_M0{2}
                  /\  pk_X{2} = pk_X0{2}). auto => />.

  seq 2 2 : (#pre /\ Array960.init (fun (i:int) => ct_mlkem{1}.[i]) = ct_M{2}.`1
                  /\ Array128.init (fun (i:int) => ct_mlkem{1}.[i+960]) = ct_M{2}.`2
                  /\ ct_x25519{1} = ct_X{2}
                  /\ ct_M{2}.`1 = (init (fun (i_0 : int) => sctp{1}.[0 + i_0]))%Array960
                  /\ ct_M{2}.`2 = (init (fun (i_0 : int) => sctp{1}.[960 + i_0]))%Array128
                  /\ ct_X{2} = (init (fun (i_0 : int) => sctp{1}.[3 * 320 + 128 + i_0]))%Array32).
  + wp; auto => />; move => &1 &2 [#] H H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13. rewrite !tP. do split.
  + move => i ib. rewrite H  !initiE 1..3:/# //=.
  + move => i ib. rewrite H1  !initiE 1:/# //= !initiE 1:/# //=.
  + move => i ib. rewrite H2  !initiE 1:/# //= //= /#.
  + move => i ib. rewrite H1 !initiE 1:/# //= //= /#.
  + move => i ib. rewrite H2 !initiE 1:/# //= //= /#.

  seq 1 1 : (#pre /\ ss_mlkem{1} = ss_M{2}).
  + call mlkem_kem_correct_dec. auto => />.
  + move => [#] &1 &2 eH H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19.
  + rewrite !tP. do split;1:smt(). move => i ib. rewrite H14 1:/#.

  seq 1 1 : (#pre /\ pack32 (to_list ss_x25519{1}) = ss_X_256{2} /\ expanded_x25519{1} = sk_X{2}).
  + call eq_spec_xwing_25519_mulx. auto => />.

  seq 0 1 : (#pre /\ ss_X{2} = ss_x25519{1}). auto => />. rewrite !tP. move => *.
  rewrite !/of_list !/to_list !/mkseq -!iotaredE => />. rewrite !initiE 1:/# /#.

  seq 1 1 : (#pre /\ ={ss}).
  + inline {2} 1. wp; sp.
  + ecall {1} (sha3_256_A128__A6 ss{1} ss_mlkem{1} ss_x25519{1} ct_x25519{1} pk_x25519{1}).
  + wp; skip => />.

  seq 3 0 : (#pre  /\ ss{2} = shkp{1} /\ ={ss} /\ shkp{1} = ss{1}).

    + while{1} (#pre /\ aux{1} = 4
                     /\ 0 <= i{1} <= 4
                     /\ ={ss}
                     /\ (forall k, 0<=k<min (8 * i{1}) 32 => shkp{1}.[k] = ss{1}.[k])
                     /\ (forall k, 0<=k<min (8 * i{1}) 32 => shkp{1}.[k] = ss{2}.[k])) (4 - i{1}).
    + auto => />. move => &hr Z. rewrite !tP.
    + move => [#] H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17.
    + move => [#] H18 H19.
    + do split. smt(). smt().
    + move => i ib *.  rewrite !initiE 1:/#.
    + rewrite get8_set64_directE 1,2:/#. case(8 * i{!hr} <= i && i < 8 * i{!hr} + 8) => *.
    + rewrite get64E /init8 pack8bE 1:/# !initiE 1:/# //= !initiE 1:/# //= /#.
    + rewrite /get8 /init8 -H18 1:/#. smt(WArray32.initiE).
    + move => i ib *.  rewrite !initiE 1:/#.
    + rewrite get8_set64_directE 1,2:/#. case(8 * i{!hr} <= i && i < 8 * i{!hr} + 8) => *.
    + rewrite get64E /init8 pack8bE 1:/# !initiE 1:/# //= !initiE 1:/# //= /#.
    + rewrite /get8 /init8 -H18 1:/#. smt(WArray32.initiE).  smt().
    + wp. simplify. skip => />.
    + move => &1 &2 [#] H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16.
    + do split. smt(). move => [#] H22 H23 H24. smt(). move => [#] H24 H25. do split. smt().
    + move => [#] H28 H29 H30 H31. do split. rewrite tP => i ib. smt(). rewrite tP => i ib. smt().
    auto => />.
qed.


lemma xwing_kg_correct:
  equiv [Xkem_avx2.M.jade_kem_xwing_xwing_amd64_avx2_keypair_derand ~ XWing.kg_derand :
      sk{2} = coins{1}
      ==>
      res{2}.`1 = Array32.init(fun i => res{1}.`2.[i])  /\
      res{2}.`2.`1.`1 = Array1152.init(fun i => res{1}.`1.[i]) /\
      res{2}.`2.`1.`2 = Array32.init(fun i => res{1}.`1.[i+1152]) /\
      res{2}.`2.`2 = Array32.init(fun i => res{1}.`1.[i+1184])].
proof.
    transitivity
    Xkem_avx2_clean.M.jade_kem_xwing_xwing_amd64_avx2_keypair_derand
    (={arg} ==> ={res})
    ( sk{2} = Array32.init(fun i => coins{1}.[i])
      ==> res{2}.`1 = Array32.init(fun i => res{1}.`2.[i])  /\
          res{2}.`2.`1.`1 = Array1152.init(fun i => res{1}.`1.[i]) /\
          res{2}.`2.`1.`2 = Array32.init(fun i => res{1}.`1.[i+1152]) /\
          res{2}.`2.`2 = Array32.init(fun i => res{1}.`1.[i+1184])).
    + auto => />. move => &1. exists(public_key{1}, secret_key{1}, coins{1}).
    + do split;1:smt(). rewrite tP => i ib. rewrite !initiE 1:/# /#.
    + smt(). proc *. symmetry. call eq_xwing_clean_kg. auto => />.

    proc *. inline {1} 1. wp; sp. call eq_spec_xwing_keygen.
    auto => />. move => &1. rewrite !tP => i ib. rewrite initiE 1:/# /#.
qed.

lemma xwing_enc_correct:
  equiv [Xkem_avx2.M.jade_kem_xwing_xwing_amd64_avx2_enc_derand ~ XWing.enc_derand :
         pk{2}.`1.`1 = Array1152.init (fun (i : int) => public_key{1}.[i])
      /\ pk{2}.`1.`2 = Array32.init (fun (i : int) => public_key{1}.[i + 1152])
      /\ pk{2}.`2    = Array32.init(fun i => public_key{1}.[i+1184])
      /\ coins{2}.`1 = Array32.init (fun (i : int) => coins{1}.[i])
      /\ coins{2}.`2 = Array32.init (fun (i : int) => coins{1}.[i+32])
      ==>
         res{2}.`1.`1.`1 = Array960.init(fun i => res{1}.`1.[i])
      /\ res{2}.`1.`1.`2 = Array128.init(fun i => res{1}.`1.[i+960])
      /\ res{2}.`1.`2    = Array32.init(fun i => res{1}.`1.[i+1088])
      /\ res{2}.`2 = res{1}.`2].
proof.
    transitivity
    Xkem_avx2_clean.M.jade_kem_xwing_xwing_amd64_avx2_enc_derand
    (={arg} ==> ={res})
    ( pk{2}.`1.`1 = Array1152.init (fun (i : int) => public_key{1}.[i])
      /\ pk{2}.`1.`2 = Array32.init (fun (i : int) => public_key{1}.[i + 1152])
      /\ pk{2}.`2    = Array32.init(fun i => public_key{1}.[i+1184])
      /\ coins{2}.`1 = Array32.init (fun (i : int) => coins{1}.[i])
      /\ coins{2}.`2 = Array32.init (fun (i : int) => coins{1}.[i+32])
      ==>
      res{2}.`1.`1.`1 = Array960.init(fun i => res{1}.`1.[i])
      /\ res{2}.`1.`1.`2 = Array128.init(fun i => res{1}.`1.[i+960])
      /\ res{2}.`1.`2    = Array32.init(fun i => res{1}.`1.[i+1088])
      /\ res{2}.`2 = res{1}.`2).
    + auto => />. move => &1 &2 [#] *. exists(ciphertext{1}, shared_secret{1}, public_key{1}, coins{1}).
    + do split;1..6:smt(). smt().
    + proc *. symmetry. call eq_xwing_clean_enc. auto => />.
    proc *. inline {1} 1. wp; sp. call eq_spec_xwing_enc.
    auto => />.
qed.

lemma xwing_dec_correct:
  equiv [Xkem_avx2.M.jade_kem_xwing_xwing_amd64_avx2_dec ~ XWing.dec :
         secret_key{1} = sk{2}
      /\ cph{2}.`1.`1 = Array960.init(fun i => ciphertext{1}.[i])
      /\ cph{2}.`1.`2 = Array128.init(fun i => ciphertext{1}.[i+960])
      /\ cph{2}.`2    = Array32.init(fun i => ciphertext{1}.[i+1088])
      ==>
      res{1}.`1 = res{2}].
proof.
    transitivity
    Xkem_avx2_clean.M.jade_kem_xwing_xwing_amd64_avx2_dec
    (={arg} ==> ={res})
    ( secret_key{1} = sk{2}
      /\ cph{2}.`1.`1 = Array960.init(fun i => ciphertext{1}.[i])
      /\ cph{2}.`1.`2 = Array128.init(fun i => ciphertext{1}.[i+960])
      /\ cph{2}.`2    = Array32.init(fun i => ciphertext{1}.[i+1088])
      ==>
      res{1}.`1 = res{2}).
    + auto => />. move => &1 &2 [#] *. exists(shared_secret{1}, ciphertext{1}, secret_key{1}).
    + do split;1..5:smt(). smt().
    + proc *. symmetry. call eq_xwing_clean_dec. auto => />.
    proc *. inline {1} 1. wp; sp. call eq_spec_xwing_dec.
    auto => />.
qed.
