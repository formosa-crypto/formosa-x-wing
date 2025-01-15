require import AllCore IntDiv CoreMap List Distr IntDiv Ring StdOrder.

import IntID.

from CryptoSpecs require import Bindings.
from CryptoSpecs require import Correctness.

from Jasmin require import JModel_x86.

from CryptoSpecs require import Correctness.
from JazzEC require import Jkem_avx2.

from MLKEM require import MLKEM_KEM_avx2_stack.

from JazzEC require import WArray4 WArray6 WArray32 WArray64 WArray96 WArray1088 WArray1120 WArray1184 WArray1216 WArray2400.
from JazzEC require import Array4 Array6 Array8 Array32 Array64 Array96 Array140 Array152 Array128 Array960 Array1088 Array1120 Array1184 Array1216 Array2400 Array1152.

require import Xkem_avx2_clean XWing_Helper_Functions XWing_Spec.
require import XWing_keccak_avx2.

from JazzEC require import Xkem_avx2 Mulx_scalarmult_s Jkem_avx2_stack.

from X25519 require import CorrectnessProof_Mulx Curve25519_Procedures.

from CryptoSpecs require import MLKEM Symmetric InnerPKE FIPS202_SHA3.

from MLKEM require import Mlkem_filter48_bindings.

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

equiv aux_invntt_xkem :
  Jkem_avx2_stack.M._poly_invntt ~ Xkem_avx2.M._poly_invntt : ={arg} ==> ={res}.
proc.
  by unroll for {1} ^while; unroll for {2} ^while; sim.
qed.

lemma mlkem_kg_equiv:
  equiv [Jkem_avx2_stack.M.jade_kem_mlkem_mlkem768_amd64_avx2_keypair_derand ~ Xkem_avx2.M.jade_kem_mlkem_mlkem768_amd64_avx2_keypair_derand: ={arg} ==> ={res}].
proof. by sim. qed.

lemma mlkem_enc_equiv:
  equiv [Jkem_avx2_stack.M.jade_kem_mlkem_mlkem768_amd64_avx2_enc_derand ~ Xkem_avx2.M.jade_kem_mlkem_mlkem768_amd64_avx2_enc_derand: ={arg} ==> ={res}].
proof. 
proc => />; inline __crypto_kem_enc_jazz __indcpa_enc.
sim (Jkem_avx2_stack.M._poly_invntt ~ Xkem_avx2.M._poly_invntt : (true)).
by apply aux_invntt_xkem.
qed.

lemma mlkem_dec_equiv:
  equiv [Jkem_avx2_stack.M.jade_kem_mlkem_mlkem768_amd64_avx2_dec ~ Xkem_avx2.M.jade_kem_mlkem_mlkem768_amd64_avx2_dec: ={arg} ==> ={res}].
proof.
proc => />; inline __crypto_kem_dec_jazz __indcpa_dec.
sim (Jkem_avx2_stack.M._poly_invntt ~ Xkem_avx2.M._poly_invntt : (true)).
by apply aux_invntt_xkem.
qed.


lemma eq_xwing_clean_kg:
  equiv [Xkem_avx2_clean.M.jade_kem_xwing_xwing_amd64_avx2_keypair_derand ~ Xkem_avx2.M.jade_kem_xwing_xwing_amd64_avx2_keypair_derand : ={arg} ==> ={res}].
proof.
proc => />; wp; sp.
inline {1} 1; inline {2} 1.
by sim (Jkem_avx2_stack.M.jade_kem_mlkem_mlkem768_amd64_avx2_keypair_derand ~ Xkem_avx2.M.jade_kem_mlkem_mlkem768_amd64_avx2_keypair_derand : true).
qed.

lemma eq_xwing_clean_enc:
  equiv [Xkem_avx2_clean.M.jade_kem_xwing_xwing_amd64_avx2_enc_derand ~ Xkem_avx2.M.jade_kem_xwing_xwing_amd64_avx2_enc_derand : ={arg} ==> ={res}].
proof.
proc => />; wp; sp.
inline {1} 1. inline {2} 1.
sim (Jkem_avx2_stack.M.jade_kem_mlkem_mlkem768_amd64_avx2_enc_derand ~ Xkem_avx2.M.jade_kem_mlkem_mlkem768_amd64_avx2_enc_derand : true).
by proc *; call mlkem_enc_equiv; auto => />.
qed.

lemma eq_xwing_clean_dec:
  equiv [Xkem_avx2_clean.M.jade_kem_xwing_xwing_amd64_avx2_dec ~ Xkem_avx2.M.jade_kem_xwing_xwing_amd64_avx2_dec : ={arg} ==> ={res}].
proof.
proc => />; wp; sp.
inline {1} 1. inline {2} 1.
sim (Jkem_avx2_stack.M.jade_kem_mlkem_mlkem768_amd64_avx2_dec ~ Xkem_avx2.M.jade_kem_mlkem_mlkem768_amd64_avx2_dec : true).
by proc *; call mlkem_dec_equiv; auto => />.
qed.

lemma xwing_25519_base_mulx_equiv :
  equiv [Xkem_avx2_clean.M.xwing_x25519_base ~ Mulx_scalarmult_s.M.__curve25519_mulx_base :
    _k{2} = toRep4 np{1}
    ==>
    res{2} = toRep4 res{1}].
proof.
proc.
inline{1} 4.
seq 7 3 : (={u, r, k, _k}). 
 wp; auto => /> &1.
 rewrite /copy64 tP => i ib.
 rewrite unpack64E pack32E /init8 of_listE /get8 /(\bits64).
 rewrite !initiE 1,2:/# /=.
 rewrite get64E pack8E !initiE 1:/# //=.
 rewrite /to_list /mkseq -iotaredE => />.
 rewrite wordP => ii iib.
 by rewrite !initiE 1,2:/# //= !initiE 1,2:/# //= !initiE 1,2:/# //= /#.
seq 4 3 : (={u, k, _k, r} /\ q{1} = r{2}). 
 sim.
 wp; skip => /> &2.
 rewrite unpack64E pack32E of_listE.
 rewrite tP => i ib.
 rewrite initiE 1:/# /= /get8 /(\bits64).
 rewrite initiE 1:/# /= /copy_64.
 rewrite wordP => ii iib.
 rewrite initiE 1:/# /= /init64 /(\bits8).
 rewrite initiE 1:/# //= initiE 1:/# //=.
 rewrite /to_list /mkseq -iotaredE => />.
 smt(W8.initiE).
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
 move => &1 &2 [?] [H] *; rewrite H.
 rewrite unpack64E pack32E /init8 of_listE.
 rewrite tP => i ib.
 rewrite /get8 /(\bits64) /copy_64.
 rewrite initiE 1:/# /= initiE 1:/# /=.
 rewrite /to_list /init64 /(\bits8) /get64_direct /mkseq -iotaredE => />.
 rewrite wordP => ii iib.
 rewrite initiE 1:/# /= initiE 1:/# //= initiE 1:/# //=.
 ring. 
 smt(W8.initiE).
auto => /> &1 *; do split.
 rewrite unpack64E pack32E of_listE.
 rewrite tP => i ib.
 rewrite /get8 /(\bits64) /copy_64 /get64_direct /init64 /(\bits8) /pack8_t.
 rewrite !initiE 1,2:/# /= !initiE 1:/# /=.
 rewrite wordP => ii iib.
 rewrite !initiE 1,2:/# /= !initiE 1,2:/# //=  initiE 1:/# //= initiE 1:/# //=.
 by rewrite /to_list /mkseq -iotaredE => /> /#.
rewrite unpack64E pack32E of_listE.
rewrite tP => i ib.
rewrite /get8 /(\bits64) /copy_64 /get64_direct /init64 /(\bits8) /pack8_t.
rewrite !initiE 1,2:/# /= !initiE 1:/# /=.
rewrite wordP => ii iib.
rewrite !initiE 1,2:/# /= !initiE 1,2:/# //=  initiE 1:/# //= initiE 1:/# //=.
by rewrite /to_list /mkseq -iotaredE => /> /#.
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
+ move => &1.
  exists(toRep4 np{1}).
  do split.
  rewrite of_listK.
   by rewrite size_to_list //=. 
  by rewrite to_listK /#.
+ move => &1; rewrite of_listK.
   by rewrite size_to_list //= /#.
  smt().
+ by proc *; call xwing_25519_base_mulx_equiv.
by proc *; symmetry; call eq_spec_impl_scalarmult_base_mulx.
qed.

lemma eq_spec_xwing_25519_mulx :
   equiv [Xkem_avx2_clean.M.xwing_x25519 ~ CurveProcedures.scalarmult :
       k'{2} = pack32 (to_list np{1}) /\
       u'{2} = pack32 (to_list pp{1})
       ==>
       res{2} = pack32 (to_list res{1})].
proof.
transitivity
  Mulx_scalarmult_s.M.__curve25519_mulx
  (toRep4 np{1} = _k{2} /\ toRep4 pp{1} = _u{2}
   ==> toRep4 res{1} = res{2})
  (pack4 (to_list _k{1}) = k'{2} /\
   pack4 (to_list _u{1}) = u'{2}
   ==> pack4 (to_list res{1}) = res{2}) => />.
+ move => &1 &2 H H0.
  exists(toRep4 np{1}, toRep4 pp{1}).
  do split.
   by rewrite -H //= of_listK //=.
  by rewrite -H0 //= of_listK //=.
+ by move => &1; rewrite of_listK //=  of_listK //=.
+ by proc *; call xwing_25519_mulx_equiv.
by proc *; symmetry; call eq_spec_impl_scalarmult_mulx.
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
proc => /=.
inline {2} 1.
seq 14 2: (skp{1}=sk{2} /\ expanded_s{1}=expanded{2}).
 wp; ecall {1} (shake256_A96_A32 expanded{1} randomness{1}).
 cfold {1} ^aux<-.
 wp; while {1} (0 <= i{1} <= 4 /\ sub randomness{1} 0 (8*i{1}) = sub skp{1} 0 (8*i{1}))
               (4-i{1}).
  move=> /> z; auto => /> &m Hi1 _ IH Hi2; split.
   split; first smt().
   rewrite /sub !mulzDr /= !mkseq_add 1..4:/#; congr.
   move: IH; rewrite /sub => ->.
    apply eq_in_mkseq => i Hi /=.
    rewrite !initiE 1:/# get8_set64_directE 1,2:/# ifF 1:/#.
    by rewrite /get8 /init8 initiE /#.
   apply eq_in_mkseq => i Hi /=.
   rewrite !initiE 1:/# get8_set64_directE 1,2:/# ifT 1:/#.
   by rewrite get64E /init8 pack8bE 1:/# !initiE 1:/# /= initiE /#.
  by smt().
 auto => /> &m; split.
  by rewrite /sub !mkseq0.
 move=> /> i skp; split; first smt().
 move=> ???; have ->/=: i=4 by smt().
 move => H; rewrite tP => k Hk.
 by rewrite -(Array32.nth_sub witness skp 0 32 k) 1:// -H nth_sub.
swap {2} [3..4] -2; swap {2} 5 -2.
seq 3 3: (#pre /\ pack32 (to_list pk_x25519{1})=pk_X_256{2}).
 by call eq_spec_xwing_25519_base_mulx; auto => />.
wp; call mlkem_kem_correct_kg; auto => /> &1 &2; split.
 split; rewrite tP => i Hi; rewrite !initiE 1..2:/# //=.
  smt().
 by rewrite initiE /#.
move=> _ _ []pkM1 c11 c12 [][pkM21 pkM22]/= []skM21 skM22 c21 c22 /=.
move=> /> H1 H2; split.
 by rewrite tP => i Hi; rewrite initiE /#.
split.
 by rewrite tP => i Hi; rewrite !initiE 1..3:/# /= ifT /#.
split.
 by rewrite tP => i Hi; rewrite !initiE 1..2:/# /= initiE 1:/# /= ifT /#.
rewrite /of_list.
by apply Array32.all_eq_eq; rewrite /all_eq /to_list !nth_mkseq /#.
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
print copy1216.
proc rewrite {1} ^spkp<-{2} (copy1216).
proc rewrite {1} ^seseed<-{2} (copy64).
seq 12 0 : (#pre /\ spkp{1} = pkp{1} /\ spkp{1} = pkp{1} /\ seseed{1} = eseed{1}).
 by auto => />.
seq 1 1  : (#pre /\ pk_M{2}.`1 = Array1152.init (fun (i:int) => pk_mlkem{1}.[i])
            /\ pk_M{2}.`2 = Array32.init (fun (i:int) => pk_mlkem{1}.[i+1152])
            /\ pk_M{2}.`1 = Array1152.init (fun (i:int) => pkp{1}.[i])
            /\ pk_M{2}.`2 = Array32.init (fun (i:int) => pkp{1}.[i+1152])).
 auto => />; rewrite !tP; move => &1 &2 [#] H H0 H1 H2 H3; do split.
  by move => i ib; rewrite !initiE 1,2:/# H1 1:/#  !initiE 1,2:/#.
 by move => i ib; rewrite !initiE 1:/# //= H2 1:/# !initiE 1,2:/# //=.
seq 1 1  : (#pre /\ pk_X{2} = Array32.init (fun (i:int) => pk_x25519{1}.[i])
            /\ pk_X{2} = Array32.init (fun (i:int) => pkp{1}.[i+1184])).
 auto => />; rewrite !tP; move => &1 &2 [#] H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9.
 by rewrite !initiE 1,2:/# //= H3 1:/# !initiE 1,2:/#.
seq 1 1  : (#pre /\ ek_X{2} = Array32.init (fun (i:int) => ek_x25519{1}.[i])
            /\ ek_X{2} = Array32.init (fun (i:int) => seseed{1}.[i+32])).
 auto => />; rewrite !tP; move => &1 &2 [#] H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
 by  rewrite !initiE 1,2:/# //= H0 1:/# !initiE 1,2:/#.
swap{1} 3 -2.
seq 1 1  : (#pre /\ c_M{2} = seed_mlkem{1}
            /\ c_M{2} = Array32.init (fun (i:int) => seseed{1}.[i])).
 by auto => />.
seq 1 1 : (#pre /\ pack32 (to_list ct_x25519{1}) = ct_X_256{2}).
 call eq_spec_xwing_25519_base_mulx; auto => />.
 move => &1 &2 H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9.
 by congr; congr; congr; rewrite tP => *; smt(Array32.initiE).
seq 1 1 : (#pre /\ pack32 (to_list ss_x25519{1}) = ss_X_256{2}).
 call eq_spec_xwing_25519_mulx; auto => />.
 move => &1 &2 H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9; do split.
  by congr; congr; congr; rewrite tP => *; smt(Array32.initiE).
 by congr; congr; congr; rewrite tP => *; smt(Array32.initiE).
seq 0 1 : (#pre /\ ct_X{2} = ct_x25519{1}).
 auto => />; move => &1 &2 H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9.
 rewrite !/of_list !/to_list !/mkseq -iotaredE => />.
 rewrite tP => i ib.
 by rewrite initiE 1,2:/#.
seq 0 1 : (#pre /\ ss_X{2} = ss_x25519{1}).
 auto => /> &1 &2 H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9.
 rewrite !/of_list !/to_list !/mkseq -iotaredE => />.
 rewrite tP => i ib.
 by rewrite initiE 1,2:/#.
seq 2 3 : (#{~ss_x25519{1}}pre /\ ct_M{2}.`1 = Array960.init(fun i => ct_mlkem{1}.[i])
           /\ ct_M{2}.`2 = Array128.init(fun i => ct_mlkem{1}.[i+960])
           /\ ct{2}.`1.`1 = Array960.init(fun i => ct_mlkem{1}.[i])
           /\ ct{2}.`1.`2 = Array128.init(fun i => ct_mlkem{1}.[i+960])
           /\ ct{2}.`2 = Array32.init (fun i => ct_X{2}.[i])
           /\ ct{2}.`2 = ct_x25519{1}
           /\ ct_x25519{1} = ct_X{2}
           /\ ct_M{2}.`1 = ct{2}.`1.`1
           /\ ct_M{2}.`2 = ct{2}.`1.`2
           /\ ss_M{2} = ss_mlkem{1}
           /\ ss_x25519{1} = ss{2}) => /=.
 inline {2} 2; wp; sp.
 ecall {1} (sha3_256_A128__A6 ss_mlkem{1} ss_x25519{1} ct_x25519{1} pk_x25519{1}).
 call mlkem_kem_correct_enc; auto => />.
 move => /> &1 &2 H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9.
 move=> []ct1 ss1 ? []st2 ss2.
 move=> /> H10 H11.
 split. 
  by rewrite tP => i ib; rewrite initiE 1:// /= /#.
 congr; congr.
 by rewrite tP => i ib; rewrite initiE /#.
conseq (: true ==> 
            ctp{1} = Array1120.init (fun i => if i < 1088 
                                              then ct_mlkem{1}.[i]
                                              else ct_x25519{1}.[i-1088])
            /\ shkp{1} = ss_x25519{1}).
 move=> &1 &2 /> -> -> -> -> -> /=; do split.
 + by rewrite tP=> i Hi; rewrite !initiE /#.
 + by rewrite tP=> i Hi; rewrite !initiE 1..2:// /= initiE /#.
 by rewrite tP=> i Hi; rewrite !initiE 1..2:// /= initiE 1:/# /= initiE /#.
cfold {1} ^aux<-{3}; cfold {1} ^aux<-{2}; cfold {1} ^aux<-.
wp; while {1} (0 <= i{1} <= 4 /\ 
               sub shkp{1} 0 (8*i{1}) = sub ss_x25519{1} 0 (8*i{1})) (4-i{1}) => //=.
 move=> z; auto => /> &m Hi1 _ IH Hi2.
 do split; 1..2,4:smt().
 apply (eq_from_nth witness); first by rewrite !size_sub /#.
 move => i; rewrite size_sub 1:/# => Hi.
 rewrite !mulzDr /=.
 rewrite /sub !mkseq_add 1..4:/#; congr; congr.
  move: IH; rewrite /sub /= => <-.
  apply eq_in_mkseq => k Hk /=.
  rewrite !initiE 1:/# get8_set64_directE 1,2:/# ifF 1:/#.
  by rewrite /get8 /init8 initiE 1:/#.
 apply eq_in_mkseq => k Hk /=.
 rewrite !initiE 1:/# get8_set64_directE 1,2:/# ifT 1:/#.
 by rewrite get64E /init8 pack8bE 1:/# !initiE 1:/# /= initiE /#.
wp; while {1} (0 <= i{1} <= 4 /\ sub ctp{1} 0 1088 = sub ct_mlkem{1} 0 1088 /\
               sub ctp{1} 1088 (8*i{1}) = sub ct_x25519{1} 0 (8*i{1})) (4-i{1}) => //=.
 move=> z; auto => /> &m Hi1 _ IH1 IH2 Hi2.
 do split; 1..2,5:smt().
  rewrite -IH1; apply (eq_from_nth witness); first by rewrite !size_sub /#.
  move=> i; rewrite size_sub /sub 1:/# => Hi.
  rewrite !nth_mkseq 1..2:// /= initiE 1:/# get8_set64_directE 1,2:/# ifF 1:/#.
  by rewrite /get8 /init8 !initiE /#.
 apply (eq_from_nth witness); first by rewrite !size_sub /#.
 move => i; rewrite size_sub 1:/# => Hi.
 rewrite !mulzDr /=.
 rewrite /sub !mkseq_add 1..4:/#; congr; congr.
  move: IH2; rewrite /sub /= => <-.
  apply eq_in_mkseq => k Hk /=.
  rewrite !initiE 1:/# get8_set64_directE 1,2:/# ifF 1:/#.
  by rewrite /get8 /init8 initiE 1:/#.
 apply eq_in_mkseq => k Hk /=.
 rewrite !initiE 1:/# get8_set64_directE 1,2:/# ifT 1:/#.
 by rewrite get64E /init8 pack8bE 1:/# !initiE 1:/# /= initiE /#.
wp; while {1} (0 <= i{1} <= 136 /\ 
               sub ctp{1} 0 (8*i{1}) = sub ct_mlkem{1} 0 (8*i{1})) (136-i{1}) => //=.
 move=> z; auto => /> &m Hi1 _ IH Hi2.
 do split; 1..2,4:smt().
 apply (eq_from_nth witness); first by rewrite !size_sub /#.
 move => i; rewrite size_sub 1:/# => Hi.
 rewrite !mulzDr /=.
 rewrite /sub !mkseq_add 1..4:/#; congr; congr.
  move: IH; rewrite /sub /= => <-.
  apply eq_in_mkseq => k Hk /=.
  rewrite !initiE 1:/# get8_set64_directE 1,2:/# ifF 1:/#.
  by rewrite /get8 /init8 initiE 1:/#.
 apply eq_in_mkseq => k Hk /=.
 rewrite !initiE 1:/# get8_set64_directE 1,2:/# ifT 1:/#.
 by rewrite get64E /init8 pack8bE 1:/# !initiE 1:/# /= initiE /#.
auto => /> &m; split.
 by rewrite /sub !mkseq0.
move=> ctp1 i1 />; split; first smt().
move=> ???; have ->/=: i1=136 by smt().
move=> H1; split.
 by rewrite /sub !mkseq0.
move=> ctp2 i2 />; split; first smt().
move=> ???; have ->/=: i2=4 by smt().
move=> H2 H3; split.
 by rewrite /sub !mkseq0.
move=> i3 shkp />; split; first smt().
move=> ???; have ->/=: i3=4 by smt().
move=> H4; split.
 rewrite tP => k Hk; rewrite initiE 1://.
 case: (k < 1088) => C; rewrite C /=.
  have /=<- := (Array1088.nth_sub witness ct_mlkem{m} 0 1088).
   smt().
  by rewrite -H2 nth_sub 1:/#.
 have /= := (Array1120.nth_sub witness ctp2 1088 32 (k-1088) _).
  smt().
 by rewrite H3 nth_sub /#.
rewrite tP => i Hi.
by rewrite -(Array32.nth_sub witness shkp 0 32 i) 1:// H4 nth_sub /#.
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
proc rewrite {1} ^sctp<-{2} (copy1120).
proc rewrite {1} ^sskp<-{2} (copy32).
inline {2} 1; auto => />.
seq 15 2 : (#pre /\ expanded{1} = SHAKE256_32_96 sskp{1}
            /\ skp{1} = sskp{1}
            /\ sctp{1} = ctp{1}
            /\ ={expanded}
            /\ sskp{1} = sk0{2}
            /\ sskp{1} = sk{2}).
 by ecall {1} (shake256_A96_A32 expanded{1} sskp{1}); wp; skip => />.
swap{1} 3 -2; swap{2} 3 -2.
seq 1 1 : (#pre /\ coins3{2} = expanded_x25519{1}
           /\ coins3{2} = Array32.init(fun (i : int) => expanded{1}.[i + 64])
           /\ coins3{2} = Array32.init(fun (i : int) => expanded{2}.[i + 64])).
 auto => /> &1 &2 [#] H H0 H1; rewrite !tP; do split.
  by move => i ib; rewrite !initiE 1,2:/# //= /#.
 by move => i ib; rewrite !initiE 1,2:/# //= /#.
seq 1 2 : (#pre /\ coins1{2} = Array32.init (fun (i : int ) => expanded_mlkem{1}.[i])
           /\ coins2{2} = Array32.init (fun (i : int ) => expanded_mlkem{1}.[32 + i])
           /\ coins1{2} = Array32.init (fun (i : int ) => expanded{1}.[i])
           /\ coins2{2} = Array32.init (fun (i : int ) => expanded{1}.[32 + i])
           /\ coins1{2} = Array32.init (fun (i : int ) => expanded{2}.[i])
           /\ coins2{2} = Array32.init (fun (i : int ) => expanded{2}.[32+i])).
 auto => />; move => &1 &2 [#] H H0 H1; do split.
  by rewrite tP => i ib; rewrite !initiE 1..5:/# //=.
 by rewrite tP => i ib; rewrite !initiE 1..2:/# //= !initiE 1..3:/# //=.
auto => />.
seq 0 1 : (#pre /\ expanded_x25519{1} = sk_X0{2}
           /\ sk_X0{2} = coins3{2}); auto => />.
swap{1} 1 1.
seq 1 1 : (#pre /\ pack32 (to_list pk_x25519{1}) = pk_X_256{2}).
 by call eq_spec_xwing_25519_base_mulx; auto => />.
seq 0 1 : (#pre /\ pk_x25519{1} = pk_X0{2}
           /\ pk_x25519{1} = Array32.of_list W8.zero (W32u8.to_list pk_X_256{2})); auto => />.
 move => &1 &2 [#] *; rewrite !tP; do split.
  move => i ib; rewrite !/to_list !/mkseq -!iotaredE => />.
  by rewrite !/of_list initiE /#.
 move => i ib; rewrite !/to_list !/mkseq -!iotaredE => />.
 by rewrite !/of_list initiE /#.
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
 by call mlkem_kem_correct_kg; auto => /> /#. 
auto => />.
seq 0 2 : (#pre /\ sk_M{2} = sk_M0{2}
           /\ sk_X{2} = sk_X0{2}
           /\ pk_M{2} = pk_M0{2}
           /\  pk_X{2} = pk_X0{2}); auto => />.
seq 2 2 : (#pre /\ Array960.init (fun (i:int) => ct_mlkem{1}.[i]) = ct_M{2}.`1
           /\ Array128.init (fun (i:int) => ct_mlkem{1}.[i+960]) = ct_M{2}.`2
           /\ ct_x25519{1} = ct_X{2}
           /\ ct_M{2}.`1 = (init (fun (i_0 : int) => sctp{1}.[0 + i_0]))%Array960
           /\ ct_M{2}.`2 = (init (fun (i_0 : int) => sctp{1}.[960 + i_0]))%Array128
           /\ ct_X{2} = (init (fun (i_0 : int) => sctp{1}.[3 * 320 + 128 + i_0]))%Array32).
 wp; auto => /> &1 &2 [#] H H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 ?.
 rewrite !tP; do split.
 + by move => i ib; rewrite H !initiE 1..3:/# //=.
 + by move => i ib; rewrite H1 !initiE 1:/# //= !initiE 1:/# //=.
 + by move => i ib; rewrite H2 !initiE 1:/# //= //= /#.
 + by move => i ib; rewrite H1 !initiE 1:/# //= //= /#.
 + by move => i ib; rewrite H2 !initiE 1:/# //= //= /#.
seq 1 1 : (#pre /\ ss_mlkem{1} = ss_M{2}).
 call mlkem_kem_correct_dec; auto => />.
 move => /> &1 &2 eH H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19.
 rewrite !tP; do split; 1:smt().
 by move => i ib; rewrite H14 1:/#.
seq 1 1 : (#pre /\ pack32 (to_list ss_x25519{1}) = ss_X_256{2} /\ expanded_x25519{1} = sk_X{2}).
 by call eq_spec_xwing_25519_mulx; auto => />.
seq 0 1 : (#pre /\ ss_X{2} = ss_x25519{1}); auto => />.
 rewrite !tP; move => *.
 by rewrite !/of_list !/to_list !/mkseq -!iotaredE => />; rewrite !initiE 1:/# /#.
seq 1 1 : (ss_x25519{1}=ss{2}).
 inline {2} 1; wp; sp.
 ecall {1} (sha3_256_A128__A6 ss_mlkem{1} ss_x25519{1} ct_x25519{1} pk_x25519{1}).
 by wp; skip => />.
cfold {1} ^aux<-.
wp; while {1} (0 <= i{1} <= 4 /\ 
               sub shkp{1} 0 (8*i{1}) = sub ss_x25519{1} 0 (8*i{1})) (4-i{1}) => //=.
 move=> z; auto => /> &m Hi1 _ IH Hi2.
 do split; 1..2,4:smt().
 apply (eq_from_nth witness); first by rewrite !size_sub /#.
 move => i; rewrite size_sub 1:/# => Hi.
 rewrite !mulzDr /=.
 rewrite /sub !mkseq_add 1..4:/#; congr; congr.
  move: IH; rewrite /sub /= => <-.
  apply eq_in_mkseq => k Hk /=.
  rewrite !initiE 1:/# get8_set64_directE 1,2:/# ifF 1:/#.
  by rewrite /get8 /init8 initiE 1:/#.
 apply eq_in_mkseq => k Hk /=.
 rewrite !initiE 1:/# get8_set64_directE 1,2:/# ifT 1:/#.
 by rewrite get64E /init8 pack8bE 1:/# !initiE 1:/# /= initiE /#.
auto => /> &1 &2; split.
 by rewrite /sub !mkseq0.
move=> i shkp />; split; first smt().
move=> ???; have ->/=: i=4 by smt().
move=> H; rewrite tP => k Hk.
by rewrite -(Array32.nth_sub witness shkp 0 32 k) 1:// H nth_sub /#.
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
