require import AllCore List.

require import XWing_Spec XWing_Helper_Functions.
from JazzEC require import Xkem_avx2.

from Jasmin require import JModel.

from CryptoSpecs require import FIPS202_Keccakf1600.
from CryptoSpecs require import Keccakf1600_Spec.

(****************************************************************************)
(****************************************************************************)
from Keccak require import Keccak1600_avx2.

equiv state_init_avx2_eq:
 M.__state_init_avx2 ~ Jazz_avx2.M.__state_init_avx2
 : ={arg} ==> ={res}
 by sim.

equiv pstate_init_avx2_eq:
 M.__pstate_init_avx2 ~ Jazz_avx2.M.__pstate_init_avx2
 : ={arg} ==> ={res}
 by sim.

(****************************************************************************)
(****************************************************************************)

from Keccak require Keccak1600_array_avx2.

(****************************************************************************)
from JazzEC require import Array6 WArray6.

clone Keccak1600_array_avx2.KeccakArrayAvx2 as A6avx2
 with op aSIZE <- 6,
      theory A <- Array6,
      theory WA <- WArray6
      proof aSIZE_ge0 by done.

equiv a6__pabsorb_array_avx2_eq:
 M.a6____pabsorb_array_avx2 ~ A6avx2.M(A6avx2.P).__pabsorb_array_avx2
 : ={arg} ==> ={res}
 by sim.

(****************************************************************************)
from JazzEC require import Array32 WArray32.

clone Keccak1600_array_avx2.KeccakArrayAvx2 as A32avx2
 with op aSIZE <- 32,
      theory A <- Array32,
      theory WA <- WArray32
      proof aSIZE_ge0 by done.

equiv a32__pabsorb_array_avx2_eq:
 M.a32____pabsorb_array_avx2 ~ A32avx2.M(A32avx2.P).__pabsorb_array_avx2
 : ={arg} ==> ={res}
 by sim.

equiv a32__squeeze_array_avx2_eq:
 M.a32____squeeze_array_avx2 ~ A32avx2.M(A32avx2.P).__squeeze_array_avx2
 : ={arg} ==> ={res}
 by sim.

(****************************************************************************)
from JazzEC require import Array96 WArray96.

clone Keccak1600_array_avx2.KeccakArrayAvx2 as A96avx2
 with op aSIZE <- 96,
      theory A <- Array96,
      theory WA <- WArray96
      proof aSIZE_ge0 by done.

equiv a96__squeeze_array_avx2_eq:
 M.a96____squeeze_array_avx2 ~ A96avx2.M(A96avx2.P).__squeeze_array_avx2
 : ={arg} ==> ={res}
 by sim.

(****************************************************************************)
(****************************************************************************)
(****************************************************************************)

from JazzEC require import Array6 Array7.

abbrev xWING_LABEL = (Array6.of_list witness
  [(W8.of_int 92); (W8.of_int 46); (W8.of_int 47); (W8.of_int 47); (W8.of_int 94); (W8.of_int 92)]).

module K = {
  proc _shake256_A96__A32(out : W8.t Array96.t, in_0 : W8.t Array32.t) :
    W8.t Array96.t = {
    var st : W256.t Array7.t;
    var offset : W64.t;
    var _0 : W64.t;
    var _1 : W256.t Array7.t;
    
    _1 <- witness;
    st <- witness;
    st <@ Jazz_avx2.M.__state_init_avx2();
    offset <- W64.zero;
    (st, _0) <@ A32avx2.M(A32avx2.P).__absorb_array_avx2(st, in_0, offset, 32, 136, 31);
    offset <- W64.zero;
    (out, _1) <@ A96avx2.M(A96avx2.P).__squeeze_array_avx2(out, offset, 96, st, 136);
    
    return out;
  }
  proc _sha3_256_A128__A6(ss_x25519 : W8.t Array32.t, ss_mlkem : W8.t Array32.t, ct_x25519 : W8.t Array32.t, pk_x25519 : W8.t Array32.t) :
    W8.t Array32.t = {
    var pst : W64.t Array25.t;
    var st : W256.t Array7.t;
    var offset : W64.t;
    var _0 : int;
    var _1 : W64.t;
    var _2 : int;
    var _3 : W64.t;
    var _4 : int;
    var _5 : W64.t;
    var _6 : int;
    var _7 : W64.t;
    var _8 : int;
    var _9 : W64.t;
    var _10 : W256.t Array7.t;
    
    _10 <- witness;
    pst <- witness;
    st <- witness;
    (pst, st) <@ Jazz_avx2.M.__pstate_init_avx2(pst);
    offset <- W64.zero;
    (pst, _0, st, _1) <@
      A32avx2.M(A32avx2.P).__pabsorb_array_avx2(pst, 0, st, ss_mlkem, offset, 32, 136, 0);
    offset <- W64.zero;
    (pst, _2, st, _3) <@
      A32avx2.M(A32avx2.P).__pabsorb_array_avx2(pst, 32, st, ss_x25519, offset, 32, 136, 0);
    offset <- W64.zero;
    (pst, _4, st, _5) <@
      A32avx2.M(A32avx2.P).__pabsorb_array_avx2(pst, 64, st, ct_x25519, offset, 32, 136, 0);
    offset <- W64.zero;
    (pst, _6, st, _7) <@
      A32avx2.M(A32avx2.P).__pabsorb_array_avx2(pst, 96, st, pk_x25519, offset, 32, 136, 0);
    offset <- W64.zero;
    (pst, _8, st, _9) <@
      A6avx2.M(A6avx2.P).__pabsorb_array_avx2(pst, 128, st, xWING_LABEL, offset, 6, 136, 6);
    offset <- W64.zero;
    (ss_x25519, _10) <@
      A32avx2.M(A32avx2.P).__squeeze_array_avx2(ss_x25519, offset, 32, st, 136);
    
    return ss_x25519;
  }
}.


(*********************************************************************************)
equiv shake256_A96__A32_eq:
  M._shake256_A96__A32 ~ K._shake256_A96__A32
 : ={arg} ==> ={res}
by sim.

hoare shake256_A96__A32_h' out inp :
 K._shake256_A96__A32
 : arg = (out, inp)
 ==> res = SHAKE256_32_96 inp.
proof.
proc.
ecall (A96avx2.squeeze_array_avx2_h out offset 96 st 136).
wp; ecall (A32avx2.absorb_array_avx2_h st in_0 offset 32 136 31).
wp; call state_init_avx2_h.
auto => |> [st ?] /= -> _ [out0 st2] /= -> Hst2.
rewrite stavx2_from_st25K -(Array96.of_listK W8.zero (SQUEEZE1600 136 96 _)).
 by rewrite size_SQUEEZE1600 /#.
rewrite tP => i Hi.
rewrite initiE // filliE //= Hi /=.
congr; rewrite /SHAKE256 /c512_r8 /KECCAK1600 of_listK ?size_SQUEEZE1600 1..3://.
congr; congr; first smt().
by apply eq_in_mkseq => k Hk /=.
qed.

lemma shake256_A96__A32_ll: islossless K._shake256_A96__A32.
proof.
proc.
call A96avx2.squeeze_array_avx2_ll.
wp; call A32avx2.absorb_array_avx2_ll.
wp; call state_init_avx2_ll.
by auto.
qed.

phoare shake256_A96__A32_ph' out inp :
 [ K._shake256_A96__A32
 : arg = (out, inp)
 ==> res = SHAKE256_32_96 inp
 ] = 1%r.
proof. by conseq shake256_A96__A32_ll (shake256_A96__A32_h' out inp). qed.

phoare shake256_A96_A32 out inp :
 [ M._shake256_A96__A32
 : arg = (out, inp)
 ==> res = SHAKE256_32_96 inp
 ] = 1%r.
proof.
by conseq shake256_A96__A32_eq (shake256_A96__A32_ph' out inp) => /> /#.
qed.


(*********************************************************************************)
equiv sha3_256_A128__A6_eq:
  M._sha3_256_A128__A6 ~ K._sha3_256_A128__A6
 : ={arg} ==> ={res}
by sim.

hoare sha3_256_A128__A6_h' _ss_mlkem _ss_x25519 _ct_25519 _pk_25519 :
 K._sha3_256_A128__A6
 : arg = (_ss_x25519, _ss_mlkem, _ct_25519, _pk_25519)
 ==> res = SHA3_256_134_32 (_ss_mlkem, _ss_x25519, _ct_25519, _pk_25519, xwing_label).
proof.
proc => /=.
ecall (A32avx2.squeeze_array_avx2_h ss_x25519 W64.zero 32 st 136) => /=.
wp; ecall (A6avx2.pabsorb_array_avx2_h (to_list ss_mlkem++to_list ss_x25519++to_list ct_x25519++to_list pk_x25519) Top.xWING_LABEL W64.zero 6 136 6).
wp; ecall (A32avx2.pabsorb_array_avx2_h (to_list ss_mlkem++to_list ss_x25519++to_list ct_x25519) pk_x25519 W64.zero 32 136 0).
wp; ecall (A32avx2.pabsorb_array_avx2_h (to_list ss_mlkem++to_list ss_x25519) ct_x25519 W64.zero 32 136 0).
wp; ecall (A32avx2.pabsorb_array_avx2_h (to_list ss_mlkem) ss_x25519 W64.zero 32 136 0).
wp; ecall (A32avx2.pabsorb_array_avx2_h [<:W8.t>] ss_mlkem W64.zero 32 136 0) => /=.
wp; call (pstate_init_avx2_h 136).
auto => |> [pst0 st0] /= H0 []pst1 at1 st1 off1 /= H1'.
move => |>; rewrite size_to_list 1:// /=.
move=> H1 []pst2 at2 st2 off2 /= -> ??; rewrite !size_cat !size_to_list /=.
move=> []pst3 at3 st3 off3 /= -> ??_.
move=> []pst4 at4 st4 off4 /= -> ??_.
move=> []pst5 at5 st5 off5 /= -> [r1 st] /= ->; rewrite !stavx2_from_st25K => E.
rewrite tP => i Hi.
rewrite filliE 1:// initiE 1:// /= Hi /=; congr.
rewrite /SHA3_256 /KECCAK1600; congr; 1:smt().
congr; 1..2:smt().
congr; apply eq_in_mkseq => k Hk /=.
by rewrite !initiE /#.
qed.

lemma sha3_256_A128__A6_ll: islossless K._sha3_256_A128__A6.
proc.
call A32avx2.squeeze_array_avx2_ll.
wp; call A6avx2.pabsorb_array_avx2_ll.
wp; call A32avx2.pabsorb_array_avx2_ll.
wp; call A32avx2.pabsorb_array_avx2_ll.
wp; call A32avx2.pabsorb_array_avx2_ll.
wp; call A32avx2.pabsorb_array_avx2_ll.
wp; call pstate_init_avx2_ll.
by auto => />.
qed.

phoare sha3_256_A128__A6_ph' ss_mlkem ss_x25519 ct_25519 pk_25519 :
 [ K._sha3_256_A128__A6
 : arg = (ss_x25519, ss_mlkem, ct_25519, pk_25519)
 ==> res = SHA3_256_134_32 (ss_mlkem, ss_x25519, ct_25519, pk_25519, xwing_label)
 ] = 1%r.
proof.
by conseq sha3_256_A128__A6_ll (sha3_256_A128__A6_h' ss_mlkem ss_x25519 ct_25519 pk_25519).
qed.

phoare sha3_256_A128__A6 ss_mlkem ss_x25519 ct_25519 pk_25519 :
 [ M._sha3_256_A128__A6
 : arg = (ss_x25519, ss_mlkem, ct_25519, pk_25519)
 ==> res = SHA3_256_134_32 (ss_mlkem, ss_x25519, ct_25519, pk_25519, xwing_label)
 ] = 1%r.
proof.
by conseq sha3_256_A128__A6_eq (sha3_256_A128__A6_ph' ss_mlkem ss_x25519 ct_25519 pk_25519) => /> /#.
qed.
