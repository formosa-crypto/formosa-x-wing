require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.
require import XWing_Spec XWing_Helper_Functions CorrectnessProof_Mulx Mulx_scalarmult_s Jkem_avx2_stack FIPS202_SHA3 MLKEM.
require import Array4 Array6 Array8 Array32 Array64 Array96 Array140 Array152 Array1088 Array1120 Array1184 Array1216 Array2400.
require import WArray4 WArray6 WArray32 WArray64 WArray96 WArray1088 WArray1120 WArray1184 WArray1216 WArray2400.


op SHA3_256_A128_A6 : W8.t Array32.t -> W8.t Array32.t -> W8.t Array32.t -> W8.t Array32.t -> W8.t Array32.t -> W8.t Array32.t.
op SHAKE256_A96_A32 : W8.t Array96.t -> W8.t Array32.t -> W8.t Array96.t.


axiom sha3_256_A128__A6 ss ss_mlkem ss_x25519 ct_25519 pk_25519 :
   phoare [M._sha3_256_A128__A6 :
               arg = (ss, ss_mlkem, ss_x25519, ct_25519, pk_25519) ==>
               res = SHA3_256_A128_A6 ss ss_mlkem ss_x25519 ct_25519 pk_25519] = 1%r.

axiom shake256_A96_A32 out inp :
   phoare [M._shake256_A96__A32 :
               arg = (out, inp) ==>
               res = SHAKE256_A96_A32 out inp] = 1%r.
