require import Xkem_avx2_clean XWing_Spec.

axiom shake256_A96_A32 out inp :
  phoare [Xkem_avx2_clean.M._shake256_A96__A32 :
               arg = (out, inp) ==>
               res = SHAKE256_32_96 inp] = 1%r.

axiom sha3_256_A128__A6 ss ss_mlkem ss_x25519 ct_25519 pk_25519 :
   phoare [Xkem_avx2_clean.M._sha3_256_A128__A6 :
               arg = (ss, ss_mlkem, ss_x25519, ct_25519, pk_25519) ==>
               res = SHA3_256_134_32 (ss_mlkem, ss_x25519, ct_25519, pk_25519, xwing_label)] = 1%r.

