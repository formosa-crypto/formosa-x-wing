require import AllCore Int List.
from Jasmin require import JWord.

require import MLKEM Curve25519_Procedures Keccak1600_Spec.
require import Array128 Array32 Array6 Array96.

type X25519_publickey = W8.t Array32.t.
type X25519_secretkey = W8.t Array32.t.
type X25519_ciphertext = W8.t Array32.t.
type X25519_sharedsecret = W8.t Array32.t.

type publickey = Top.MLKEM.publickey * X25519_publickey.
type secretkey = W8.t Array32.t.
type sharedsecret = W8.t Array32.t.
type ciphertext = Top.MLKEM.ciphertext * X25519_ciphertext.
type expandedSecretKey = Top.MLKEM.secretkey * X25519_secretkey * Top.MLKEM.publickey * X25519_publickey.

op SHA3_256_134_32 (x: W8.t Array6.t * W8.t Array32.t * W8.t Array32.t * W8.t Array32.t * W8.t Array32.t): W8.t Array32.t =
    Array32.of_list W8.zero (SHA3_256 (to_list x.`1 ++ to_list x.`2 ++ to_list x.`3 ++ to_list x.`4 ++ to_list x.`5)).

op SHAKE256_32_96 (x: W8.t Array32.t): W8.t Array96.t =
    Array96.of_list W8.zero (SHAKE256 (to_list x) 96).

abbrev xwing_label = Array6.of_list witness [W8.of_int 92; W8.of_int 46; W8.of_int 47; W8.of_int 47; W8.of_int 94; W8.of_int 92].

module XWing_Helper_Functions = {

    proc expandDecapsulationKey(sk : secretkey) : expandedSecretKey  = {
        var expanded, coins1, coins2, coins3, pk_M, sk_M, pk_X_256, pk_X, sk_X, k;

        expanded <- SHAKE256_32_96(sk);

        coins1 <- Array32.init (fun (i: int) => expanded.[0 + i]);
        coins2 <- Array32.init (fun (i: int) => expanded.[32 + i]);
        coins3 <- Array32.init (fun (i: int) => expanded.[64 + i]);

        (pk_M, sk_M) <@ MLKEM.kg_derand(coins1, coins2);

        sk_X <- coins3;
        pk_X_256 <@ CurveProcedures.scalarmult_base(W32u8.pack32 (to_list sk_X));
        pk_X <- Array32.of_list W8.zero (W32u8.to_list pk_X_256);

        k <- (sk_M, sk_X, pk_M, pk_X);
        return k;
    }


    proc combiner(ss_M : Top.MLKEM.sharedsecret, ss_X : X25519_sharedsecret, ct_X : X25519_ciphertext, pk_X : X25519_publickey) : sharedsecret =
    {
        var ss;
        ss <- SHA3_256_134_32(xwing_label, ss_M, ss_X, ct_X, pk_X);
        return ss;
    }
}.
