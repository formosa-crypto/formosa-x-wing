require import AllCore Int List.
from Jasmin require import JWord.

require import MLKEM XWing_Helper_Functions.
require import Curve25519_Procedures.
require import Array32 Array96.

module XWing = {

  proc kg_derand(sk: secretkey) : secretkey * publickey = {
        var sk_M, sk_X, pk_M, pk_X, pk;

        (sk_M, sk_X, pk_M, pk_X) <@ XWing_Helper_Functions.expandDecapsulationKey(sk);
        pk <- (pk_M, pk_X);

        return (sk, pk);
  }

  proc enc_derand(pk : publickey, coins: W8.t Array32.t * W8.t Array32.t) : ciphertext * sharedsecret = {
        var pk_M, pk_X, ek_X, ct_X, ct_X_256, ss_X, ss_X_256, ss_M, ct_M, ss, ct, c_M;
        pk_M <- pk.`1;
        pk_X <- pk.`2;
        ek_X <- coins.`2;
        c_M <- coins.`1;

        ct_X_256 <@ CurveProcedures.scalarmult_base(W32u8.pack32 (to_list ek_X));
        ss_X_256 <@ CurveProcedures.scalarmult(W32u8.pack32 (to_list ek_X), W32u8.pack32 (to_list pk_X));

        ct_X <- Array32.of_list W8.zero (W32u8.to_list ct_X_256);
        ss_X <- Array32.of_list W8.zero (W32u8.to_list ss_X_256);

        (ct_M, ss_M) <@ MLKEM.enc_derand(pk_M, c_M);

        ss <@ XWing_Helper_Functions.combiner(ss_M, ss_X, ct_X, pk_X);
        ct <- (ct_M, ct_X);

        return (ct, ss);
  }

  proc dec(cph : ciphertext, sk : secretkey) : sharedsecret = {
        var sk_M, pk_M, sk_X, pk_X, ct_M, ct_X, ss_M, ss_X_256, ss_X, ss;

        (sk_M, sk_X, pk_M, pk_X) <@ XWing_Helper_Functions.expandDecapsulationKey(sk);

        ct_M <- cph.`1;
        ct_X <- cph.`2;

        ss_M <@ MLKEM.dec(ct_M, sk_M);

        ss_X_256 <@ CurveProcedures.scalarmult(W32u8.pack32 (to_list sk_X), W32u8.pack32 (to_list pk_X));
        ss_X <- Array32.of_list W8.zero (W32u8.to_list ss_X_256);

        ss <@ XWing_Helper_Functions.combiner(ss_M, ss_X, ct_X, pk_X);
        return ss;
  }
}.
