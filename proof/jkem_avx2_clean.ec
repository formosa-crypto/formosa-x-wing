require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.
require import CorrectnessProof_Mulx Mulx_scalarmult_s Jkem_avx2_stack FIPS202_SHA3.
require import Array4 Array6 Array8 Array32 Array64 Array96 Array140 Array152 Array1088 Array1120 Array1184 Array1216 Array2400.
require import WArray4 WArray6 WArray32 WArray64 WArray96 WArray1088 WArray1120 WArray1184 WArray1216 WArray2400.

abbrev xWING_LABEL =
(Array6.of_list witness
[(W8.of_int 92); (W8.of_int 46); (W8.of_int 47); (W8.of_int 47);
(W8.of_int 94); (W8.of_int 92)]).

module M = {

  proc _shake256_A96__A32 (out:W8.t Array96.t, in_0:W8.t Array32.t) :
  W8.t Array96.t = {
      var trash;
      return trash;
  }

   proc _sha3_256_A128__A6 (ss: W8.t Array32.t, ss_m: W8.t Array32.t,  ssx: W8.t Array32.t, ct_x: W8.t Array32.t, pk_x:  W8.t Array32.t) : W8.t Array32.t = {
      var trash;
      return trash;
  }

  proc xwing_x25519_base (qp:W8.t Array32.t, np:W8.t Array32.t) : W8.t Array32.t = {
    var n:W64.t Array4.t;
    var q:W64.t Array4.t;
    n <- witness;
    q <- witness;
    (* Erased call to spill *)
    n <-
    (copy_64
    (Array4.init (fun i => (get64 (WArray32.init8 (fun i => np.[i])) i))));
    q <@ Mulx_scalarmult_s.M.__curve25519_mulx_base (n);
    (* Erased call to unspill *)
    qp <-
    (Array32.init
    (fun i => (get8 (WArray32.init64 (fun i => (copy_64 q).[i])) i)));
    return qp;
  }
  proc xwing_x25519 (qp:W8.t Array32.t, np:W8.t Array32.t, pp:W8.t Array32.t) :
  W8.t Array32.t = {
    var p:W64.t Array4.t;
    var n:W64.t Array4.t;
    var q:W64.t Array4.t;
    n <- witness;
    p <- witness;
    q <- witness;
    (* Erased call to spill *)
    p <-
    (copy_64
    (Array4.init (fun i => (get64 (WArray32.init8 (fun i => pp.[i])) i))));
    n <-
    (copy_64
    (Array4.init (fun i => (get64 (WArray32.init8 (fun i => np.[i])) i))));
    q <@ Mulx_scalarmult_s.M.__curve25519_mulx (n, p);
    (* Erased call to unspill *)
    qp <-
    (Array32.init
    (fun i => (get8 (WArray32.init64 (fun i => (copy_64 q).[i])) i)));
    return qp;
  }
  proc _crypto_xkem_keypair_derand_jazz (pkp:W8.t Array1216.t, skp:W8.t Array32.t, randomness:W8.t Array32.t) :
  W8.t Array1216.t * W8.t Array32.t = {
    var aux:int;
    var srandomness:W8.t Array32.t;
    var expanded:W8.t Array96.t;
    var expanded_x25519:W8.t Array32.t;
    var pk_x25519:W8.t Array32.t;
    var expanded_mlkem:W8.t Array64.t;
    var pk_mlkem:W8.t Array1184.t;
    var sk_mlkem:W8.t Array2400.t;
    var i:int;
    var t64:W64.t;
    expanded <- witness;
    expanded_mlkem <- witness;
    expanded_x25519 <- witness;
    pk_mlkem <- witness;
    pk_x25519 <- witness;
    sk_mlkem <- witness;
    srandomness <- witness;
    (* Erased call to spill *)
    srandomness <-
    (Array32.init
    (fun i_0 => (get8
                (WArray32.init64
                (fun i_0 => (copy_64
                            (Array4.init
                            (fun i_0 => (get64
                                        (WArray32.init8
                                        (fun i_0 => randomness.[i_0]))
                                        i_0))
                            )).[i_0])
                ) i_0))
    );
    expanded <@ _shake256_A96__A32 (expanded, srandomness);
    expanded_x25519 <-
    (Array32.init (fun i_0 => expanded.[((32 + 32) + i_0)]));
    pk_x25519 <@ xwing_x25519_base (pk_x25519, expanded_x25519);
    expanded_mlkem <- (Array64.init (fun i_0 => expanded.[(0 + i_0)]));
    (pk_mlkem, sk_mlkem) <@ Jkem_avx2_stack.M.__crypto_kem_keypair_jazz (pk_mlkem, sk_mlkem, expanded_mlkem);
    (* Erased call to unspill *)
    aux <- (((3 * 384) + 32) %/ 8);
    i <- 0;
    while ((i < aux)) {
      t64 <- (get64 (WArray1184.init8 (fun i_0 => pk_mlkem.[i_0])) i);
      pkp <-
      (Array1216.init
      (WArray1216.get8
      (WArray1216.set64 (WArray1216.init8 (fun i_0 => pkp.[i_0])) i t64)));
      i <- (i + 1);
    }
    aux <- (32 %/ 8);
    i <- 0;
    while ((i < aux)) {
      t64 <- (get64 (WArray32.init8 (fun i_0 => pk_x25519.[i_0])) i);
      pkp <-
      (Array1216.init
      (WArray1216.get8
      (WArray1216.set64 (WArray1216.init8 (fun i_0 => pkp.[i_0]))
      ((((3 * 384) + 32) %/ 8) + i) t64)));
      i <- (i + 1);
    }
    aux <- (32 %/ 8);
    i <- 0;
    while ((i < aux)) {
      t64 <- (get64 (WArray32.init8 (fun i_0 => srandomness.[i_0])) i);
      skp <-
      (Array32.init
      (WArray32.get8
      (WArray32.set64 (WArray32.init8 (fun i_0 => skp.[i_0])) i t64)));
      i <- (i + 1);
    }
    return (pkp, skp);
  }
  proc _crypto_xkem_enc_derand_jazz (ctp:W8.t Array1120.t, shkp:W8.t Array32.t, pkp:W8.t Array1216.t, eseed:W8.t Array64.t) : W8.t Array1120.t * W8.t Array32.t = {
    var aux:int;
    var spkp:W8.t Array1216.t;
    var seseed:W8.t Array64.t;
    var pk_mlkem:W8.t Array1184.t;
    var pk_x25519:W8.t Array32.t;
    var ek_x25519:W8.t Array32.t;
    var ct_x25519:W8.t Array32.t;
    var ss_x25519:W8.t Array32.t;
    var seed_mlkem:W8.t Array32.t;
    var ct_mlkem:W8.t Array1088.t;
    var ss_mlkem:W8.t Array32.t;
    var ss:W8.t Array32.t;
    var i:int;
    var t64:W64.t;
    ct_mlkem <- witness;
    ct_x25519 <- witness;
    ek_x25519 <- witness;
    pk_mlkem <- witness;
    pk_x25519 <- witness;
    seed_mlkem <- witness;
    seseed <- witness;
    spkp <- witness;
    ss <- witness;
    ss_mlkem <- witness;
    ss_x25519 <- witness;
    (* Erased call to spill *)
    spkp <-
    (Array1216.init
    (fun i_0 => (get8
                (WArray1216.init64
                (fun i_0 => (copy_64
                            (Array152.init
                            (fun i_0 => (get64
                                        (WArray1216.init8
                                        (fun i_0 => pkp.[i_0])) i_0))
                            )).[i_0])
                ) i_0))
    );
    seseed <-
    (Array64.init
    (fun i_0 => (get8
                (WArray64.init64
                (fun i_0 => (copy_64
                            (Array8.init
                            (fun i_0 => (get64
                                        (WArray64.init8
                                        (fun i_0 => eseed.[i_0])) i_0))
                            )).[i_0])
                ) i_0))
    );
    pk_mlkem <- (Array1184.init (fun i_0 => spkp.[(0 + i_0)]));
    pk_x25519 <- (Array32.init (fun i_0 => spkp.[(((3 * 384) + 32) + i_0)]));
    ek_x25519 <- (Array32.init (fun i_0 => seseed.[(32 + i_0)]));
    ct_x25519 <@ xwing_x25519_base (ct_x25519, ek_x25519);
    ss_x25519 <@ xwing_x25519 (ss_x25519, ek_x25519, pk_x25519);
    seed_mlkem <- (Array32.init (fun i_0 => seseed.[(0 + i_0)]));
    (ct_mlkem, ss_mlkem) <@ Jkem_avx2_stack.M.__crypto_kem_enc_jazz (ct_mlkem, ss_mlkem, pk_mlkem, seed_mlkem);
    ss <@ _sha3_256_A128__A6 (ss, ss_mlkem, ss_x25519, ct_x25519, pk_x25519);
    (* Erased call to unspill *)
    aux <- (((3 * 320) + 128) %/ 8);
    i <- 0;
    while ((i < aux)) {
      t64 <- (get64 (WArray1088.init8 (fun i_0 => ct_mlkem.[i_0])) i);
      ctp <-
      (Array1120.init
      (WArray1120.get8
      (WArray1120.set64 (WArray1120.init8 (fun i_0 => ctp.[i_0])) i t64)));
      i <- (i + 1);
    }
    aux <- (32 %/ 8);
    i <- 0;
    while ((i < aux)) {
      t64 <- (get64 (WArray32.init8 (fun i_0 => ct_x25519.[i_0])) i);
      ctp <-
      (Array1120.init
      (WArray1120.get8
      (WArray1120.set64 (WArray1120.init8 (fun i_0 => ctp.[i_0]))
      ((((3 * 320) + 128) %/ 8) + i) t64)));
      i <- (i + 1);
    }
    aux <- (32 %/ 8);
    i <- 0;
    while ((i < aux)) {
      t64 <- (get64 (WArray32.init8 (fun i_0 => ss.[i_0])) i);
      shkp <-
      (Array32.init
      (WArray32.get8
      (WArray32.set64 (WArray32.init8 (fun i_0 => shkp.[i_0])) i t64)));
      i <- (i + 1);
    }
    return (ctp, shkp);
  }
  proc _crypto_xkem_dec_jazz (shkp:W8.t Array32.t, ctp:W8.t Array1120.t, skp:W8.t Array32.t) : W8.t Array32.t = {
    var aux:int;
    var sctp:W8.t Array1120.t;
    var sskp:W8.t Array32.t;
    var expanded:W8.t Array96.t;
    var expanded_mlkem:W8.t Array64.t;
    var pk_mlkem:W8.t Array1184.t;
    var sk_mlkem:W8.t Array2400.t;
    var expanded_x25519:W8.t Array32.t;
    var pk_x25519:W8.t Array32.t;
    var ct_mlkem:W8.t Array1088.t;
    var ct_x25519:W8.t Array32.t;
    var ss_mlkem:W8.t Array32.t;
    var ss_x25519:W8.t Array32.t;
    var ss:W8.t Array32.t;
    var i:int;
    var t64:W64.t;
    ct_mlkem <- witness;
    ct_x25519 <- witness;
    expanded <- witness;
    expanded_mlkem <- witness;
    expanded_x25519 <- witness;
    pk_mlkem <- witness;
    pk_x25519 <- witness;
    sctp <- witness;
    sk_mlkem <- witness;
    ss <- witness;
    ss_mlkem <- witness;
    ss_x25519 <- witness;
    sskp <- witness;
    (* Erased call to spill *)
    sctp <-
    (Array1120.init
    (fun i_0 => (get8
                (WArray1120.init64
                (fun i_0 => (copy_64
                            (Array140.init
                            (fun i_0 => (get64
                                        (WArray1120.init8
                                        (fun i_0 => ctp.[i_0])) i_0))
                            )).[i_0])
                ) i_0))
    );
    sskp <-
    (Array32.init
    (fun i_0 => (get8
                (WArray32.init64
                (fun i_0 => (copy_64
                            (Array4.init
                            (fun i_0 => (get64
                                        (WArray32.init8
                                        (fun i_0 => skp.[i_0])) i_0))
                            )).[i_0])
                ) i_0))
    );
    expanded <@ _shake256_A96__A32 (expanded, sskp);
    expanded_mlkem <- (Array64.init (fun i_0 => expanded.[(0 + i_0)]));
    (pk_mlkem, sk_mlkem) <@ Jkem_avx2_stack.M.__crypto_kem_keypair_jazz (pk_mlkem, sk_mlkem, expanded_mlkem);
    expanded_x25519 <-
    (Array32.init (fun i_0 => expanded.[((32 + 32) + i_0)]));
    pk_x25519 <@ xwing_x25519_base (pk_x25519, expanded_x25519);
    ct_mlkem <- (Array1088.init (fun i_0 => sctp.[(0 + i_0)]));
    ct_x25519 <-
    (Array32.init (fun i_0 => sctp.[(((3 * 320) + 128) + i_0)]));
    ss_mlkem <@ Jkem_avx2_stack.M.__crypto_kem_dec_jazz (ss_mlkem, ct_mlkem, sk_mlkem);
    ss_x25519 <@ xwing_x25519 (ss_x25519, expanded_x25519, ct_x25519);
    ss <@ _sha3_256_A128__A6 (ss, ss_mlkem, ss_x25519, ct_x25519, pk_x25519);
    (* Erased call to unspill *)
    aux <- (32 %/ 8);
    i <- 0;
    while ((i < aux)) {
      t64 <- (get64 (WArray32.init8 (fun i_0 => ss.[i_0])) i);
      shkp <-
      (Array32.init
      (WArray32.get8
      (WArray32.set64 (WArray32.init8 (fun i_0 => shkp.[i_0])) i t64)));
      i <- (i + 1);
    }
    return shkp;
  }
  proc jade_kem_xwing_xwing_amd64_avx2_keypair_derand (public_key:W8.t Array1216.t, secret_key:W8.t Array32.t , coins:W8.t Array32.t) :
  W8.t Array1216.t * W8.t Array32.t * W64.t = {
    var r:W64.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var  _0:W64.t;
    var  _1:bool;
     _0 <- (init_msf);
    (* Erased call to spill *)
    (public_key, secret_key) <@ _crypto_xkem_keypair_derand_jazz (public_key, secret_key, coins);
    (_of_, _cf_, _sf_,  _1, _zf_, r) <- (set0_64);
    return (public_key, secret_key, r);
  }
  proc jade_kem_xwing_xwing_amd64_avx2_enc_derand (ciphertext:W8.t Array1120.t, shared_secret:W8.t Array32.t, public_key:W8.t Array1216.t, coins:W8.t Array64.t) :
  W8.t Array1120.t * W8.t Array32.t * W64.t = {
    var r:W64.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var  _0:W64.t;
    var  _1:bool;
     _0 <- (init_msf);
    (* Erased call to spill *)
    (ciphertext, shared_secret) <@ _crypto_xkem_enc_derand_jazz (ciphertext, shared_secret, public_key, coins);
    (_of_, _cf_, _sf_,  _1, _zf_, r) <- (set0_64);
    return (ciphertext, shared_secret, r);
  }
  proc jade_kem_xwing_xwing_amd64_avx2_dec (shared_secret:W8.t Array32.t, ciphertext:W8.t Array1120.t, secret_key:W8.t Array32.t) :
  W8.t Array32.t * W64.t = {
    var r:W64.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var  _0:W64.t;
    var  _1:bool;
     _0 <- (init_msf);
    (* Erased call to spill *)
    shared_secret <@ _crypto_xkem_dec_jazz (shared_secret, ciphertext, secret_key);
    (_of_, _cf_, _sf_,  _1, _zf_, r) <- (set0_64);
    return (shared_secret, r);
  }
}.
