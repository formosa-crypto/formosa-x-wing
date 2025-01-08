require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import Array4 Array8 Array32.

require import WArray32 WArray64.

module M = {
  proc __ith_bit (k:W8.t Array32.t, ctr:W64.t) : W64.t = {
    var bit:W64.t;
    var p:W64.t;
    p <- ctr;
    p <- (p `>>` (W8.of_int 3));
    bit <- (zeroextu64 k.[(W64.to_uint p)]);
    p <- ctr;
    p <- (p `&` (W64.of_int 7));
    bit <- (bit `>>` (truncateu8 (p `&` (W64.of_int 63))));
    bit <- (bit `&` (W64.of_int 1));
    return bit;
  }
  proc __decode_scalar (k:W64.t Array4.t) : W8.t Array32.t = {
    var aux:int;
    var ks:W8.t Array32.t;
    var i:int;
    ks <- witness;
    i <- 0;
    while ((i < 4)) {
      ks <-
      (Array32.init
      (WArray32.get8
      (WArray32.set64 (WArray32.init8 (fun i_0 => ks.[i_0])) i k.[i])));
      i <- (i + 1);
    }
    ks.[0] <- (ks.[0] `&` (W8.of_int 248));
    ks.[31] <- (ks.[31] `&` (W8.of_int 127));
    ks.[31] <- (ks.[31] `|` (W8.of_int 64));
    return ks;
  }
  proc __decode_u_coordinate4 (u:W64.t Array4.t) : W64.t Array4.t = {
    
    u.[3] <- (u.[3] `&` (W64.of_int 9223372036854775807));
    return u;
  }
  proc __decode_u_coordinate_base4 () : W64.t Array4.t = {
    var u:W64.t Array4.t;
    u <- witness;
    u.[0] <- (W64.of_int 9);
    u.[1] <- (W64.of_int 0);
    u.[2] <- (W64.of_int 0);
    u.[3] <- (W64.of_int 0);
    return u;
  }
  proc __init_points4 (initr:W64.t Array4.t) : W64.t Array4.t *
                                               W64.t Array4.t *
                                               W64.t Array4.t *
                                               W64.t Array4.t = {
    var aux:int;
    var x2:W64.t Array4.t;
    var z2r:W64.t Array4.t;
    var x3:W64.t Array4.t;
    var z3:W64.t Array4.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var z:W64.t;
    var i:int;
    var  _0:bool;
    x2 <- witness;
    x3 <- witness;
    z2r <- witness;
    z3 <- witness;
    (_of_, _cf_, _sf_,  _0, _zf_, z) <- (set0_64);
    x2.[0] <- (W64.of_int 1);
    z2r.[0] <- (W64.of_int 0);
    x3 <- (copy_64 initr);
    z3.[0] <- (W64.of_int 1);
    i <- 1;
    while ((i < 4)) {
      x2.[i] <- z;
      z2r.[i] <- z;
      z3.[i] <- z;
      i <- (i + 1);
    }
    return (x2, z2r, x3, z3);
  }
  proc __add4_rrs (f:W64.t Array4.t, g:W64.t Array4.t) : W64.t Array4.t = {
    var aux:bool;
    var aux_1:int;
    var aux_0:W64.t;
    var h:W64.t Array4.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var z:W64.t;
    var cf:bool;
    var i:int;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    h <- witness;
    (_of_, _cf_, _sf_,  _0, _zf_, z) <- (set0_64);
    h <- (copy_64 f);
    (aux, aux_0) <- (adc_64 h.[0] g.[0] false);
    cf <- aux;
    h.[0] <- aux_0;
    i <- 1;
    while ((i < 4)) {
      (aux, aux_0) <- (adc_64 h.[i] g.[i] cf);
      cf <- aux;
      h.[i] <- aux_0;
      i <- (i + 1);
    }
    ( _1, z) <- (sbb_64 z z cf);
    z <- (z `&` (W64.of_int 38));
    (aux, aux_0) <- (adc_64 h.[0] z false);
    cf <- aux;
    h.[0] <- aux_0;
    i <- 1;
    while ((i < 4)) {
      (aux, aux_0) <- (adc_64 h.[i] (W64.of_int 0) cf);
      cf <- aux;
      h.[i] <- aux_0;
      i <- (i + 1);
    }
    ( _2, z) <- (sbb_64 z z cf);
    z <- (z `&` (W64.of_int 38));
    h.[0] <- (h.[0] + z);
    return h;
  }
  proc __add4_sss (fs:W64.t Array4.t, gs:W64.t Array4.t) : W64.t Array4.t = {
    var hs:W64.t Array4.t;
    var f:W64.t Array4.t;
    var h:W64.t Array4.t;
    f <- witness;
    h <- witness;
    hs <- witness;
    f <- (copy_64 fs);
    h <@ __add4_rrs (f, gs);
    hs <- (copy_64 h);
    return hs;
  }
  proc __add4_ssr (fs:W64.t Array4.t, g:W64.t Array4.t) : W64.t Array4.t = {
    var hs:W64.t Array4.t;
    var h:W64.t Array4.t;
    h <- witness;
    hs <- witness;
    h <@ __add4_rrs (g, fs);
    hs <- (copy_64 h);
    return hs;
  }
  proc __sub4_rrs (f:W64.t Array4.t, gs:W64.t Array4.t) : W64.t Array4.t = {
    var aux:bool;
    var aux_1:int;
    var aux_0:W64.t;
    var h:W64.t Array4.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var z:W64.t;
    var cf:bool;
    var i:int;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    h <- witness;
    (_of_, _cf_, _sf_,  _0, _zf_, z) <- (set0_64);
    h <- (copy_64 f);
    (aux, aux_0) <- (sbb_64 h.[0] gs.[0] false);
    cf <- aux;
    h.[0] <- aux_0;
    i <- 1;
    while ((i < 4)) {
      (aux, aux_0) <- (sbb_64 h.[i] gs.[i] cf);
      cf <- aux;
      h.[i] <- aux_0;
      i <- (i + 1);
    }
    ( _1, z) <- (sbb_64 z z cf);
    z <- (z `&` (W64.of_int 38));
    (aux, aux_0) <- (sbb_64 h.[0] z false);
    cf <- aux;
    h.[0] <- aux_0;
    i <- 1;
    while ((i < 4)) {
      (aux, aux_0) <- (sbb_64 h.[i] (W64.of_int 0) cf);
      cf <- aux;
      h.[i] <- aux_0;
      i <- (i + 1);
    }
    ( _2, z) <- (sbb_64 z z cf);
    z <- (z `&` (W64.of_int 38));
    h.[0] <- (h.[0] - z);
    return h;
  }
  proc __sub4_sss (fs:W64.t Array4.t, gs:W64.t Array4.t) : W64.t Array4.t = {
    var hs:W64.t Array4.t;
    var f:W64.t Array4.t;
    var h:W64.t Array4.t;
    f <- witness;
    h <- witness;
    hs <- witness;
    f <- (copy_64 fs);
    h <@ __sub4_rrs (f, gs);
    hs <- (copy_64 h);
    return hs;
  }
  proc __sub4_rsr (fs:W64.t Array4.t, g:W64.t Array4.t) : W64.t Array4.t = {
    var aux:bool;
    var aux_1:int;
    var aux_0:W64.t;
    var h:W64.t Array4.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var z:W64.t;
    var cf:bool;
    var i:int;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    h <- witness;
    (_of_, _cf_, _sf_,  _0, _zf_, z) <- (set0_64);
    h <- (copy_64 fs);
    (aux, aux_0) <- (sbb_64 h.[0] g.[0] false);
    cf <- aux;
    h.[0] <- aux_0;
    i <- 1;
    while ((i < 4)) {
      (aux, aux_0) <- (sbb_64 h.[i] g.[i] cf);
      cf <- aux;
      h.[i] <- aux_0;
      i <- (i + 1);
    }
    ( _1, z) <- (sbb_64 z z cf);
    z <- (z `&` (W64.of_int 38));
    (aux, aux_0) <- (sbb_64 h.[0] z false);
    cf <- aux;
    h.[0] <- aux_0;
    i <- 1;
    while ((i < 4)) {
      (aux, aux_0) <- (sbb_64 h.[i] (W64.of_int 0) cf);
      cf <- aux;
      h.[i] <- aux_0;
      i <- (i + 1);
    }
    ( _2, z) <- (sbb_64 z z cf);
    z <- (z `&` (W64.of_int 38));
    h.[0] <- (h.[0] - z);
    return h;
  }
  proc __sub4_ssr (fs:W64.t Array4.t, g:W64.t Array4.t) : W64.t Array4.t = {
    var hs:W64.t Array4.t;
    var h:W64.t Array4.t;
    h <- witness;
    hs <- witness;
    h <@ __sub4_rsr (fs, g);
    hs <- (copy_64 h);
    return hs;
  }
  proc __cswap4 (x2:W64.t Array4.t, z2r:W64.t Array4.t, x3:W64.t Array4.t,
                 z3:W64.t Array4.t, toswap:W64.t) : W64.t Array4.t *
                                                    W64.t Array4.t *
                                                    W64.t Array4.t *
                                                    W64.t Array4.t = {
    var aux:int;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var mask:W64.t;
    var z3r:W64.t Array4.t;
    var t4:W64.t Array4.t;
    var i:int;
    var x3r:W64.t Array4.t;
    var x2r:W64.t Array4.t;
    var t:W64.t;
    var  _0:bool;
    t4 <- witness;
    x2r <- witness;
    x3r <- witness;
    z3r <- witness;
    (_of_, _cf_, _sf_,  _0, _zf_, mask) <- (set0_64);
    mask <- (mask - toswap);
    z3r <- (copy_64 z3);
    t4 <- (copy_64 z2r);
    i <- 0;
    while ((i < 4)) {
      t4.[i] <- (t4.[i] `^` z3r.[i]);
      i <- (i + 1);
    }
    i <- 0;
    while ((i < 4)) {
      t4.[i] <- (t4.[i] `&` mask);
      i <- (i + 1);
    }
    i <- 0;
    while ((i < 4)) {
      z2r.[i] <- (z2r.[i] `^` t4.[i]);
      z3r.[i] <- (z3r.[i] `^` t4.[i]);
      z3.[i] <- z3r.[i];
      i <- (i + 1);
    }
    x3r <- (copy_64 x3);
    i <- 0;
    while ((i < 4)) {
      x2r.[i] <- x2.[i];
      t <- x3r.[i];
      t <- (t `^` x2r.[i]);
      t <- (t `&` mask);
      x2r.[i] <- (x2r.[i] `^` t);
      x3r.[i] <- (x3r.[i] `^` t);
      x2.[i] <- x2r.[i];
      x3.[i] <- x3r.[i];
      i <- (i + 1);
    }
    return (x2, z2r, x3, z3);
  }
  proc __tobytes4 (f:W64.t Array4.t) : W64.t Array4.t = {
    var aux_3:bool;
    var aux_2:bool;
    var aux_1:bool;
    var aux_0:bool;
    var aux:bool;
    var aux_4:W64.t;
    var t:W64.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var cf:bool;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    t <- (LEA_64 (f.[3] + f.[3]));
    (aux_3, aux_2, aux_1, aux_0, aux, aux_4) <-
    (SAR_64 f.[3] (W8.of_int 63));
    _of_ <- aux_3;
    _cf_ <- aux_2;
    _sf_ <- aux_1;
     _0 <- aux_0;
    _zf_ <- aux;
    f.[3] <- aux_4;
    t <- (t `>>` (W8.of_int 1));
    f.[3] <- (f.[3] `&` (W64.of_int 19));
    f.[3] <- (f.[3] + (W64.of_int 19));
    (aux_3, aux_4) <- (adc_64 f.[0] f.[3] false);
    cf <- aux_3;
    f.[0] <- aux_4;
    (aux_3, aux_4) <- (adc_64 f.[1] (W64.of_int 0) cf);
    cf <- aux_3;
    f.[1] <- aux_4;
    (aux_3, aux_4) <- (adc_64 f.[2] (W64.of_int 0) cf);
    cf <- aux_3;
    f.[2] <- aux_4;
    ( _1, t) <- (adc_64 t (W64.of_int 0) cf);
    f.[3] <- (LEA_64 (t + t));
    (_of_, _cf_, _sf_,  _2, _zf_, t) <- (SAR_64 t (W8.of_int 63));
    f.[3] <- (f.[3] `>>` (W8.of_int 1));
    t <- (invw t);
    t <- (t `&` (W64.of_int 19));
    (aux_3, aux_4) <- (sbb_64 f.[0] t false);
    cf <- aux_3;
    f.[0] <- aux_4;
    (aux_3, aux_4) <- (sbb_64 f.[1] (W64.of_int 0) cf);
    cf <- aux_3;
    f.[1] <- aux_4;
    (aux_3, aux_4) <- (sbb_64 f.[2] (W64.of_int 0) cf);
    cf <- aux_3;
    f.[2] <- aux_4;
    (aux_3, aux_4) <- (sbb_64 f.[3] (W64.of_int 0) cf);
     _3 <- aux_3;
    f.[3] <- aux_4;
    return f;
  }
  proc __reduce4 (h:W64.t Array4.t, r:W64.t Array4.t, _38:W64.t, z:W64.t,
                  cf:bool, of_0:bool) : W64.t Array4.t = {
    var aux:bool;
    var aux_1:W64.t;
    var aux_0:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    (hi, lo) <- (MULX_64 _38 r.[0]);
    (aux, aux_1) <- (ADOX_64 h.[0] lo of_0);
    of_0 <- aux;
    h.[0] <- aux_1;
    (aux, aux_1) <- (ADCX_64 h.[1] hi cf);
    cf <- aux;
    h.[1] <- aux_1;
    (hi, lo) <- (MULX_64 _38 r.[1]);
    (aux, aux_1) <- (ADOX_64 h.[1] lo of_0);
    of_0 <- aux;
    h.[1] <- aux_1;
    (aux, aux_1) <- (ADCX_64 h.[2] hi cf);
    cf <- aux;
    h.[2] <- aux_1;
    (hi, lo) <- (MULX_64 _38 r.[2]);
    (aux, aux_1) <- (ADOX_64 h.[2] lo of_0);
    of_0 <- aux;
    h.[2] <- aux_1;
    (aux, aux_1) <- (ADCX_64 h.[3] hi cf);
    cf <- aux;
    h.[3] <- aux_1;
    (aux_1, aux_0) <- (MULX_64 _38 r.[3]);
    r.[0] <- aux_1;
    lo <- aux_0;
    (aux, aux_1) <- (ADOX_64 h.[3] lo of_0);
    of_0 <- aux;
    h.[3] <- aux_1;
    (aux, aux_1) <- (ADCX_64 r.[0] z cf);
    cf <- aux;
    r.[0] <- aux_1;
    (aux, aux_1) <- (ADOX_64 r.[0] z of_0);
    of_0 <- aux;
    r.[0] <- aux_1;
    ( _0,  _1,  _2,  _3,  _4, lo) <- (IMULri_64 r.[0] (W64.of_int 38));
    (aux, aux_1) <- (adc_64 h.[0] lo false);
    cf <- aux;
    h.[0] <- aux_1;
    (aux, aux_1) <- (adc_64 h.[1] z cf);
    cf <- aux;
    h.[1] <- aux_1;
    (aux, aux_1) <- (adc_64 h.[2] z cf);
    cf <- aux;
    h.[2] <- aux_1;
    (aux, aux_1) <- (adc_64 h.[3] z cf);
    cf <- aux;
    h.[3] <- aux_1;
    ( _5, z) <- (sbb_64 z z cf);
    z <- (z `&` (W64.of_int 38));
    h.[0] <- (h.[0] + z);
    return h;
  }
  proc __mul4_c0 (f0:W64.t, g:W64.t Array4.t, z:W64.t, cf:bool, of_0:bool) : 
  W64.t Array4.t * W64.t Array4.t * bool * bool = {
    var aux_1:bool;
    var aux_0:W64.t;
    var aux:W64.t;
    var h:W64.t Array4.t;
    var r:W64.t Array4.t;
    var lo:W64.t;
    h <- witness;
    r <- witness;
    (aux_0, aux) <- (MULX_64 f0 g.[0]);
    h.[1] <- aux_0;
    h.[0] <- aux;
    (aux_0, aux) <- (MULX_64 f0 g.[1]);
    h.[2] <- aux_0;
    lo <- aux;
    (aux_1, aux_0) <- (ADCX_64 h.[1] lo cf);
    cf <- aux_1;
    h.[1] <- aux_0;
    (aux_0, aux) <- (MULX_64 f0 g.[2]);
    h.[3] <- aux_0;
    lo <- aux;
    (aux_1, aux_0) <- (ADCX_64 h.[2] lo cf);
    cf <- aux_1;
    h.[2] <- aux_0;
    (aux_0, aux) <- (MULX_64 f0 g.[3]);
    r.[0] <- aux_0;
    lo <- aux;
    (aux_1, aux_0) <- (ADCX_64 h.[3] lo cf);
    cf <- aux_1;
    h.[3] <- aux_0;
    (aux_1, aux_0) <- (ADCX_64 r.[0] z cf);
    cf <- aux_1;
    r.[0] <- aux_0;
    return (h, r, cf, of_0);
  }
  proc __mul4_c1 (h:W64.t Array4.t, r:W64.t Array4.t, f:W64.t,
                  g:W64.t Array4.t, z:W64.t, cf:bool, of_0:bool) : W64.t Array4.t *
                                                                   W64.t Array4.t *
                                                                   bool *
                                                                   bool = {
    var aux:bool;
    var aux_1:W64.t;
    var aux_0:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    (hi, lo) <- (MULX_64 f g.[0]);
    (aux, aux_1) <- (ADOX_64 h.[1] lo of_0);
    of_0 <- aux;
    h.[1] <- aux_1;
    (aux, aux_1) <- (ADCX_64 h.[2] hi cf);
    cf <- aux;
    h.[2] <- aux_1;
    (hi, lo) <- (MULX_64 f g.[1]);
    (aux, aux_1) <- (ADOX_64 h.[2] lo of_0);
    of_0 <- aux;
    h.[2] <- aux_1;
    (aux, aux_1) <- (ADCX_64 h.[3] hi cf);
    cf <- aux;
    h.[3] <- aux_1;
    (hi, lo) <- (MULX_64 f g.[2]);
    (aux, aux_1) <- (ADOX_64 h.[3] lo of_0);
    of_0 <- aux;
    h.[3] <- aux_1;
    (aux, aux_1) <- (ADCX_64 r.[0] hi cf);
    cf <- aux;
    r.[0] <- aux_1;
    (aux_1, aux_0) <- (MULX_64 f g.[3]);
    r.[1] <- aux_1;
    lo <- aux_0;
    (aux, aux_1) <- (ADOX_64 r.[0] lo of_0);
    of_0 <- aux;
    r.[0] <- aux_1;
    (aux, aux_1) <- (ADCX_64 r.[1] z cf);
    cf <- aux;
    r.[1] <- aux_1;
    (aux, aux_1) <- (ADOX_64 r.[1] z of_0);
    of_0 <- aux;
    r.[1] <- aux_1;
    return (h, r, cf, of_0);
  }
  proc __mul4_c2 (h:W64.t Array4.t, r:W64.t Array4.t, f:W64.t,
                  g:W64.t Array4.t, z:W64.t, cf:bool, of_0:bool) : W64.t Array4.t *
                                                                   W64.t Array4.t *
                                                                   bool *
                                                                   bool = {
    var aux:bool;
    var aux_1:W64.t;
    var aux_0:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    (hi, lo) <- (MULX_64 f g.[0]);
    (aux, aux_1) <- (ADOX_64 h.[2] lo of_0);
    of_0 <- aux;
    h.[2] <- aux_1;
    (aux, aux_1) <- (ADCX_64 h.[3] hi cf);
    cf <- aux;
    h.[3] <- aux_1;
    (hi, lo) <- (MULX_64 f g.[1]);
    (aux, aux_1) <- (ADOX_64 h.[3] lo of_0);
    of_0 <- aux;
    h.[3] <- aux_1;
    (aux, aux_1) <- (ADCX_64 r.[0] hi cf);
    cf <- aux;
    r.[0] <- aux_1;
    (hi, lo) <- (MULX_64 f g.[2]);
    (aux, aux_1) <- (ADOX_64 r.[0] lo of_0);
    of_0 <- aux;
    r.[0] <- aux_1;
    (aux, aux_1) <- (ADCX_64 r.[1] hi cf);
    cf <- aux;
    r.[1] <- aux_1;
    (aux_1, aux_0) <- (MULX_64 f g.[3]);
    r.[2] <- aux_1;
    lo <- aux_0;
    (aux, aux_1) <- (ADOX_64 r.[1] lo of_0);
    of_0 <- aux;
    r.[1] <- aux_1;
    (aux, aux_1) <- (ADCX_64 r.[2] z cf);
    cf <- aux;
    r.[2] <- aux_1;
    (aux, aux_1) <- (ADOX_64 r.[2] z of_0);
    of_0 <- aux;
    r.[2] <- aux_1;
    return (h, r, cf, of_0);
  }
  proc __mul4_c3 (h:W64.t Array4.t, r:W64.t Array4.t, f:W64.t,
                  g:W64.t Array4.t, z:W64.t, cf:bool, of_0:bool) : W64.t Array4.t *
                                                                   W64.t Array4.t *
                                                                   bool *
                                                                   bool = {
    var aux:bool;
    var aux_1:W64.t;
    var aux_0:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    (hi, lo) <- (MULX_64 f g.[0]);
    (aux, aux_1) <- (ADOX_64 h.[3] lo of_0);
    of_0 <- aux;
    h.[3] <- aux_1;
    (aux, aux_1) <- (ADCX_64 r.[0] hi cf);
    cf <- aux;
    r.[0] <- aux_1;
    (hi, lo) <- (MULX_64 f g.[1]);
    (aux, aux_1) <- (ADOX_64 r.[0] lo of_0);
    of_0 <- aux;
    r.[0] <- aux_1;
    (aux, aux_1) <- (ADCX_64 r.[1] hi cf);
    cf <- aux;
    r.[1] <- aux_1;
    (hi, lo) <- (MULX_64 f g.[2]);
    (aux, aux_1) <- (ADOX_64 r.[1] lo of_0);
    of_0 <- aux;
    r.[1] <- aux_1;
    (aux, aux_1) <- (ADCX_64 r.[2] hi cf);
    cf <- aux;
    r.[2] <- aux_1;
    (aux_1, aux_0) <- (MULX_64 f g.[3]);
    r.[3] <- aux_1;
    lo <- aux_0;
    (aux, aux_1) <- (ADOX_64 r.[2] lo of_0);
    of_0 <- aux;
    r.[2] <- aux_1;
    (aux, aux_1) <- (ADCX_64 r.[3] z cf);
    cf <- aux;
    r.[3] <- aux_1;
    (aux, aux_1) <- (ADOX_64 r.[3] z of_0);
    of_0 <- aux;
    r.[3] <- aux_1;
    return (h, r, cf, of_0);
  }
  proc __mul4_rsr (fs:W64.t Array4.t, g:W64.t Array4.t) : W64.t Array4.t = {
    var h:W64.t Array4.t;
    var of_0:bool;
    var cf:bool;
    var z:W64.t;
    var f:W64.t;
    var r:W64.t Array4.t;
    var _38:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    h <- witness;
    r <- witness;
    (of_0, cf,  _0,  _1,  _2, z) <- (set0_64);
    f <- fs.[0];
    (h, r, cf, of_0) <@ __mul4_c0 (f, g, z, cf, of_0);
    f <- fs.[1];
    (h, r, cf, of_0) <@ __mul4_c1 (h, r, f, g, z, cf, of_0);
    f <- fs.[2];
    (h, r, cf, of_0) <@ __mul4_c2 (h, r, f, g, z, cf, of_0);
    f <- fs.[3];
    (h, r, cf, of_0) <@ __mul4_c3 (h, r, f, g, z, cf, of_0);
    _38 <- (W64.of_int 38);
    h <@ __reduce4 (h, r, _38, z, cf, of_0);
    return h;
  }
  proc __mul4_rpr (fp:W64.t Array4.t, g:W64.t Array4.t) : W64.t Array4.t = {
    var h:W64.t Array4.t;
    var of_0:bool;
    var cf:bool;
    var z:W64.t;
    var f:W64.t;
    var r:W64.t Array4.t;
    var _38:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    h <- witness;
    r <- witness;
    (of_0, cf,  _0,  _1,  _2, z) <- (set0_64);
    f <- fp.[0];
    (h, r, cf, of_0) <@ __mul4_c0 (f, g, z, cf, of_0);
    f <- fp.[1];
    (h, r, cf, of_0) <@ __mul4_c1 (h, r, f, g, z, cf, of_0);
    f <- fp.[2];
    (h, r, cf, of_0) <@ __mul4_c2 (h, r, f, g, z, cf, of_0);
    f <- fp.[3];
    (h, r, cf, of_0) <@ __mul4_c3 (h, r, f, g, z, cf, of_0);
    _38 <- (W64.of_int 38);
    h <@ __reduce4 (h, r, _38, z, cf, of_0);
    return h;
  }
  proc _mul4_rpr (fp:W64.t Array4.t, g:W64.t Array4.t) : W64.t Array4.t = {
    var h:W64.t Array4.t;
    h <- witness;
    h <@ __mul4_rpr (fp, g);
    return h;
  }
  proc _mul4_rsr_ (_fs:W64.t Array4.t, _g:W64.t Array4.t) : W64.t Array4.t = {
    var _h:W64.t Array4.t;
    var fp:W64.t Array4.t;
    var g:W64.t Array4.t;
    var h:W64.t Array4.t;
    _h <- witness;
    fp <- witness;
    g <- witness;
    h <- witness;
    fp <- _fs;
    g <- (copy_64 _g);
    h <@ _mul4_rpr (fp, g);
    _h <- (copy_64 h);
    return _h;
  }
  proc __mul4_ssr (fs:W64.t Array4.t, g:W64.t Array4.t) : W64.t Array4.t = {
    var hs:W64.t Array4.t;
    var h:W64.t Array4.t;
    h <- witness;
    hs <- witness;
    h <@ __mul4_rsr (fs, g);
    hs <- (copy_64 h);
    return hs;
  }
  proc __mul4_sss (fs:W64.t Array4.t, gs:W64.t Array4.t) : W64.t Array4.t = {
    var hs:W64.t Array4.t;
    var g:W64.t Array4.t;
    var h:W64.t Array4.t;
    g <- witness;
    h <- witness;
    hs <- witness;
    g <- (copy_64 gs);
    h <@ __mul4_rsr (fs, g);
    hs <- (copy_64 h);
    return hs;
  }
  proc __mul4_rss (fs:W64.t Array4.t, gs:W64.t Array4.t) : W64.t Array4.t = {
    var h:W64.t Array4.t;
    var g:W64.t Array4.t;
    g <- witness;
    h <- witness;
    g <- (copy_64 gs);
    h <@ __mul4_rsr (fs, g);
    return h;
  }
  proc __mul4_a24_rs (fs:W64.t Array4.t, a24:W64.t) : W64.t Array4.t = {
    var aux_1:bool;
    var aux_0:W64.t;
    var aux:W64.t;
    var h:W64.t Array4.t;
    var c:W64.t;
    var lo:W64.t;
    var cf:bool;
    var r0:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    h <- witness;
    c <- a24;
    (aux_0, aux) <- (MULX_64 c fs.[0]);
    h.[1] <- aux_0;
    h.[0] <- aux;
    (aux_0, aux) <- (MULX_64 c fs.[1]);
    h.[2] <- aux_0;
    lo <- aux;
    (aux_1, aux_0) <- (adc_64 h.[1] lo false);
    cf <- aux_1;
    h.[1] <- aux_0;
    (aux_0, aux) <- (MULX_64 c fs.[2]);
    h.[3] <- aux_0;
    lo <- aux;
    (aux_1, aux_0) <- (adc_64 h.[2] lo cf);
    cf <- aux_1;
    h.[2] <- aux_0;
    (r0, lo) <- (MULX_64 c fs.[3]);
    (aux_1, aux_0) <- (adc_64 h.[3] lo cf);
    cf <- aux_1;
    h.[3] <- aux_0;
    ( _0, r0) <- (adc_64 r0 (W64.of_int 0) cf);
    ( _1,  _2,  _3,  _4,  _5, r0) <- (IMULri_64 r0 (W64.of_int 38));
    (aux_1, aux_0) <- (adc_64 h.[0] r0 false);
    cf <- aux_1;
    h.[0] <- aux_0;
    (aux_1, aux_0) <- (adc_64 h.[1] (W64.of_int 0) cf);
    cf <- aux_1;
    h.[1] <- aux_0;
    (aux_1, aux_0) <- (adc_64 h.[2] (W64.of_int 0) cf);
    cf <- aux_1;
    h.[2] <- aux_0;
    (aux_1, aux_0) <- (adc_64 h.[3] (W64.of_int 0) cf);
    cf <- aux_1;
    h.[3] <- aux_0;
    ( _6, c) <- (sbb_64 c c cf);
    c <- (c `&` (W64.of_int 38));
    h.[0] <- (h.[0] + c);
    return h;
  }
  proc __mul4_a24_ss (fs:W64.t Array4.t, a24:W64.t) : W64.t Array4.t = {
    var hs:W64.t Array4.t;
    var h:W64.t Array4.t;
    h <- witness;
    hs <- witness;
    h <@ __mul4_a24_rs (fs, a24);
    hs <- (copy_64 h);
    return hs;
  }
  proc __sqr4_rr (f:W64.t Array4.t) : W64.t Array4.t = {
    var aux_1:bool;
    var aux_0:W64.t;
    var aux:W64.t;
    var h:W64.t Array4.t;
    var of_0:bool;
    var cf:bool;
    var z:W64.t;
    var fx:W64.t;
    var t:W64.t Array8.t;
    var r:W64.t Array4.t;
    var _38:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    h <- witness;
    r <- witness;
    t <- witness;
    (of_0, cf,  _0,  _1,  _2, z) <- (set0_64);
    fx <- f.[0];
    (aux_0, aux) <- (MULX_64 fx fx);
    t.[1] <- aux_0;
    h.[0] <- aux;
    (aux_0, aux) <- (MULX_64 fx f.[1]);
    h.[2] <- aux_0;
    h.[1] <- aux;
    (aux_0, aux) <- (MULX_64 fx f.[2]);
    h.[3] <- aux_0;
    t.[2] <- aux;
    (aux_1, aux_0) <- (ADCX_64 h.[2] t.[2] cf);
    cf <- aux_1;
    h.[2] <- aux_0;
    (aux_0, aux) <- (MULX_64 fx f.[3]);
    r.[0] <- aux_0;
    t.[3] <- aux;
    (aux_1, aux_0) <- (ADCX_64 h.[3] t.[3] cf);
    cf <- aux_1;
    h.[3] <- aux_0;
    fx <- f.[1];
    (aux_0, aux) <- (MULX_64 fx f.[2]);
    t.[4] <- aux_0;
    t.[3] <- aux;
    (aux_1, aux_0) <- (ADOX_64 h.[3] t.[3] of_0);
    of_0 <- aux_1;
    h.[3] <- aux_0;
    (aux_1, aux_0) <- (ADCX_64 r.[0] t.[4] cf);
    cf <- aux_1;
    r.[0] <- aux_0;
    (aux_0, aux) <- (MULX_64 fx f.[3]);
    r.[1] <- aux_0;
    t.[4] <- aux;
    (aux_1, aux_0) <- (ADOX_64 r.[0] t.[4] of_0);
    of_0 <- aux_1;
    r.[0] <- aux_0;
    (aux_0, aux) <- (MULX_64 fx fx);
    t.[3] <- aux_0;
    t.[2] <- aux;
    fx <- f.[2];
    (aux_0, aux) <- (MULX_64 fx f.[3]);
    r.[2] <- aux_0;
    t.[5] <- aux;
    (aux_1, aux_0) <- (ADCX_64 r.[1] t.[5] cf);
    cf <- aux_1;
    r.[1] <- aux_0;
    (aux_1, aux_0) <- (ADOX_64 r.[1] z of_0);
    of_0 <- aux_1;
    r.[1] <- aux_0;
    (aux_1, aux_0) <- (ADCX_64 r.[2] z cf);
    cf <- aux_1;
    r.[2] <- aux_0;
    (aux_1, aux_0) <- (ADOX_64 r.[2] z of_0);
    of_0 <- aux_1;
    r.[2] <- aux_0;
    (aux_0, aux) <- (MULX_64 fx fx);
    t.[5] <- aux_0;
    t.[4] <- aux;
    fx <- f.[3];
    (aux_0, aux) <- (MULX_64 fx fx);
    r.[3] <- aux_0;
    t.[6] <- aux;
    (aux_1, aux_0) <- (ADCX_64 h.[1] h.[1] cf);
    cf <- aux_1;
    h.[1] <- aux_0;
    (aux_1, aux_0) <- (ADOX_64 h.[1] t.[1] of_0);
    of_0 <- aux_1;
    h.[1] <- aux_0;
    (aux_1, aux_0) <- (ADCX_64 h.[2] h.[2] cf);
    cf <- aux_1;
    h.[2] <- aux_0;
    (aux_1, aux_0) <- (ADOX_64 h.[2] t.[2] of_0);
    of_0 <- aux_1;
    h.[2] <- aux_0;
    (aux_1, aux_0) <- (ADCX_64 h.[3] h.[3] cf);
    cf <- aux_1;
    h.[3] <- aux_0;
    (aux_1, aux_0) <- (ADOX_64 h.[3] t.[3] of_0);
    of_0 <- aux_1;
    h.[3] <- aux_0;
    (aux_1, aux_0) <- (ADCX_64 r.[0] r.[0] cf);
    cf <- aux_1;
    r.[0] <- aux_0;
    (aux_1, aux_0) <- (ADOX_64 r.[0] t.[4] of_0);
    of_0 <- aux_1;
    r.[0] <- aux_0;
    (aux_1, aux_0) <- (ADCX_64 r.[1] r.[1] cf);
    cf <- aux_1;
    r.[1] <- aux_0;
    (aux_1, aux_0) <- (ADOX_64 r.[1] t.[5] of_0);
    of_0 <- aux_1;
    r.[1] <- aux_0;
    (aux_1, aux_0) <- (ADCX_64 r.[2] r.[2] cf);
    cf <- aux_1;
    r.[2] <- aux_0;
    (aux_1, aux_0) <- (ADOX_64 r.[2] t.[6] of_0);
    of_0 <- aux_1;
    r.[2] <- aux_0;
    (aux_1, aux_0) <- (ADCX_64 r.[3] z cf);
    cf <- aux_1;
    r.[3] <- aux_0;
    (aux_1, aux_0) <- (ADOX_64 r.[3] z of_0);
    of_0 <- aux_1;
    r.[3] <- aux_0;
    _38 <- (W64.of_int 38);
    h <@ __reduce4 (h, r, _38, z, cf, of_0);
    return h;
  }
  proc _sqr4_rr (f:W64.t Array4.t) : W64.t Array4.t = {
    var h:W64.t Array4.t;
    h <- witness;
    h <@ __sqr4_rr (f);
    return h;
  }
  proc _sqr4_rr_ (_f:W64.t Array4.t) : W64.t Array4.t = {
    var _h:W64.t Array4.t;
    var f:W64.t Array4.t;
    var h:W64.t Array4.t;
    _h <- witness;
    f <- witness;
    h <- witness;
    f <- (copy_64 _f);
    h <@ _sqr4_rr (f);
    _h <- (copy_64 h);
    return _h;
  }
  proc __it_sqr4_x2 (f:W64.t Array4.t, i:W32.t) : W64.t Array4.t = {
    var zf:bool;
    var _i:W32.t;
    var h:W64.t Array4.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    h <- witness;
    _i <- i;
    h <@ __sqr4_rr (f);
    f <@ __sqr4_rr (h);
    i <- _i;
    ( _0,  _1,  _2, zf, i) <- (DEC_32 i);
    while ((! zf)) {
      _i <- i;
      h <@ __sqr4_rr (f);
      f <@ __sqr4_rr (h);
      i <- _i;
      ( _0,  _1,  _2, zf, i) <- (DEC_32 i);
    }
    return f;
  }
  proc _it_sqr4_x2 (f:W64.t Array4.t, i:W32.t) : W64.t Array4.t = {
    
    f <@ __it_sqr4_x2 (f, i);
    return f;
  }
  proc _it_sqr4_x2_ (_f:W64.t Array4.t, i:W32.t) : W64.t Array4.t = {
    var f:W64.t Array4.t;
    f <- witness;
    f <- (copy_64 _f);
    f <@ _it_sqr4_x2 (f, i);
    return f;
  }
  proc __sqr4_ss (fs:W64.t Array4.t) : W64.t Array4.t = {
    var hs:W64.t Array4.t;
    var f:W64.t Array4.t;
    var h:W64.t Array4.t;
    f <- witness;
    h <- witness;
    hs <- witness;
    f <- (copy_64 fs);
    h <@ __sqr4_rr (f);
    hs <- (copy_64 h);
    return hs;
  }
  proc __sqr4_rs (fs:W64.t Array4.t) : W64.t Array4.t = {
    var h:W64.t Array4.t;
    var f:W64.t Array4.t;
    f <- witness;
    h <- witness;
    f <- (copy_64 fs);
    h <@ __sqr4_rr (f);
    return h;
  }
  proc __invert4 (f:W64.t Array4.t) : W64.t Array4.t = {
    var t1:W64.t Array4.t;
    var fs:W64.t Array4.t;
    var t0:W64.t Array4.t;
    var t0s:W64.t Array4.t;
    var t1s:W64.t Array4.t;
    var t2:W64.t Array4.t;
    var i:W32.t;
    var t2s:W64.t Array4.t;
    var t3:W64.t Array4.t;
    fs <- witness;
    t0 <- witness;
    t0s <- witness;
    t1 <- witness;
    t1s <- witness;
    t2 <- witness;
    t2s <- witness;
    t3 <- witness;
    fs <- (copy_64 f);
    t0 <@ _sqr4_rr_ (f);
    t0s <- (copy_64 t0);
    t1 <@ _sqr4_rr_ (t0);
    t1 <@ _sqr4_rr_ (t1);
    t1 <@ _mul4_rsr_ (fs, t1);
    t1s <- (copy_64 t1);
    t0 <@ _mul4_rsr_ (t0s, t1);
    t0s <- (copy_64 t0);
    t2 <@ _sqr4_rr_ (t0);
    t1 <@ _mul4_rsr_ (t1s, t2);
    t1s <- (copy_64 t1);
    t2 <@ _sqr4_rr_ (t1);
    i <- (W32.of_int (4 %/ 2));
    t2 <@ _it_sqr4_x2_ (t2, i);
    t2s <- (copy_64 t2);
    t1 <@ _mul4_rsr_ (t1s, t2);
    t1s <- (copy_64 t1);
    i <- (W32.of_int (10 %/ 2));
    t2 <@ _it_sqr4_x2_ (t1, i);
    t2 <@ _mul4_rsr_ (t1s, t2);
    t2s <- (copy_64 t2);
    i <- (W32.of_int (20 %/ 2));
    t3 <@ _it_sqr4_x2_ (t2, i);
    t2 <@ _mul4_rsr_ (t2s, t3);
    i <- (W32.of_int (10 %/ 2));
    t2 <@ _it_sqr4_x2_ (t2, i);
    t1 <@ _mul4_rsr_ (t1s, t2);
    t1s <- (copy_64 t1);
    i <- (W32.of_int (50 %/ 2));
    t2 <@ _it_sqr4_x2_ (t1, i);
    t2 <@ _mul4_rsr_ (t1s, t2);
    t2s <- (copy_64 t2);
    i <- (W32.of_int (100 %/ 2));
    t3 <@ _it_sqr4_x2_ (t2, i);
    t2 <@ _mul4_rsr_ (t2s, t3);
    i <- (W32.of_int (50 %/ 2));
    t2 <@ _it_sqr4_x2_ (t2, i);
    t1 <@ _mul4_rsr_ (t1s, t2);
    i <- (W32.of_int (4 %/ 2));
    t1 <@ _it_sqr4_x2_ (t1, i);
    t1 <@ _sqr4_rr_ (t1);
    t1 <@ _mul4_rsr_ (t0s, t1);
    return t1;
  }
  proc __add_and_double4 (init:W64.t Array4.t, x2:W64.t Array4.t,
                          z2r:W64.t Array4.t, x3:W64.t Array4.t,
                          z3:W64.t Array4.t) : W64.t Array4.t *
                                               W64.t Array4.t *
                                               W64.t Array4.t *
                                               W64.t Array4.t = {
    var t0:W64.t Array4.t;
    var t1:W64.t Array4.t;
    var z2:W64.t Array4.t;
    var t2:W64.t Array4.t;
    var t1r:W64.t Array4.t;
    t0 <- witness;
    t1 <- witness;
    t1r <- witness;
    t2 <- witness;
    z2 <- witness;
    t0 <@ __sub4_ssr (x2, z2r);
    x2 <@ __add4_ssr (x2, z2r);
    t1 <@ __sub4_sss (x3, z3);
    z2 <@ __add4_sss (x3, z3);
    z3 <@ __mul4_sss (x2, t1);
    z2 <@ __mul4_sss (z2, t0);
    t2 <@ __sqr4_ss (x2);
    t1r <@ __sqr4_rs (t0);
    x3 <@ __add4_sss (z3, z2);
    z2 <@ __sub4_sss (z3, z2);
    t0 <@ __sub4_ssr (t2, t1r);
    x2 <@ __mul4_ssr (t2, t1r);
    z2 <@ __sqr4_ss (z2);
    z3 <@ __mul4_a24_ss (t0, (W64.of_int 121665));
    x3 <@ __sqr4_ss (x3);
    t2 <@ __add4_sss (t2, z3);
    z3 <@ __mul4_sss (init, z2);
    z2r <@ __mul4_rss (t0, t2);
    return (x2, z2r, x3, z3);
  }
  proc __montgomery_ladder_step4 (k:W8.t Array32.t, init:W64.t Array4.t,
                                  x2:W64.t Array4.t, z2r:W64.t Array4.t,
                                  x3:W64.t Array4.t, z3:W64.t Array4.t,
                                  swapped:W64.t, ctr:W64.t) : W64.t Array4.t *
                                                              W64.t Array4.t *
                                                              W64.t Array4.t *
                                                              W64.t Array4.t *
                                                              W64.t = {
    var bit:W64.t;
    var toswap:W64.t;
    bit <@ __ith_bit (k, ctr);
    toswap <- swapped;
    toswap <- (toswap `^` bit);
    (x2, z2r, x3, z3) <@ __cswap4 (x2, z2r, x3, z3, toswap);
    swapped <- bit;
    (x2, z2r, x3, z3) <@ __add_and_double4 (init, x2, z2r, x3, z3);
    return (x2, z2r, x3, z3, swapped);
  }
  proc __montgomery_ladder4 (u:W64.t Array4.t, k:W8.t Array32.t) : W64.t Array4.t *
                                                                   W64.t Array4.t = {
    var x2:W64.t Array4.t;
    var z2r:W64.t Array4.t;
    var x3:W64.t Array4.t;
    var z3:W64.t Array4.t;
    var us:W64.t Array4.t;
    var ctr:W64.t;
    var swapped:W64.t;
    us <- witness;
    x2 <- witness;
    x3 <- witness;
    z2r <- witness;
    z3 <- witness;
    (x2, z2r, x3, z3) <@ __init_points4 (u);
    us <- (copy_64 u);
    ctr <- (W64.of_int 255);
    swapped <- (W64.of_int 0);
    ctr <- (ctr - (W64.of_int 1));
    (* Erased call to spill *)
    (x2, z2r, x3, z3, swapped) <@ __montgomery_ladder_step4 (k, us, x2, 
    z2r, x3, z3, swapped, ctr);
    (* Erased call to unspill *)
    while (((W64.of_int 0) \ult ctr)) {
      ctr <- (ctr - (W64.of_int 1));
      (* Erased call to spill *)
      (x2, z2r, x3, z3, swapped) <@ __montgomery_ladder_step4 (k, us, 
      x2, z2r, x3, z3, swapped, ctr);
      (* Erased call to unspill *)
    }
    return (x2, z2r);
  }
  proc __encode_point4 (x2:W64.t Array4.t, z2r:W64.t Array4.t) : W64.t Array4.t = {
    var r:W64.t Array4.t;
    r <- witness;
    z2r <@ __invert4 (z2r);
    r <@ __mul4_rsr (x2, z2r);
    r <@ __tobytes4 (r);
    return r;
  }
  proc __curve25519_internal_mulx (k:W8.t Array32.t, u:W64.t Array4.t) : 
  W64.t Array4.t = {
    var r:W64.t Array4.t;
    var x2:W64.t Array4.t;
    var z2r:W64.t Array4.t;
    r <- witness;
    x2 <- witness;
    z2r <- witness;
    (x2, z2r) <@ __montgomery_ladder4 (u, k);
    r <@ __encode_point4 (x2, z2r);
    return r;
  }
  proc __curve25519_mulx (_k:W64.t Array4.t, _u:W64.t Array4.t) : W64.t Array4.t = {
    var r:W64.t Array4.t;
    var k:W8.t Array32.t;
    var u:W64.t Array4.t;
    k <- witness;
    r <- witness;
    u <- witness;
    k <@ __decode_scalar (_k);
    u <@ __decode_u_coordinate4 (_u);
    r <@ __curve25519_internal_mulx (k, u);
    return r;
  }
  proc __curve25519_mulx_base (_k:W64.t Array4.t) : W64.t Array4.t = {
    var r:W64.t Array4.t;
    var k:W8.t Array32.t;
    var u:W64.t Array4.t;
    k <- witness;
    r <- witness;
    u <- witness;
    k <@ __decode_scalar (_k);
    u <@ __decode_u_coordinate_base4 ();
    r <@ __curve25519_internal_mulx (k, u);
    return r;
  }
  proc jade_scalarmult_curve25519_amd64_mulx (qp:W64.t Array4.t,
                                              np:W64.t Array4.t,
                                              pp:W64.t Array4.t) : W64.t Array4.t *
                                                                   W64.t = {
    var r:W64.t;
    var n:W64.t Array4.t;
    var p:W64.t Array4.t;
    var q:W64.t Array4.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var  _0:W64.t;
    var  _1:bool;
    n <- witness;
    p <- witness;
    q <- witness;
     _0 <- (init_msf);
    (* Erased call to spill *)
    n <- (copy_64 np);
    p <- (copy_64 pp);
    q <@ __curve25519_mulx (n, p);
    (* Erased call to unspill *)
    qp <- (copy_64 q);
    (_of_, _cf_, _sf_,  _1, _zf_, r) <- (set0_64);
    return (qp, r);
  }
  proc jade_scalarmult_curve25519_amd64_mulx_base (qp:W64.t Array4.t,
                                                   np:W64.t Array4.t) : 
  W64.t Array4.t * W64.t = {
    var r:W64.t;
    var n:W64.t Array4.t;
    var q:W64.t Array4.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var  _0:W64.t;
    var  _1:bool;
    n <- witness;
    q <- witness;
     _0 <- (init_msf);
    (* Erased call to spill *)
    n <- (copy_64 np);
    q <@ __curve25519_mulx_base (n);
    (* Erased call to unspill *)
    qp <- (copy_64 q);
    (_of_, _cf_, _sf_,  _1, _zf_, r) <- (set0_64);
    return (qp, r);
  }
}.
