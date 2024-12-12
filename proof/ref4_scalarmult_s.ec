require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import Array4 Array5 Array8 Array32.

require import WArray32 WArray40 WArray64.

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
  proc __reduce4 (z:W64.t Array8.t) : W64.t Array4.t = {
    var aux:bool;
    var aux_1:int;
    var aux_0:W64.t;
    var r:W64.t Array4.t;
    var r38:W64.t;
    var rax:W64.t;
    var h:W64.t;
    var l:W64.t;
    var cf:bool;
    var z8:W64.t;
    var i:int;
    var r0:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    r <- witness;
    r38 <- (W64.of_int 38);
    rax <- z.[4];
    (h, l) <- (mulu_64 rax r38);
    r.[0] <- l;
    r.[1] <- h;
    rax <- z.[5];
    (h, l) <- (mulu_64 rax r38);
    (aux, aux_0) <- (adc_64 r.[1] l false);
    cf <- aux;
    r.[1] <- aux_0;
    r.[2] <- (MOV_64 (W64.of_int 0));
    rax <- z.[6];
    (aux, aux_0) <- (adc_64 r.[2] h cf);
     _0 <- aux;
    r.[2] <- aux_0;
    (h, l) <- (mulu_64 rax r38);
    (aux, aux_0) <- (adc_64 r.[2] l false);
    cf <- aux;
    r.[2] <- aux_0;
    r.[3] <- (MOV_64 (W64.of_int 0));
    rax <- z.[7];
    (aux, aux_0) <- (adc_64 r.[3] h cf);
     _1 <- aux;
    r.[3] <- aux_0;
    (h, l) <- (mulu_64 rax r38);
    (aux, aux_0) <- (adc_64 r.[3] l false);
    cf <- aux;
    r.[3] <- aux_0;
    z8 <- (MOV_64 (W64.of_int 0));
    ( _2, z8) <- (adc_64 z8 h cf);
    (aux, aux_0) <- (adc_64 r.[0] z.[0] false);
    cf <- aux;
    r.[0] <- aux_0;
    i <- 1;
    while ((i < 4)) {
      (aux, aux_0) <- (adc_64 r.[i] z.[i] cf);
      cf <- aux;
      r.[i] <- aux_0;
      i <- (i + 1);
    }
    ( _3, z8) <- (adc_64 z8 (W64.of_int 0) cf);
    z8 <- (z8 * (W64.of_int 38));
    r0 <- (MOV_64 (W64.of_int 0));
    (aux, aux_0) <- (adc_64 r.[0] z8 false);
    cf <- aux;
    r.[0] <- aux_0;
    i <- 1;
    while ((i < 4)) {
      (aux, aux_0) <- (adc_64 r.[i] r0 cf);
      cf <- aux;
      r.[i] <- aux_0;
      i <- (i + 1);
    }
    ( _4, r0) <- (adc_64 r0 r0 cf);
    r0 <- (r0 * (W64.of_int 38));
    r.[0] <- (r.[0] + r0);
    return r;
  }
  proc __mul4_rss (xa:W64.t Array4.t, ya:W64.t Array4.t) : W64.t Array4.t = {
    var aux_0:bool;
    var aux:int;
    var aux_1:W64.t;
    var r:W64.t Array4.t;
    var i:int;
    var z:W64.t Array8.t;
    var x:W64.t Array4.t;
    var j:int;
    var y:W64.t Array4.t;
    var h:W64.t;
    var l:W64.t;
    var cf:bool;
    var hprev:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    r <- witness;
    x <- witness;
    y <- witness;
    z <- witness;
    i <- 2;
    while ((i < 8)) {
      z.[i] <- (MOV_64 (W64.of_int 0));
      i <- (i + 1);
    }
    x.[0] <- xa.[0];
    j <- 0;
    while ((j < 4)) {
      y.[j] <- ya.[j];
      (h, l) <- (mulu_64 y.[j] x.[0]);
      if ((j = 0)) {
        z.[0] <- l;
        z.[1] <- h;
      } else {
        (aux_0, aux_1) <- (adc_64 z.[j] l false);
        cf <- aux_0;
        z.[j] <- aux_1;
        (aux_0, aux_1) <- (adc_64 z.[(j + 1)] h cf);
         _0 <- aux_0;
        z.[(j + 1)] <- aux_1;
      }
      j <- (j + 1);
    }
    i <- 1;
    while ((i < 4)) {
      x.[i] <- xa.[i];
      j <- 0;
      while ((j < 4)) {
        y.[j] <- ya.[j];
        (h, l) <- (mulu_64 y.[j] x.[i]);
        (aux_0, aux_1) <- (adc_64 z.[(i + j)] l false);
        cf <- aux_0;
        z.[(i + j)] <- aux_1;
        if ((j = 0)) {
          hprev <- (MOV_64 (W64.of_int 0));
          ( _3, hprev) <- (adc_64 hprev h cf);
        } else {
          ( _1, h) <- (adc_64 h (W64.of_int 0) cf);
          (aux_0, aux_1) <- (adc_64 z.[(i + j)] hprev false);
          cf <- aux_0;
          z.[(i + j)] <- aux_1;
          if (((1 <= j) /\ (j < (4 - 1)))) {
            hprev <- (MOV_64 (W64.of_int 0));
            ( _2, hprev) <- (adc_64 hprev h cf);
          } else {
            (aux_0, aux_1) <- (adc_64 z.[((i + j) + 1)] h cf);
            cf <- aux_0;
            z.[((i + j) + 1)] <- aux_1;
          }
        }
        j <- (j + 1);
      }
      i <- (i + 1);
    }
    r <@ __reduce4 (z);
    return r;
  }
  proc __mul4_sss (xa:W64.t Array4.t, ya:W64.t Array4.t) : W64.t Array4.t = {
    var rs:W64.t Array4.t;
    var r:W64.t Array4.t;
    r <- witness;
    rs <- witness;
    r <@ __mul4_rss (xa, ya);
    rs <- (copy_64 r);
    return rs;
  }
  proc _mul4_pp (xa:W64.t Array4.t, ya:W64.t Array4.t) : W64.t Array4.t = {
    var aux_0:bool;
    var aux:int;
    var aux_1:W64.t;
    var i:int;
    var z:W64.t Array8.t;
    var x:W64.t Array4.t;
    var j:int;
    var y:W64.t Array4.t;
    var h:W64.t;
    var l:W64.t;
    var cf:bool;
    var hprev:W64.t;
    var r:W64.t Array4.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    r <- witness;
    x <- witness;
    y <- witness;
    z <- witness;
    i <- 2;
    while ((i < 8)) {
      z.[i] <- (MOV_64 (W64.of_int 0));
      i <- (i + 1);
    }
    x.[0] <- xa.[0];
    j <- 0;
    while ((j < 4)) {
      y.[j] <- ya.[j];
      (h, l) <- (mulu_64 y.[j] x.[0]);
      if ((j = 0)) {
        z.[0] <- l;
        z.[1] <- h;
      } else {
        (aux_0, aux_1) <- (adc_64 z.[j] l false);
        cf <- aux_0;
        z.[j] <- aux_1;
        (aux_0, aux_1) <- (adc_64 z.[(j + 1)] h cf);
         _0 <- aux_0;
        z.[(j + 1)] <- aux_1;
      }
      j <- (j + 1);
    }
    i <- 1;
    while ((i < 4)) {
      x.[i] <- xa.[i];
      j <- 0;
      while ((j < 4)) {
        y.[j] <- ya.[j];
        (h, l) <- (mulu_64 y.[j] x.[i]);
        (aux_0, aux_1) <- (adc_64 z.[(i + j)] l false);
        cf <- aux_0;
        z.[(i + j)] <- aux_1;
        if ((j = 0)) {
          hprev <- (MOV_64 (W64.of_int 0));
          ( _3, hprev) <- (adc_64 hprev h cf);
        } else {
          ( _1, h) <- (adc_64 h (W64.of_int 0) cf);
          (aux_0, aux_1) <- (adc_64 z.[(i + j)] hprev false);
          cf <- aux_0;
          z.[(i + j)] <- aux_1;
          if (((1 <= j) /\ (j < (4 - 1)))) {
            hprev <- (MOV_64 (W64.of_int 0));
            ( _2, hprev) <- (adc_64 hprev h cf);
          } else {
            (aux_0, aux_1) <- (adc_64 z.[((i + j) + 1)] h cf);
            cf <- aux_0;
            z.[((i + j) + 1)] <- aux_1;
          }
        }
        j <- (j + 1);
      }
      i <- (i + 1);
    }
    r <@ __reduce4 (z);
    i <- 0;
    while ((i < 4)) {
      xa.[i] <- r.[i];
      i <- (i + 1);
    }
    return xa;
  }
  proc _mul4_ss_ (xa:W64.t Array4.t, ya:W64.t Array4.t) : W64.t Array4.t = {
    var xp:W64.t Array4.t;
    var yp:W64.t Array4.t;
    xp <- witness;
    yp <- witness;
    xp <- xa;
    yp <- ya;
    xp <@ _mul4_pp (xp, yp);
    xa <- xp;
    return xa;
  }
  proc __mul4_a24_rs (xa:W64.t Array4.t, a24:W64.t) : W64.t Array4.t = {
    var aux:bool;
    var aux_0:W64.t;
    var r:W64.t Array4.t;
    var c:W64.t;
    var rax:W64.t;
    var rdx:W64.t;
    var t1:W64.t;
    var t2:W64.t;
    var t3:W64.t;
    var t4:W64.t;
    var cf:bool;
    var  _0:bool;
    var  _1:W64.t;
    r <- witness;
    c <- a24;
    rax <- xa.[0];
    (rdx, rax) <- (mulu_64 rax c);
    r.[0] <- rax;
    r.[1] <- rdx;
    rax <- xa.[2];
    (rdx, rax) <- (mulu_64 rax c);
    r.[2] <- rax;
    r.[3] <- rdx;
    rax <- xa.[1];
    (rdx, rax) <- (mulu_64 rax c);
    t1 <- rax;
    t2 <- rdx;
    rax <- xa.[3];
    (rdx, rax) <- (mulu_64 rax c);
    t3 <- rax;
    t4 <- rdx;
    (aux, aux_0) <- (adc_64 r.[1] t1 false);
    cf <- aux;
    r.[1] <- aux_0;
    (aux, aux_0) <- (adc_64 r.[2] t2 cf);
    cf <- aux;
    r.[2] <- aux_0;
    (aux, aux_0) <- (adc_64 r.[3] t3 cf);
    cf <- aux;
    r.[3] <- aux_0;
    ( _0, t4) <- (adc_64 t4 (W64.of_int 0) cf);
    ( _1, t4) <- (mulu_64 t4 (W64.of_int 38));
    (aux, aux_0) <- (adc_64 r.[0] t4 false);
    cf <- aux;
    r.[0] <- aux_0;
    (aux, aux_0) <- (adc_64 r.[1] (W64.of_int 0) cf);
    cf <- aux;
    r.[1] <- aux_0;
    (aux, aux_0) <- (adc_64 r.[2] (W64.of_int 0) cf);
    cf <- aux;
    r.[2] <- aux_0;
    (aux, aux_0) <- (adc_64 r.[3] (W64.of_int 0) cf);
    cf <- aux;
    r.[3] <- aux_0;
    t1 <- (W64.of_int 38);
    t2 <- (MOV_64 (W64.of_int 0));
    t1 <- ((! cf) ? t2 : t1);
    r.[0] <- (r.[0] + t1);
    return r;
  }
  proc __mul4_a24_ss (xa:W64.t Array4.t, a24:W64.t) : W64.t Array4.t = {
    var rs:W64.t Array4.t;
    var r:W64.t Array4.t;
    r <- witness;
    rs <- witness;
    r <@ __mul4_a24_rs (xa, a24);
    rs <- (copy_64 r);
    return rs;
  }
  proc __sqr4_rs (xa:W64.t Array4.t) : W64.t Array4.t = {
    var aux:bool;
    var aux_0:W64.t;
    var r:W64.t Array4.t;
    var z:W64.t Array8.t;
    var zero:W64.t;
    var rax:W64.t;
    var rdx:W64.t;
    var cf:bool;
    var t:W64.t Array5.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    r <- witness;
    t <- witness;
    z <- witness;
    z.[7] <- (MOV_64 (W64.of_int 0));
    zero <- (MOV_64 (W64.of_int 0));
    rax <- xa.[1];
    (rdx, rax) <- (mulu_64 rax xa.[0]);
    z.[1] <- rax;
    z.[2] <- rdx;
    rax <- xa.[2];
    (rdx, rax) <- (mulu_64 rax xa.[1]);
    z.[3] <- rax;
    z.[4] <- rdx;
    rax <- xa.[3];
    (rdx, rax) <- (mulu_64 rax xa.[2]);
    z.[5] <- rax;
    z.[6] <- rdx;
    rax <- xa.[2];
    (rdx, rax) <- (mulu_64 rax xa.[0]);
    (aux, aux_0) <- (adc_64 z.[2] rax false);
    cf <- aux;
    z.[2] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[3] rdx cf);
    cf <- aux;
    z.[3] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[4] zero cf);
     _0 <- aux;
    z.[4] <- aux_0;
    rax <- xa.[3];
    (rdx, rax) <- (mulu_64 rax xa.[1]);
    (aux, aux_0) <- (adc_64 z.[4] rax false);
    cf <- aux;
    z.[4] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[5] rdx cf);
    cf <- aux;
    z.[5] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[6] zero cf);
     _1 <- aux;
    z.[6] <- aux_0;
    rax <- xa.[3];
    (rdx, rax) <- (mulu_64 rax xa.[0]);
    (aux, aux_0) <- (adc_64 z.[3] rax false);
    cf <- aux;
    z.[3] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[4] rdx cf);
    cf <- aux;
    z.[4] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[5] zero cf);
    cf <- aux;
    z.[5] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[6] zero cf);
    cf <- aux;
    z.[6] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[7] zero cf);
     _2 <- aux;
    z.[7] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[1] z.[1] false);
    cf <- aux;
    z.[1] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[2] z.[2] cf);
    cf <- aux;
    z.[2] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[3] z.[3] cf);
    cf <- aux;
    z.[3] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[4] z.[4] cf);
    cf <- aux;
    z.[4] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[5] z.[5] cf);
    cf <- aux;
    z.[5] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[6] z.[6] cf);
    cf <- aux;
    z.[6] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[7] z.[7] cf);
    cf <- aux;
    z.[7] <- aux_0;
    rax <- xa.[0];
    (rdx, rax) <- (mulu_64 rax xa.[0]);
    z.[0] <- rax;
    t.[0] <- rdx;
    rax <- xa.[1];
    (rdx, rax) <- (mulu_64 rax xa.[1]);
    t.[1] <- rax;
    t.[2] <- rdx;
    rax <- xa.[2];
    (rdx, rax) <- (mulu_64 rax xa.[2]);
    t.[3] <- rax;
    t.[4] <- rdx;
    (aux, aux_0) <- (adc_64 z.[1] t.[0] false);
    cf <- aux;
    z.[1] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[2] t.[1] cf);
    cf <- aux;
    z.[2] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[3] t.[2] cf);
    cf <- aux;
    z.[3] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[4] t.[3] cf);
    cf <- aux;
    z.[4] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[5] t.[4] cf);
    cf <- aux;
    z.[5] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[6] (W64.of_int 0) cf);
    cf <- aux;
    z.[6] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[7] (W64.of_int 0) cf);
     _3 <- aux;
    z.[7] <- aux_0;
    rax <- xa.[3];
    (rdx, rax) <- (mulu_64 rax xa.[3]);
    (aux, aux_0) <- (adc_64 z.[6] rax false);
    cf <- aux;
    z.[6] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[7] rdx cf);
     _4 <- aux;
    z.[7] <- aux_0;
    r <@ __reduce4 (z);
    return r;
  }
  proc __sqr4_ss (xa:W64.t Array4.t) : W64.t Array4.t = {
    var rs:W64.t Array4.t;
    var r:W64.t Array4.t;
    r <- witness;
    rs <- witness;
    r <@ __sqr4_rs (xa);
    rs <- (copy_64 r);
    return rs;
  }
  proc _sqr4_p (xa:W64.t Array4.t) : W64.t Array4.t = {
    var aux:bool;
    var aux_1:int;
    var aux_0:W64.t;
    var z:W64.t Array8.t;
    var zero:W64.t;
    var rax:W64.t;
    var rdx:W64.t;
    var cf:bool;
    var t:W64.t Array5.t;
    var r:W64.t Array4.t;
    var i:int;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    r <- witness;
    t <- witness;
    z <- witness;
    z.[7] <- (MOV_64 (W64.of_int 0));
    zero <- (MOV_64 (W64.of_int 0));
    rax <- xa.[1];
    (rdx, rax) <- (mulu_64 rax xa.[0]);
    z.[1] <- rax;
    z.[2] <- rdx;
    rax <- xa.[2];
    (rdx, rax) <- (mulu_64 rax xa.[1]);
    z.[3] <- rax;
    z.[4] <- rdx;
    rax <- xa.[3];
    (rdx, rax) <- (mulu_64 rax xa.[2]);
    z.[5] <- rax;
    z.[6] <- rdx;
    rax <- xa.[2];
    (rdx, rax) <- (mulu_64 rax xa.[0]);
    (aux, aux_0) <- (adc_64 z.[2] rax false);
    cf <- aux;
    z.[2] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[3] rdx cf);
    cf <- aux;
    z.[3] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[4] zero cf);
     _0 <- aux;
    z.[4] <- aux_0;
    rax <- xa.[3];
    (rdx, rax) <- (mulu_64 rax xa.[1]);
    (aux, aux_0) <- (adc_64 z.[4] rax false);
    cf <- aux;
    z.[4] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[5] rdx cf);
    cf <- aux;
    z.[5] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[6] zero cf);
     _1 <- aux;
    z.[6] <- aux_0;
    rax <- xa.[3];
    (rdx, rax) <- (mulu_64 rax xa.[0]);
    (aux, aux_0) <- (adc_64 z.[3] rax false);
    cf <- aux;
    z.[3] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[4] rdx cf);
    cf <- aux;
    z.[4] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[5] zero cf);
    cf <- aux;
    z.[5] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[6] zero cf);
    cf <- aux;
    z.[6] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[7] zero cf);
     _2 <- aux;
    z.[7] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[1] z.[1] false);
    cf <- aux;
    z.[1] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[2] z.[2] cf);
    cf <- aux;
    z.[2] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[3] z.[3] cf);
    cf <- aux;
    z.[3] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[4] z.[4] cf);
    cf <- aux;
    z.[4] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[5] z.[5] cf);
    cf <- aux;
    z.[5] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[6] z.[6] cf);
    cf <- aux;
    z.[6] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[7] z.[7] cf);
    cf <- aux;
    z.[7] <- aux_0;
    rax <- xa.[0];
    (rdx, rax) <- (mulu_64 rax xa.[0]);
    z.[0] <- rax;
    t.[0] <- rdx;
    rax <- xa.[1];
    (rdx, rax) <- (mulu_64 rax xa.[1]);
    t.[1] <- rax;
    t.[2] <- rdx;
    rax <- xa.[2];
    (rdx, rax) <- (mulu_64 rax xa.[2]);
    t.[3] <- rax;
    t.[4] <- rdx;
    (aux, aux_0) <- (adc_64 z.[1] t.[0] false);
    cf <- aux;
    z.[1] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[2] t.[1] cf);
    cf <- aux;
    z.[2] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[3] t.[2] cf);
    cf <- aux;
    z.[3] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[4] t.[3] cf);
    cf <- aux;
    z.[4] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[5] t.[4] cf);
    cf <- aux;
    z.[5] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[6] (W64.of_int 0) cf);
    cf <- aux;
    z.[6] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[7] (W64.of_int 0) cf);
     _3 <- aux;
    z.[7] <- aux_0;
    rax <- xa.[3];
    (rdx, rax) <- (mulu_64 rax xa.[3]);
    (aux, aux_0) <- (adc_64 z.[6] rax false);
    cf <- aux;
    z.[6] <- aux_0;
    (aux, aux_0) <- (adc_64 z.[7] rdx cf);
     _4 <- aux;
    z.[7] <- aux_0;
    r <@ __reduce4 (z);
    i <- 0;
    while ((i < 4)) {
      xa.[i] <- r.[i];
      i <- (i + 1);
    }
    return xa;
  }
  proc _sqr4_ss_ (xa:W64.t Array4.t) : W64.t Array4.t = {
    var aux:int;
    var ra:W64.t Array4.t;
    var j:int;
    var t:W64.t;
    var rp:W64.t Array4.t;
    ra <- witness;
    rp <- witness;
    j <- 0;
    while ((j < 4)) {
      t <- xa.[j];
      ra.[j] <- t;
      j <- (j + 1);
    }
    rp <- ra;
    rp <@ _sqr4_p (rp);
    ra <- rp;
    return ra;
  }
  proc _sqr4_s_ (x:W64.t Array4.t) : W64.t Array4.t = {
    var xp:W64.t Array4.t;
    xp <- witness;
    xp <- x;
    xp <@ _sqr4_p (xp);
    x <- xp;
    return x;
  }
  proc _it_sqr4_p (x:W64.t Array4.t, i:W32.t) : W64.t Array4.t = {
    var zf:bool;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    x <@ _sqr4_p (x);
    ( _0,  _1,  _2, zf, i) <- (DEC_32 i);
    while ((! zf)) {
      x <@ _sqr4_p (x);
      ( _0,  _1,  _2, zf, i) <- (DEC_32 i);
    }
    return x;
  }
  proc _it_sqr4_s_ (x:W64.t Array4.t, i:W32.t) : W64.t Array4.t = {
    var xp:W64.t Array4.t;
    xp <- witness;
    xp <- x;
    xp <@ _it_sqr4_p (xp, i);
    x <- xp;
    return x;
  }
  proc _it_sqr4_ss_ (r:W64.t Array4.t, x:W64.t Array4.t, i:W32.t) : W64.t Array4.t = {
    var aux:int;
    var j:int;
    var t:W64.t;
    var rp:W64.t Array4.t;
    rp <- witness;
    j <- 0;
    while ((j < 4)) {
      t <- x.[j];
      r.[j] <- t;
      j <- (j + 1);
    }
    rp <- r;
    rp <@ _it_sqr4_p (rp, i);
    r <- rp;
    return r;
  }
  proc __invert4 (fs:W64.t Array4.t) : W64.t Array4.t = {
    var t1s:W64.t Array4.t;
    var t0s:W64.t Array4.t;
    var t2s:W64.t Array4.t;
    var i:W32.t;
    var t3s:W64.t Array4.t;
    t0s <- witness;
    t1s <- witness;
    t2s <- witness;
    t3s <- witness;
    t0s <@ _sqr4_ss_ (fs);
    t1s <@ _sqr4_ss_ (t0s);
    t1s <@ _sqr4_s_ (t1s);
    t1s <@ _mul4_ss_ (t1s, fs);
    t0s <@ _mul4_ss_ (t0s, t1s);
    t2s <@ _sqr4_ss_ (t0s);
    t1s <@ _mul4_ss_ (t1s, t2s);
    t2s <@ _sqr4_ss_ (t1s);
    i <- (W32.of_int 4);
    t2s <@ _it_sqr4_s_ (t2s, i);
    t1s <@ _mul4_ss_ (t1s, t2s);
    i <- (W32.of_int 10);
    t2s <@ _it_sqr4_ss_ (t2s, t1s, i);
    t2s <@ _mul4_ss_ (t2s, t1s);
    i <- (W32.of_int 20);
    t3s <@ _it_sqr4_ss_ (t3s, t2s, i);
    t2s <@ _mul4_ss_ (t2s, t3s);
    i <- (W32.of_int 10);
    t2s <@ _it_sqr4_s_ (t2s, i);
    t1s <@ _mul4_ss_ (t1s, t2s);
    i <- (W32.of_int 50);
    t2s <@ _it_sqr4_ss_ (t2s, t1s, i);
    t2s <@ _mul4_ss_ (t2s, t1s);
    i <- (W32.of_int 100);
    t3s <@ _it_sqr4_ss_ (t3s, t2s, i);
    t2s <@ _mul4_ss_ (t2s, t3s);
    i <- (W32.of_int 50);
    t2s <@ _it_sqr4_s_ (t2s, i);
    t1s <@ _mul4_ss_ (t1s, t2s);
    i <- (W32.of_int 4);
    t1s <@ _it_sqr4_s_ (t1s, i);
    t1s <@ _sqr4_s_ (t1s);
    t1s <@ _mul4_ss_ (t1s, t0s);
    return t1s;
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
    t0 <- witness;
    t1 <- witness;
    t2 <- witness;
    z2 <- witness;
    t0 <@ __sub4_ssr (x2, z2r);
    x2 <@ __add4_ssr (x2, z2r);
    t1 <@ __sub4_sss (x3, z3);
    z2 <@ __add4_sss (x3, z3);
    z3 <@ __mul4_sss (x2, t1);
    z2 <@ __mul4_sss (z2, t0);
    t2 <@ __sqr4_ss (x2);
    t1 <@ __sqr4_ss (t0);
    x3 <@ __add4_sss (z3, z2);
    z2 <@ __sub4_sss (z3, z2);
    x2 <@ __mul4_sss (t2, t1);
    t0 <@ __sub4_sss (t2, t1);
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
    var z2:W64.t Array4.t;
    r <- witness;
    z2 <- witness;
    z2 <- (copy_64 z2r);
    z2 <@ __invert4 (z2);
    r <@ __mul4_rss (x2, z2);
    r <@ __tobytes4 (r);
    return r;
  }
  proc __curve25519_internal_ref4 (k:W8.t Array32.t, u:W64.t Array4.t) : 
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
  proc _curve25519_ref4 (_k:W64.t Array4.t, _u:W64.t Array4.t) : W64.t Array4.t = {
    var r:W64.t Array4.t;
    var k:W8.t Array32.t;
    var u:W64.t Array4.t;
    k <- witness;
    r <- witness;
    u <- witness;
    k <@ __decode_scalar (_k);
    u <@ __decode_u_coordinate4 (_u);
    r <@ __curve25519_internal_ref4 (k, u);
    return r;
  }
  proc _curve25519_ref4_base (_k:W64.t Array4.t) : W64.t Array4.t = {
    var r:W64.t Array4.t;
    var k:W8.t Array32.t;
    var u:W64.t Array4.t;
    k <- witness;
    r <- witness;
    u <- witness;
    k <@ __decode_scalar (_k);
    u <@ __decode_u_coordinate_base4 ();
    r <@ __curve25519_internal_ref4 (k, u);
    return r;
  }
  proc jade_scalarmult_curve25519_amd64_ref4 (qp:W64.t Array4.t,
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
    q <@ _curve25519_ref4 (n, p);
    (* Erased call to unspill *)
    qp <- (copy_64 q);
    (_of_, _cf_, _sf_,  _1, _zf_, r) <- (set0_64);
    return (qp, r);
  }
  proc jade_scalarmult_curve25519_amd64_ref4_base (qp:W64.t Array4.t,
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
    q <@ _curve25519_ref4_base (n);
    (* Erased call to unspill *)
    qp <- (copy_64 q);
    (_of_, _cf_, _sf_,  _1, _zf_, r) <- (set0_64);
    return (qp, r);
  }
}.
