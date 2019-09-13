module Hacl.Impl.Ed25519.Pow2_252m2

open FStar.HyperStack.All
module ST = FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum25519

module F51 = Hacl.Impl.Ed25519.Field51
module SC = Spec.Curve25519
module CI = Hacl.Spec.Curve25519.Finv

#set-options "--z3rlimit 500 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
val crecip_1:
     out:felem
  -> buf:lbuffer uint64 20ul
  -> z:felem ->
  Stack unit
    (requires fun h -> live h out /\ live h buf /\ live h z /\
      disjoint buf z /\ disjoint out z /\ disjoint out buf /\
      F51.mul_inv_t h z)
    (ensures  fun h0 _ h1 ->
      modifies (loc buf) h0 h1 /\
      F51.mul_inv_t h1 (gsub buf 10ul 5ul) /\
      F51.felem_fits h1 (gsub buf 5ul 5ul) (1, 2, 1, 1, 1) /\
      F51.fevalh h1 (gsub buf 5ul 5ul) == CI.pow (F51.fevalh h0 z) 1267650600228228275596796362752 /\
      F51.fevalh h1 (gsub buf 10ul 5ul) == CI.pow (F51.fevalh h0 z) 1125899906842623
    )
let crecip_1 out buf z =
  let a  = sub buf 0ul  5ul in
  let t0 = sub buf 5ul  5ul in
  let b  = sub buf 10ul 5ul in
  let c  = sub buf 15ul 5ul in
  (**) let h0 = get() in
  fsquare_times a z 1ul; // a = z ** (2 ** 1) == z ** 2
  (**) assert_norm (pow2 1 == 2);
  fsquare_times t0 a 2ul; // t0 == a ** (2 ** 2) == (z ** 2) ** 4 == z ** 8
  (**) CI.lemma_pow_mul (F51.fevalh h0 z) 2 4;
  (**) assert_norm (pow2 2 == 4);
  fmul b t0 z; // b == z0 ** 9
  (**) CI.lemma_pow_one (F51.fevalh h0 z);
  (**) CI.lemma_pow_add (F51.fevalh h0 z) 8 1;
  fmul a b a; // a == b * a == z ** 11
  (**) CI.lemma_pow_add (F51.fevalh h0 z) 9 2;
  fsquare_times t0 a 1ul; // t0 == a ** 2 == z ** 22
  (**) CI.lemma_pow_mul (F51.fevalh h0 z) 11 2;
  fmul b t0 b; // b == z ** 31
  (**) CI.lemma_pow_add (F51.fevalh h0 z) 22 9;
  fsquare_times t0 b 5ul; // t0 == b ** (2 ** 5) == z ** 992
  (**) assert_norm (pow2 5 == 32);
  (**) CI.lemma_pow_mul (F51.fevalh h0 z) 31 32;
  fmul b t0 b; // b == t0 * b == z ** 1023
  (**) CI.lemma_pow_add (F51.fevalh h0 z) 992 31;
  fsquare_times t0 b 10ul; // t0 = b ** (2 ** 1024) == z ** 1047552
  (**) assert_norm (pow2 10 == 1024);
  (**) CI.lemma_pow_mul (F51.fevalh h0 z) 1023 1024;
  fmul c t0 b; // c == z ** 1048575
  (**) CI.lemma_pow_add (F51.fevalh h0 z) 1047552 1023;
  fsquare_times t0 c 20ul; // t0 == c ** (2 ** 20) == 1099510579200
  (**) assert_norm (pow2 20 == 1048576);
  (**) CI.lemma_pow_mul (F51.fevalh h0 z) 1048575 1048576;
  fmul t0 t0 c; // t0 == z ** 1099511627775
  (**) CI.lemma_pow_add (F51.fevalh h0 z) 1099510579200 1048575;
  fsquare_times_inplace t0 10ul; // t0 == z ** 1125899906841600
  (**) CI.lemma_pow_mul (F51.fevalh h0 z) 1099511627775 1024;
  fmul b t0 b; // b == z ** 1125899906842623
  (**) CI.lemma_pow_add (F51.fevalh h0 z) 1125899906841600 1023;
  fsquare_times t0 b 50ul; // t0 == z ** 1267650600228228275596796362752;
  (**) assert_norm (pow2 50 = 1125899906842624);
  (**) CI.lemma_pow_mul (F51.fevalh h0 z) 1125899906842623 1125899906842624


inline_for_extraction noextract
val crecip_2:
     out:felem
  -> buf:lbuffer uint64 20ul
  -> z:felem ->
  Stack unit
    (requires fun h -> live h out /\ live h buf /\ live h z /\
      disjoint buf z /\ disjoint out z /\ disjoint out buf /\
      F51.mul_inv_t h (gsub buf 10ul 5ul) /\
      F51.felem_fits h (gsub buf 5ul 5ul) (1, 2, 1, 1, 1) /\
      F51.fevalh h (gsub buf 5ul 5ul) == CI.pow (F51.fevalh h z) 1267650600228228275596796362752 /\
      F51.fevalh h (gsub buf 10ul 5ul) == CI.pow (F51.fevalh h z) 1125899906842623 /\
      F51.mul_inv_t h z)
    (ensures  fun h0 _ h1 ->
      modifies (loc buf |+| loc out) h0 h1 /\
      F51.mul_inv_t h1 out /\
      F51.fevalh h1 out == CI.pow (F51.fevalh h0 z)  7237005577332262213973186563042994240829374041602535252466099000494570602494
    )
let crecip_2 out buf z =
  let a  = sub buf 0ul  5ul in
  let t0 = sub buf 5ul  5ul in
  let b  = sub buf 10ul 5ul in
  let c  = sub buf 15ul 5ul in
  let h0 = get() in
  (**) assert_norm (pow2 1 == 2);
  fsquare_times a z 1ul; // a == z ** 2;
  fmul c t0 b; // c == z ** 1267650600228229401496703205375
  (**) CI.lemma_pow_add (F51.fevalh h0 z) 1267650600228228275596796362752 1125899906842623;
  fsquare_times t0 c 100ul; // t0 == z ** 1606938044258990275541962092339894951921974764381296132096000
  (**) assert_norm (pow2 100 = 1267650600228229401496703205376);
  (**) CI.lemma_pow_mul (F51.fevalh h0 z) 1267650600228229401496703205375 1267650600228229401496703205376;
  fmul t0 t0 c; // t0 == z ** 1606938044258990275541962092341162602522202993782792835301375
  (**) CI.lemma_pow_add (F51.fevalh h0 z) 1606938044258990275541962092339894951921974764381296132096000 1267650600228229401496703205375;
  (**) assert_norm (pow2 50 == 1125899906842624);
  fsquare_times_inplace t0 50ul; // t0 == z ** 1809251394333065553493296640760748560207343510400633813116523624223735808000
  (**) CI.lemma_pow_mul (F51.fevalh h0 z) 1606938044258990275541962092341162602522202993782792835301375 1125899906842624;
  fmul t0 t0 b; // t0 == z ** 1809251394333065553493296640760748560207343510400633813116524750123642650623
  (**) CI.lemma_pow_add (F51.fevalh h0 z) 1809251394333065553493296640760748560207343510400633813116523624223735808000 1125899906842623;
  (**) assert_norm (pow2 2 == 4);
  fsquare_times_inplace t0 2ul; // t0 == z ** 7237005577332262213973186563042994240829374041602535252466099000494570602492
  (**) CI.lemma_pow_mul (F51.fevalh h0 z) 1809251394333065553493296640760748560207343510400633813116524750123642650623 4;
  fmul out t0 a;
  (**) CI.lemma_pow_add (F51.fevalh h0 z) 7237005577332262213973186563042994240829374041602535252466099000494570602492 2

val pow2_252m2:
    out:felem
  -> z:felem ->
  Stack unit
    (requires fun h -> live h out /\ live h z /\ disjoint out z /\ F51.mul_inv_t h z)
    (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
      F51.mul_inv_t h1 out /\
      F51.fevalh h1 out == F51.fevalh h0 z `SC.fpow` ((SC.prime + 3) / 8)
    )
let pow2_252m2 out z =
  push_frame();
  let buf = create 20ul (u64 0) in
  let h0 = get() in
  crecip_1 out buf z;
  crecip_2 out buf z;
  CI.lemma_fpow_is_pow (F51.fevalh h0 z) 7237005577332262213973186563042994240829374041602535252466099000494570602494;
  assert_norm (7237005577332262213973186563042994240829374041602535252466099000494570602494 == (SC.prime + 3) / 8);
  pop_frame()
