module Hacl.Impl.Ed25519.RecoverX

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum25519

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
let elemB = lbuffer uint64 5ul

inline_for_extraction noextract
val recover_x_step_1:
    x2:elemB
  -> y:elemB ->
  Stack unit
    (requires fun h -> live h x2 /\ live h y /\ disjoint x2 y)
    (ensures  fun h0 _ h1 -> modifies (loc x2) h0 h1)
let recover_x_step_1 x2 y =
  push_frame();
  let tmp = create 25ul (u64 0) in
  let one = sub tmp 0ul 5ul in
  let y2  = sub tmp 5ul 5ul in
  let dyyi = sub tmp 10ul 5ul in
  let dyy = sub tmp 15ul 5ul in
  make_one one;
  fsquare y2 y; // y2 = y `fmul` y
  times_d dyy y2; // dyy = d `fmul` (y `fmul` y)
  fsum dyy one;   // dyy = (d `fmul` (y `fmul` y)) `fadd` one
  reduce_513 dyy;
  inverse dyyi dyy; // dyyi = modp_inv ((d `fmul` (y `fmul` y)) `fadd` one)
  fdifference one y2; // one = (y `fmul` y) `fsub` 1
  fmul x2 dyyi one; //
  reduce x2;
  pop_frame()

val is_0:
  x:elemB ->
  Stack bool
    (requires fun h -> live h x)
    (ensures  fun h0 b h1 -> h0 == h1)
let is_0 x =
  let open Lib.RawIntTypes in
  let open FStar.UInt64 in
  let x0 = x.(0ul) in
  let x1 = x.(1ul) in
  let x2 = x.(2ul) in
  let x3 = x.(3ul) in
  let x4 = x.(4ul) in
  (u64_to_UInt64 x0 =^ 0uL &&
   u64_to_UInt64 x1 =^ 0uL &&
   u64_to_UInt64 x2 =^ 0uL &&
   u64_to_UInt64 x3 =^ 0uL &&
   u64_to_UInt64 x4 =^ 0uL)

val mul_modp_sqrt_m1:
  x:elemB ->
  Stack unit
    (requires fun h -> live h x)
    (ensures  fun h0 _ h1 -> modifies (loc x) h0 h1)
let mul_modp_sqrt_m1 x =
  push_frame();
  let sqrt_m1 = create 5ul (u64 0) in
  make_u64_5 sqrt_m1
    (u64 0x00061b274a0ea0b0) (u64 0x0000d5a5fc8f189d) (u64 0x0007ef5e9cbd0c60) (u64 0x00078595a6804c9e) (u64 0x0002b8324804fc1d);
  fmul x x sqrt_m1;
  pop_frame()

inline_for_extraction noextract
val gte_q:
  x:elemB ->
  Stack bool
    (requires fun h -> live h x)
    (ensures  fun h0 b h1 -> h0 == h1)
let gte_q x =
  let open Lib.RawIntTypes in
  let open FStar.UInt64 in
  let x0 = x.(0ul) in
  let x1 = x.(1ul) in
  let x2 = x.(2ul) in
  let x3 = x.(3ul) in
  let x4 = x.(4ul) in
  (u64_to_UInt64 x0 >=^ 0x7ffffffffffeduL &&
   u64_to_UInt64 x1 =^ 0x7ffffffffffffuL &&
   u64_to_UInt64 x2 =^ 0x7ffffffffffffuL &&
   u64_to_UInt64 x3 =^ 0x7ffffffffffffuL &&
   u64_to_UInt64 x4 =^ 0x7ffffffffffffuL)

inline_for_extraction noextract
val fdifference_norm:
    x:elemB
  -> y:elemB ->
  Stack unit
    (requires fun h -> live h x /\ live h y /\ disjoint x y)
    (ensures  fun h0 _ h1 -> modifies (loc x) h0 h1)
let fdifference_norm x y =
  fdifference x y;
  reduce_513 x;
  reduce x

inline_for_extraction noextract
val x_mod_2:
  x:felem ->
  Stack uint64
    (requires fun h -> live h x)
    (ensures  fun h0 z h1 -> h0 == h1)
let x_mod_2 x =
  let x0 = x.(0ul) in
  let z  = x0 &. u64 1 in
  z

inline_for_extraction noextract
val recover_x_step_2:
    x:elemB
  -> sign:uint64
  -> x2:elemB ->
  Stack uint8
    (requires fun h -> live h x2 /\ live h x /\ disjoint x x2)
    (ensures  fun h0 z h1 -> modifies (loc x) h0 h1)
let recover_x_step_2 x sign x2 =
  let open Lib.RawIntTypes in
  let open FStar.UInt64 in
  let x2_is_0 = is_0 x2 in
  if x2_is_0 then (
    if u64_to_UInt64 sign =^ 0uL then (
      make_zero x;
      u8 1
    ) else u8 0
  ) else u8 2

inline_for_extraction noextract
val recover_x_step_3:
  tmp:lbuffer uint64 20ul ->
  Stack unit
    (requires fun h -> live h tmp)
    (ensures  fun h0 _ h1 -> modifies (loc tmp) h0 h1)
let recover_x_step_3 tmp =
  let x2  = sub tmp 0ul 5ul in
  let x3  = sub tmp 5ul 5ul in
  let t0  = sub tmp 10ul 5ul in
  let t1  = sub tmp 15ul 5ul in
  Hacl.Impl.Ed25519.Pow2_252m2.pow2_252m2 x3 x2;
  fsquare t0 x3;
  copy t1 x2;
  fdifference_norm t1 t0;
  let t1_is_0 = is_0 t1 in
  if t1_is_0 then ()
  else (
    mul_modp_sqrt_m1 x3
  );
  reduce x3

inline_for_extraction noextract
val recover_x_step_4:
  tmp:lbuffer uint64 20ul ->
  Stack bool
    (requires fun h -> live h tmp)
    (ensures  fun h0 z h1 -> modifies (loc tmp) h0 h1)
let recover_x_step_4 tmp =
  let h0 = ST.get() in
  let x2  = sub tmp 0ul 5ul in
  let x3  = sub tmp 5ul 5ul in
  let t0  = sub tmp 10ul 5ul in
  let t1  = sub tmp 15ul 5ul in
  fsquare t0 x3;
  copy t1 x2;
  fdifference_norm t1 t0;
  is_0 t1

inline_for_extraction noextract
val recover_x_step_5:
    x:elemB
  -> sign:uint64
  -> tmp:lbuffer uint64 20ul ->
  Stack unit
    (requires fun h -> live h x /\ live h tmp /\ disjoint x tmp)
    (ensures  fun h0 _ h1 -> modifies (loc x |+| loc tmp) h0 h1)
let recover_x_step_5 x sign tmp =
  let x3  = sub tmp 5ul 5ul in
  let t0  = sub tmp 10ul 5ul in
  let x0 = x_mod_2 x3 in
  let open Lib.RawIntTypes in
  let open FStar.UInt64 in
  if not(u64_to_UInt64 x0 =^ u64_to_UInt64 sign) then (
    make_zero t0;
    fdifference_norm x3 t0);
  copy x x3

inline_for_extraction noextract
val recover_x_:
    x:elemB
  -> y:elemB
  -> sign:uint64
  -> tmp:lbuffer uint64 20ul ->
  Stack bool
    (requires fun h ->
      live h tmp /\ live h x /\ live h y /\
      disjoint x y /\ disjoint tmp x /\ disjoint tmp y)
    (ensures  fun h0 z h1 -> modifies (loc x |+| loc tmp) h0 h1)
let recover_x_ x y sign tmp =
  let x2 = sub tmp 0ul 5ul in
  let open Lib.RawIntTypes in
  let open FStar.UInt8 in
  let b = gte_q y in
  let res =
  if b then false
  else (
    recover_x_step_1 x2 y;
    let z = recover_x_step_2 x sign x2 in
    if (u8_to_UInt8 z =^ 0uy) then false
    else if (u8_to_UInt8 z =^ 1uy) then true
    else (
      recover_x_step_3 tmp;
      let z = recover_x_step_4 tmp in
      if z = false then false
      else (
        recover_x_step_5 x sign tmp;
        true)
    )
   ) in
   res

val recover_x:
    x:lbuffer uint64 5ul
  -> y:lbuffer uint64 5ul
  -> sign:uint64 -> //{v sign = 0 \/ v sign = 1}
  Stack bool
    (requires fun h -> live h x /\ live h y /\ disjoint x y)
    (ensures fun h0 z h1 -> modifies (loc x) h0 h1)
let recover_x x y sign =
  push_frame();
  let tmp = create 20ul (u64 0) in
  let res = recover_x_ x y sign tmp in
  pop_frame();
  res
