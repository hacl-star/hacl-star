module Hacl.Impl.Ed25519.RecoverX

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum25519

module F51 = Hacl.Impl.Ed25519.Field51
module S51 = Hacl.Spec.Curve25519.Field51.Definition

module SC = Spec.Curve25519
module SE = Spec.Ed25519

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
let elemB = lbuffer uint64 5ul

inline_for_extraction noextract
val recover_x_step_1:
    x2:elemB
  -> y:elemB ->
  Stack unit
    (requires fun h -> live h x2 /\ live h y /\ disjoint x2 y /\
      F51.mul_inv_t h y
    )
    (ensures  fun h0 _ h1 -> modifies (loc x2) h0 h1 /\
      F51.fevalh h1 x2 == F51.as_nat h1 x2 /\
      F51.mul_inv_t h1 x2 /\
      (let y = F51.fevalh h0 y in
       let x2 = F51.fevalh h1 x2 in
       let y2 = y `SC.fmul` y in
       x2 == (y2 `SC.fsub` SC.one) `SC.fmul` (SE.modp_inv ((SE.d `SC.fmul` y2) `SC.fadd` SC.one)))
    )
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
  fmul x2 one dyyi; //
  reduce x2;
  pop_frame()

val is_0:
  x:elemB ->
  Stack bool
    (requires fun h -> live h x /\ F51.as_nat h x == F51.fevalh h x)
    (ensures  fun h0 b h1 -> h0 == h1 /\
      (b <==> (F51.fevalh h0 x == SC.zero))
    )
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
    (requires fun h -> live h x /\ F51.mul_inv_t h x)
    (ensures  fun h0 _ h1 -> modifies (loc x) h0 h1 /\
      F51.mul_inv_t h1 x /\
      F51.fevalh h1 x == F51.fevalh h0 x `SC.fmul` SE.modp_sqrt_m1
    )
let mul_modp_sqrt_m1 x =
  push_frame();
  let sqrt_m1 = create 5ul (u64 0) in
  make_u64_5 sqrt_m1
    (u64 0x00061b274a0ea0b0) (u64 0x0000d5a5fc8f189d) (u64 0x0007ef5e9cbd0c60) (u64 0x00078595a6804c9e) (u64 0x0002b8324804fc1d);

  assert_norm (S51.as_nat5 (u64 0x00061b274a0ea0b0, u64 0x0000d5a5fc8f189d, u64 0x0007ef5e9cbd0c60, u64 0x00078595a6804c9e, u64 0x0002b8324804fc1d) == SE.modp_sqrt_m1);
  fmul x x sqrt_m1;
  pop_frame()

inline_for_extraction noextract
val gte_q:
  x:elemB ->
  Stack bool
    (requires fun h -> live h x /\
      F51.felem_fits h x (1, 1, 1, 1, 1)
    )
    (ensures  fun h0 b h1 -> h0 == h1 /\
      (b <==> (F51.as_nat h0 x >= SC.prime))
    )
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
val x_mod_2:
  x:felem ->
  Stack uint64
    (requires fun h -> live h x)
    (ensures  fun h0 z h1 -> h0 == h1 /\ v z < 2 /\
      v z == F51.as_nat h0 x % 2
    )
let x_mod_2 x =
  (**) let h0 = get() in
  let x0 = x.(0ul) in
  let z  = x0 &. u64 1 in
  mod_mask_lemma x0 1ul;
  Lib.IntTypes.Compatibility.uintv_extensionality (u64 1) (mod_mask #U64 1ul);
  z

inline_for_extraction noextract
val recover_x_step_2:
    x:elemB
  -> sign:uint64
  -> x2:elemB ->
  Stack uint8
    (requires fun h -> live h x2 /\ live h x /\ disjoint x x2 /\
      F51.mul_inv_t h x /\
      F51.fevalh h x2 == F51.as_nat h x2
    )
    (ensures  fun h0 z h1 -> modifies (loc x) h0 h1 /\
      F51.mul_inv_t h1 x /\
      (if F51.fevalh h0 x2 = 0 then (
        if v sign = 0 then F51.fevalh h1 x = 0 /\ z == u8 1
        else h0 == h1 /\ z == u8 0
        )
       else h0 == h1 /\ z == u8 2)
    )
let recover_x_step_2 x sign x2 =
  let open Lib.RawIntTypes in
  let open FStar.UInt64 in
  let h0 = get() in
  let x2_is_0 = is_0 x2 in
  let h1 = get() in
  if x2_is_0 then (
    assert (uint_v #U64 sign = Lib.IntTypes.v #U64 #SEC sign);
    if u64_to_UInt64 sign =^ 0uL then (
      make_zero x;
      u8 1
    ) else u8 0
  ) else u8 2

inline_for_extraction noextract
val recover_x_step_3:
  tmp:lbuffer uint64 20ul ->
  Stack unit
    (requires fun h -> live h tmp /\ F51.mul_inv_t h (gsub tmp 0ul 5ul))
    (ensures  fun h0 _ h1 -> modifies (loc tmp) h0 h1 /\
      F51.mul_inv_t h1 (gsub tmp 5ul 5ul) /\
      F51.fevalh h0 (gsub tmp 0ul 5ul) == F51.fevalh h1 (gsub tmp 0ul 5ul) /\
      F51.mul_inv_t h1 (gsub tmp 0ul 5ul) /\
      (let x2 = F51.fevalh h0 (gsub tmp 0ul 5ul) in
       let x = x2 `SC.fpow` ((SC.prime + 3) / 8) in
       let x = if ((x `SC.fmul` x) `SC.fsub` x2) <> 0 then (x `SC.fmul` SE.modp_sqrt_m1) else x in
       F51.fevalh h1 (gsub tmp 5ul 5ul) == x
      )
    )
let recover_x_step_3 tmp =
  let x2  = sub tmp 0ul 5ul in
  let x3  = sub tmp 5ul 5ul in
  let t0  = sub tmp 10ul 5ul in
  let t1  = sub tmp 15ul 5ul in
  Hacl.Impl.Ed25519.Pow2_252m2.pow2_252m2 x3 x2;
  fsquare t0 x3;
  copy t1 x2;
  fdifference t1 t0;
  reduce_513 t1;
  reduce t1;
  let t1_is_0 = is_0 t1 in
  if t1_is_0 then ()
  else (
    mul_modp_sqrt_m1 x3
  )
//  reduce x3

inline_for_extraction noextract
val recover_x_step_4:
  tmp:lbuffer uint64 20ul ->
  Stack bool
    (requires fun h -> live h tmp /\
      F51.mul_inv_t h (gsub tmp 0ul 5ul) /\
      F51.mul_inv_t h (gsub tmp 5ul 5ul)
    )
    (ensures  fun h0 z h1 -> modifies (loc tmp) h0 h1 /\
      F51.fevalh h0 (gsub tmp 0ul 5ul) == F51.fevalh h1 (gsub tmp 0ul 5ul) /\
      F51.mul_inv_t h1 (gsub tmp 0ul 5ul) /\
      F51.fevalh h0 (gsub tmp 5ul 5ul) == F51.fevalh h1 (gsub tmp 5ul 5ul) /\
      F51.mul_inv_t h1 (gsub tmp 5ul 5ul) /\
      (let u = F51.fevalh h0 (gsub tmp 5ul 5ul) in
       let v = F51.fevalh h0 (gsub tmp 0ul 5ul) in
       let y = (u `SC.fmul` u) `SC.fsub` v in
       (z <==> y == SC.zero)
      )
    )
let recover_x_step_4 tmp =
  let h0 = ST.get() in
  let x2  = sub tmp 0ul 5ul in
  let x3  = sub tmp 5ul 5ul in
  let t0  = sub tmp 10ul 5ul in
  let t1  = sub tmp 15ul 5ul in
  fsquare t0 x3;
  copy t1 x2;
  fdifference t1 t0;
  reduce_513 t1;
  reduce t1;
  is_0 t1

inline_for_extraction noextract
val recover_x_step_5:
    x:elemB
  -> y:elemB
  -> sign:uint64{v sign = 0 \/ v sign = 1}
  -> tmp:lbuffer uint64 20ul ->
  Stack unit
    (requires fun h -> live h x /\ live h tmp /\ live h y /\
      disjoint x y /\ disjoint tmp x /\ disjoint tmp y /\
      F51.mul_inv_t h (gsub tmp 5ul 5ul) /\
      (let y = F51.as_nat h y in
       let sign = (uint_v #U64 sign <> 0) in
       let x = F51.fevalh h (gsub tmp 5ul 5ul) in
       let x2 = F51.fevalh h (gsub tmp  0ul 5ul) in
       ((x `SC.fmul` x) `SC.fsub` x2) == SC.zero /\
       SE.recover_x y sign ==
           (if ((x `SC.fmul` x) `SC.fsub` x2) <> SC.zero then None
           else (
             let x = if (x % 2 = 1) <> sign then (SC.prime - x) % SC.prime else x in
             Some x)
             ))
    )
    (ensures  fun h0 _ h1 -> modifies (loc x |+| loc tmp) h0 h1 /\
      F51.mul_inv_t h1 x /\
      F51.fevalh h1 x == Some?.v (SE.recover_x (F51.as_nat h0 y) (uint_v #U64 sign <> 0))
    )

let recover_x_step_5 x y sign tmp =
  let x3  = sub tmp 5ul 5ul in
  let t0  = sub tmp 10ul 5ul in
  let hi = get() in
  reduce x3;
  let x0 = x_mod_2 x3 in
  let h0 = get() in
  let open Lib.RawIntTypes in
  let open FStar.UInt64 in
  if not(u64_to_UInt64 x0 =^ u64_to_UInt64 sign) then (
    make_zero t0;
    fdifference x3 t0;
    reduce_513 x3;
    reduce x3;
    (**) assert_norm (SC.prime % SC.prime = SC.zero % SC.prime);
    (**) FStar.Math.Lemmas.mod_add_both SC.prime SC.zero (- (F51.fevalh h0 x3)) SC.prime
    );
  copy x x3

inline_for_extraction noextract
val recover_x_:
    x:elemB
  -> y:elemB
  -> sign:uint64{v sign = 0 \/ v sign = 1}
  -> tmp:lbuffer uint64 20ul ->
  Stack bool
    (requires fun h ->
      live h tmp /\ live h x /\ live h y /\
      disjoint x y /\ disjoint tmp x /\ disjoint tmp y /\
      F51.mul_inv_t h x /\
      F51.felem_fits h y (1, 1, 1, 1, 1)
      )
    (ensures  fun h0 z h1 -> modifies (loc x |+| loc tmp) h0 h1 /\
      (z ==> F51.mul_inv_t h1 x) /\
      (let res = SE.recover_x (F51.as_nat h0 y) (uint_v #U64 sign <> 0) in
      (Some? res <==> z) /\
      (Some? res ==> F51.fevalh h1 x == Some?.v res))
    )

#restart-solver

let recover_x_ x y sign tmp =
  let x2 = sub tmp 0ul 5ul in
  let open Lib.RawIntTypes in
  let open FStar.UInt8 in
  let h0 = get() in

  let b = gte_q y in
  let res =
  if b then false
  else (
    (**) FStar.Math.Lemmas.small_mod (F51.as_nat h0 y) SC.prime;
    recover_x_step_1 x2 y;
    let z = recover_x_step_2 x sign x2 in
    if (u8_to_UInt8 z =^ 0uy) then false
    else if (u8_to_UInt8 z =^ 1uy) then true
    else (
      recover_x_step_3 tmp;
      let z = recover_x_step_4 tmp in
      let h1 = get() in
      if z = false then false
      else (
        recover_x_step_5 x y sign tmp;
        true)
    )
   ) in
   res


val recover_x:
    x:lbuffer uint64 5ul
  -> y:lbuffer uint64 5ul
  -> sign:uint64{v sign = 0 \/ v sign = 1} ->
  Stack bool
    (requires fun h -> live h x /\ live h y /\ disjoint x y /\
      F51.mul_inv_t h x /\
      F51.felem_fits h y (1, 1, 1, 1, 1)
    )
    (ensures  fun h0 z h1 -> modifies (loc x) h0 h1 /\
      (z ==> F51.mul_inv_t h1 x) /\
      (let res = SE.recover_x (F51.as_nat h0 y) (uint_v #U64 sign <> 0) in
      (Some? res <==> z) /\
      (Some? res ==> F51.fevalh h1 x == Some?.v res))
    )
let recover_x x y sign =
  push_frame();
  let tmp = create 20ul (u64 0) in
  let res = recover_x_ x y sign tmp in
  pop_frame();
  res
