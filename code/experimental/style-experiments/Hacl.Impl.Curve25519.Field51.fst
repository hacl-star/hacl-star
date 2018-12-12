module Hacl.Impl.Curve25519.Field51

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.Sequence
open Lib.IntTypes
open Lib.Buffer

include Hacl.Spec.Curve25519.Field51

module ST = FStar.HyperStack.ST

#reset-options "--z3rlimit 20"

let felem = lbuffer uint64 5ul
let felem_wide = lbuffer uint128 5ul

noextract
val as_nat: h:mem -> e:felem -> GTot nat
let as_nat h e =
  let s = as_seq h e in
  let s0 = s.[0] in
  let s1 = s.[1] in
  let s2 = s.[2] in
  let s3 = s.[3] in
  let s4 = s.[4] in
  as_nat5 (s0, s1, s2, s3, s4)

noextract
val wide_as_nat: h:mem -> e:felem_wide -> GTot nat
let wide_as_nat h e =
  let s = as_seq h e in
  let s0 = s.[0] in
  let s1 = s.[1] in
  let s2 = s.[2] in
  let s3 = s.[3] in
  let s4 = s.[4] in
  wide_as_nat5 (s0, s1, s2, s3, s4)

noextract
val felem_fits: h:mem -> f:felem -> m:scale64_5 -> Type0
let felem_fits h f m =
  let s = as_seq h f in
  let s0 = s.[0] in
  let s1 = s.[1] in
  let s2 = s.[2] in
  let s3 = s.[3] in
  let s4 = s.[4] in
  felem_fits5 (s0, s1, s2, s3, s4) m

noextract
val felem_wide_fits: h:mem -> f:felem_wide -> m:scale128_5 -> Type0
let felem_wide_fits h f m =
  let s = as_seq h f in
  let s0 = s.[0] in
  let s1 = s.[1] in
  let s2 = s.[2] in
  let s3 = s.[3] in
  let s4 = s.[4] in
  felem_wide_fits5 (s0, s1, s2, s3, s4) m


inline_for_extraction
val create_felem:
  unit -> StackInline felem
  (requires fun _ -> True)
  (ensures  fun h0 f h1 ->
    stack_allocated f h0 h1 (Seq.create 5 (u64 0)) /\
    as_nat h1 f == 0)
let create_felem () = create 5ul (u64 0)

inline_for_extraction
val create_wide:
  unit -> StackInline felem_wide
  (requires fun _ -> True)
  (ensures  fun h0 f h1 ->
    stack_allocated f h0 h1 (Seq.create 5 (u128 0)) /\
    wide_as_nat h1 f == 0)
let create_wide () = create 5ul (u128 0)


inline_for_extraction
val set_bit1:
    f:felem
  -> i:size_t{v i < 255}
  -> Stack unit
    (requires fun h -> live h f)
    (ensures  fun h0 _ h1 -> modifies (loc f) h0 h1)
let set_bit1 f i =
  f.(i /. size 51) <- f.(i /. size 51) |. (u64 1 <<. (i %. size 51))

inline_for_extraction
val set_bit0:
    f:felem
  -> i:size_t{v i < 255}
  -> Stack unit
    (requires fun h -> live h f)
    (ensures  fun h0 _ h1 -> modifies (loc f) h0 h1)
let set_bit0 f i =
  f.(i /. size 51) <- f.(i /. size 51) &. lognot (u64 1 <<. (i %. size 51))

inline_for_extraction
val set_zero:
  f:felem -> Stack unit
  (requires fun h -> live h f)
  (ensures  fun h0 _ h1 -> modifies (loc f) h0 h1)
let set_zero f =
  f.(0ul) <- u64 0;
  f.(1ul) <- u64 0;
  f.(2ul) <- u64 0;
  f.(3ul) <- u64 0;
  f.(4ul) <- u64 0

inline_for_extraction
val copy_felem:
    f1:felem
  -> f2:felem
  -> Stack unit
    (requires fun h -> live h f1 /\ live h f2)
    (ensures  fun h0 _ h1 -> modifies (loc f1) h0 h1)
let copy_felem f1 f2 =
  f1.(size 0) <- f2.(size 0);
  f1.(size 1) <- f2.(size 1);
  f1.(size 2) <- f2.(size 2);
  f1.(size 3) <- f2.(size 3);
  f1.(size 4) <- f2.(size 4)

val fadd:
    out:felem
  -> f1:felem
  -> f2:felem
  -> Stack unit
    (requires fun h ->
      live h f1 /\ live h f2 /\ live h out /\
      felem_fits h f1 (1, 2, 1, 1, 1) /\
      felem_fits h f2 (1, 2, 1, 1, 1))
    (ensures fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
      felem_fits h1 out (2, 4, 2, 2, 2) /\
      as_nat h1 out == as_nat h0 f1 + as_nat h0 f2)
[@ CInline]
let fadd out f1 f2 =
  let f10 = f1.(0ul) in
  let f20 = f2.(0ul) in
  let f11 = f1.(1ul) in
  let f21 = f2.(1ul) in
  let f12 = f1.(2ul) in
  let f22 = f2.(2ul) in
  let f13 = f1.(3ul) in
  let f23 = f2.(3ul) in
  let f14 = f1.(4ul) in
  let f24 = f2.(4ul) in
  out.(0ul) <- f10 +! f20;
  out.(1ul) <- f11 +! f21;
  out.(2ul) <- f12 +! f22;
  out.(3ul) <- f13 +! f23;
  out.(4ul) <- f14 +! f24

val fsub:
    out:felem
  -> f1:felem
  -> f2:felem
  -> Stack unit
    (requires fun h ->
      live h f1 /\ live h f2 /\ live h out /\
      felem_fits h f1 (1, 2, 1, 1, 1) /\
      felem_fits h f2 (1, 2, 1, 1, 1))
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
      felem_fits h1 out (9, 10, 9, 9, 9))
[@ CInline]
let fsub out f1 f2 =
  let f10 = f1.(0ul) in
  let f20 = f2.(0ul) in
  let f11 = f1.(1ul) in
  let f21 = f2.(1ul) in
  let f12 = f1.(2ul) in
  let f22 = f2.(2ul) in
  let f13 = f1.(3ul) in
  let f23 = f2.(3ul) in
  let f14 = f1.(4ul) in
  let f24 = f2.(4ul) in
  out.(0ul) <- f10 +! u64 0x3fffffffffff68 -! f20;
  out.(1ul) <- f11 +! u64 0x3ffffffffffff8 -! f21;
  out.(2ul) <- f12 +! u64 0x3ffffffffffff8 -! f22;
  out.(3ul) <- f13 +! u64 0x3ffffffffffff8 -! f23;
  out.(4ul) <- f14 +! u64 0x3ffffffffffff8 -! f24

#reset-options "--z3rlimit 100"

val smul_felem:
    out:felem_wide
  -> u1:uint64
  -> f2:felem
  -> Stack unit
    (requires fun h -> live h out /\ live h f2)
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
      wide_as_nat h1 out == uint_v u1 * as_nat h0 f2)
[@ CInline]
let smul_felem out u1 f2 =
  let f20 = f2.(size 0) in
  let f21 = f2.(size 1) in
  let f22 = f2.(size 2) in
  let f23 = f2.(size 3) in
  let f24 = f2.(size 4) in
  out.(size 0) <- mul64_wide u1 f20;
  out.(size 1) <- mul64_wide u1 f21;
  out.(size 2) <- mul64_wide u1 f22;
  out.(size 3) <- mul64_wide u1 f23;
  out.(size 4) <- mul64_wide u1 f24

val mul_felem:
    out:felem_wide
  -> f1:felem
  -> r:felem
  -> r19:felem
  -> Stack unit
    (requires fun h ->
      live h out /\ live h f1 /\ live h r /\ live h r19 /\
      felem_fits h f1 (9, 10, 9, 9, 9) /\
      felem_fits h r (9, 10, 9, 9, 9) /\
      felem_fits h r19 (171, 190, 171, 171, 171))
    (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
      felem_wide_fits h1 out (6579, 4797, 3340, 1881, 423))
[@ CInline]
let mul_felem out f1 r r19 =
  let f10 = f1.(size 0) in
  let f11 = f1.(size 1) in
  let f12 = f1.(size 2) in
  let f13 = f1.(size 3) in
  let f14 = f1.(size 4) in

  let r0 = r.(size 0) in
  let r1 = r.(size 1) in
  let r2 = r.(size 2) in
  let r3 = r.(size 3) in
  let r4 = r.(size 4) in

  let r190 = r19.(size 0) in
  let r191 = r19.(size 1) in
  let r192 = r19.(size 2) in
  let r193 = r19.(size 3) in
  let r194 = r19.(size 4) in
  let (o0,o1,o2,o3,o4) = mul_felem5 (f10,f11,f12,f13,f14) (r0,r1,r2,r3,r4) (r190,r191,r192,r193,r194) in
  out.(size 0) <- o0;
  out.(size 1) <- o1;
  out.(size 2) <- o2;
  out.(size 3) <- o3;
  out.(size 4) <- o4

val carry_wide:
    out:felem
  -> inp:felem_wide
  -> Stack unit
    (requires fun h ->
      live h out /\ live h inp /\
      felem_wide_fits h inp (6579, 4797, 3340, 1881, 423))
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
      felem_fits h1 out (1, 2, 1, 1, 1))
[@ CInline]
let carry_wide out inp =
  let i0 = inp.(size 0) in
  let i1 = inp.(size 1) in
  let i2 = inp.(size 2) in
  let i3 = inp.(size 3) in
  let i4 = inp.(size 4) in
  let (tmp0, tmp1, tmp2, tmp3, tmp4) = carry_wide5 (i0, i1, i2, i3, i4) in
  out.(size 0) <- tmp0;
  out.(size 1) <- tmp1;
  out.(size 2) <- tmp2;
  out.(size 3) <- tmp3;
  out.(size 4) <- tmp4

val carry_felem:
    f:felem
  -> Stack unit
    (requires fun h -> live h f)
    (ensures  fun h0 _ h1 -> modifies (loc f) h0 h1)
[@ CInline]
let carry_felem f =
  let f0 = f.(size 0) in
  let f1 = f.(size 1) in
  let f2 = f.(size 2) in
  let f3 = f.(size 3) in
  let f4 = f.(size 4) in
  let tmp0,carry = carry51 f0 (u64 0) in
  admit();
  let tmp1,carry = carry51 f1 carry in
  let tmp2,carry = carry51 f2 carry in
  let tmp3,carry = carry51 f3 carry in
  let tmp4,carry = carry51 f4 carry in
  let tmp0,carry = carry51 tmp0 (carry *. u64 19) in
  let tmp1 = tmp1 +. carry in
  f.(size 0) <- tmp0;
  f.(size 1) <- tmp1;
  f.(size 2) <- tmp2;
  f.(size 3) <- tmp3;
  f.(size 4) <- tmp4

val fmul:
    out:felem
  -> f1:felem
  -> f2:felem
  -> Stack unit
    (requires fun h ->
      live h out /\ live h f1 /\ live h f2 /\
      felem_fits h f1 (9, 10, 9, 9, 9) /\
      felem_fits h f2 (9, 10, 9, 9, 9))
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
      felem_fits h1 out (1, 2, 1, 1, 1))
[@ CInline]
let fmul out f1 f2 =
  let f10 = f1.(size 0) in
  let f11 = f1.(size 1) in
  let f12 = f1.(size 2) in
  let f13 = f1.(size 3) in
  let f14 = f1.(size 4) in

  let f20 = f2.(size 0) in
  let f21 = f2.(size 1) in
  let f22 = f2.(size 2) in
  let f23 = f2.(size 3) in
  let f24 = f2.(size 4) in

  let (o0,o1,o2,o3,o4) = fmul5 (f10,f11,f12,f13,f14) (f20,f21,f22,f23,f24) in
  out.(size 0) <- o0;
  out.(size 1) <- o1;
  out.(size 2) <- o2;
  out.(size 3) <- o3;
  out.(size 4) <- o4

[@ CInline]
val fmul2: out1:felem -> out2:felem -> f1:felem -> f2:felem -> f3:felem -> f4:felem -> Stack unit
                   (requires (fun h -> live h out1 /\ live h out2 /\ live h f1 /\ live h f2 /\ live h f3 /\ live h f4))
		   (ensures (fun h0 _ h1 -> modifies (loc out1 |+| loc out2) h0 h1))
[@ CInline]
let fmul2 out1 out2 f1 f2 f3 f4 = admit();
  push_frame();
  let tmp1 = create_felem() in
  let tmp2 = create_felem() in
  let tmp_w1 = create_wide () in
  let tmp_w2 = create_wide () in
  tmp1.(1ul) <- f2.(1ul) *. u64 19;
  tmp1.(2ul) <- f2.(2ul) *. u64 19;
  tmp1.(3ul) <- f2.(3ul) *. u64 19;
  tmp1.(4ul) <- f2.(4ul) *. u64 19;
  tmp2.(1ul) <- f4.(1ul) *. u64 19;
  tmp2.(2ul) <- f4.(2ul) *. u64 19;
  tmp2.(3ul) <- f4.(3ul) *. u64 19;
  tmp2.(4ul) <- f4.(4ul) *. u64 19;
  mul_felem tmp_w1 f1 f2 tmp1;
  mul_felem tmp_w2 f3 f4 tmp2;
  carry_wide out1 tmp_w1;
  carry_wide out2 tmp_w2;
  pop_frame()

val fmul1:
    out:felem
  -> f1:felem
  -> f2:uint64
  -> Stack unit
    (requires fun h ->
      live h out /\ live h f1 /\
      felem_fits h f1 (9, 10, 9, 9, 9) /\
      felem_fits1 f2 1)
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
      felem_fits h1 out (1, 2, 1, 1, 1))
[@ CInline]
let fmul1 out f1 f2 = admit();
  push_frame();
  let tmp_w = create_wide () in
  smul_felem tmp_w f2 f1;
  let carry = carry_wide out tmp_w in
  pop_frame()

[@ CInline]
val fsqr_: out:felem_wide -> f1:felem -> Stack unit
                   (requires (fun h -> live h out /\ live h f1))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
[@ CInline]
let fsqr_ out f =
  let f0 = f.(0ul) in
  let f1 = f.(1ul) in
  let f2 = f.(2ul) in
  let f3 = f.(3ul) in
  let f4 = f.(4ul) in
  let d0 = u64 2 *. f0 in
  let d1 = u64 2 *. f1 in
  let d2 = u64 38 *. f2 in
  let d3 = u64 19 *. f3 in
  let d419 = u64 19 *. f4 in
  let d4 = u64 2 *. d419 in
  let s0 = (mul64_wide f0 f0) +. (mul64_wide d4 f1) +. (mul64_wide d2 f3) in
  let s1 = (mul64_wide d0 f1) +. (mul64_wide d4 f2) +. (mul64_wide d3 f3) in
  let s2 = (mul64_wide d0 f2) +. (mul64_wide f1 f1) +. (mul64_wide d4 f3) in
  let s3 = (mul64_wide d0 f3) +. (mul64_wide d1 f2) +. (mul64_wide f4 d419) in
  let s4 = (mul64_wide d0 f4) +. (mul64_wide d1 f3) +. (mul64_wide f2 f2) in
  out.(0ul) <- s0;
  out.(1ul) <- s1;
  out.(2ul) <- s2;
  out.(3ul) <- s3;
  out.(4ul) <- s4

[@ CInline]
val fsqr: out:felem -> f1:felem -> Stack unit
                   (requires (fun h -> live h out /\ live h f1))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
[@ CInline]
let fsqr out f = admit();
  push_frame();
  let tmp_w = create_wide () in
  fsqr_ tmp_w f;
  carry_wide out tmp_w;
  pop_frame()

[@ CInline]
val fsqr2: out1:felem -> out2:felem -> f1:felem -> f2:felem -> Stack unit
                   (requires (fun h -> live h out1 /\ live h out2 /\ live h f1 /\ live h f2))
		   (ensures (fun h0 _ h1 -> modifies (loc out1 |+| loc out2) h0 h1))
[@ CInline]
let fsqr2 out1 out2 f1 f2 = admit();
  push_frame();
  let tmp_w1 = create_wide () in
  let tmp_w2 = create_wide () in
  fsqr_ tmp_w1 f1;
  fsqr_ tmp_w2 f2;
  carry_wide out1 tmp_w1;
  carry_wide out2 tmp_w2;
  pop_frame()

inline_for_extraction
val load_felem:
    f:felem
  -> u64s:lbuffer uint64 4ul
  -> Stack unit
    (requires fun h -> live h u64s /\ live h f)
    (ensures  fun h0 _ h1 -> modifies (loc f) h0 h1)
let load_felem f u64s =
  let f0l = u64s.(0ul) &. mask51 in
  let f0h = u64s.(0ul) >>. 51ul in
  let f1l = (u64s.(1ul) &. u64 0x3fffffffff) <<. 13ul in
  let f1h = u64s.(1ul) >>. 38ul in
  let f2l = (u64s.(2ul) &. u64 0x1ffffff) <<. 26ul in
  let f2h = u64s.(2ul) >>. 25ul in
  let f3l = (u64s.(3ul) &. u64 0xfff) <<. 39ul in
  let f3h = u64s.(3ul) >>. 12ul in
  f.(size 0) <- f0l;
  f.(size 1) <- f0h ^. f1l;
  f.(size 2) <- f1h ^. f2l;
  f.(size 3) <- f2h ^. f3l;
  f.(size 4) <- f3h

let uint64_eq_mask (a:uint64) (b:uint64) : uint64 =
  let x = a ^. b in
  let minus_x = (lognot x) +. (u64 1) in
  let x_or_minus_x = x |. minus_x in
  let xnx = x_or_minus_x >>. 63ul in
  let c = xnx -. (u64 1) in
  c

let uint64_gte_mask (a:uint64) (b:uint64) : uint64 =
  let x = a in
  let y = b in
  let x_xor_y = logxor x y in
  let x_sub_y = x -. y in
  let x_sub_y_xor_y = x_sub_y ^. y in
  let q = logor x_xor_y x_sub_y_xor_y in
  let x_xor_q = logxor x q in
  let x_xor_q_ = shift_right x_xor_q 63ul in
  let c = sub_mod x_xor_q_ (u64 1) in
  c

val store_felem:
    u64s:lbuffer uint64 4ul
  -> f:felem
  -> Stack unit
    (requires fun h -> live h f /\ live h u64s)
    (ensures  fun h0 _ h1 -> modifies (union (loc u64s) (loc f)) h0 h1)
let store_felem u64s f =
  carry_felem f;
  carry_felem f;
  let f0 = f.(0ul) in
  let f1 = f.(1ul) in
  let f2 = f.(2ul) in
  let f3 = f.(3ul) in
  let f4 = f.(4ul) in
  let m0 = uint64_gte_mask f0 (u64 0x7ffffffffffed) in
  let m1 = uint64_eq_mask f1 (u64 0x7ffffffffffff) in
  let m2 = uint64_eq_mask f2 (u64 0x7ffffffffffff) in
  let m3 = uint64_eq_mask f3 (u64 0x7ffffffffffff) in
  let m4 = uint64_eq_mask f4 (u64 0x7ffffffffffff) in
  let mask = m0 &. m1 &. m2 &. m3 &. m4 in
  let f0 = f0 -. (mask &. u64 0x7ffffffffffed) in
  let f1 = f1 -. (mask &. u64 0x7ffffffffffff) in
  let f2 = f2 -. (mask &. u64 0x7ffffffffffff) in
  let f3 = f3 -. (mask &. u64 0x7ffffffffffff) in
  let f4 = f4 -. (mask &. u64 0x7ffffffffffff) in
  let f0 = f0 ^. (f1 <<. 51ul) in
  let f1 = (f1 >>. 13ul) ^. (f2 <<. 38ul) in
  let f2 = (f2 >>. 26ul) ^. (f3 <<. 25ul) in
  let f3 = (f3 >>. 39ul) ^. (f4 <<. 12ul) in
  u64s.(0ul) <- f0;
  u64s.(1ul) <- f1;
  u64s.(2ul) <- f2;
  u64s.(3ul) <- f3
