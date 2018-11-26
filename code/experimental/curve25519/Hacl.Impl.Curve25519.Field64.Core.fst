module Hacl.Impl.Curve25519.Field64.Core

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.Sequence
open Lib.IntTypes
open Lib.Buffer

module B = Lib.Buffer
module ST = FStar.HyperStack.ST

open Hacl.Spec.Curve25519.Field64.Core

#set-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 0"

val add: out:u256 -> f1:u256 -> f2:u256
  -> Stack uint64
    (requires fun h -> live h f1 /\ live h f2 /\ live h out)
    (ensures  fun h0 c h1 ->
      modifies (loc out) h0 h1 /\
      as_nat h1 out + v c * pow2 256 == as_nat h0 f1 + as_nat h0 f2)
[@ CInline]
let add out f1 f2 =
  let f10 = f1.(0ul) in
  let f20 = f2.(0ul) in
  let f11 = f1.(1ul) in
  let f21 = f2.(1ul) in
  let f12 = f1.(2ul) in
  let f22 = f2.(2ul) in
  let f13 = f1.(3ul) in
  let f23 = f2.(3ul) in
  let (carry, out4) = add4 (f10, f11, f12, f13) (f20, f21, f22, f23) in
  let (o0, o1, o2, o3) = out4 in
  out.(0ul) <- o0;
  out.(1ul) <- o1;
  out.(2ul) <- o2;
  out.(3ul) <- o3;
  carry

[@ CInline]
let add1 out f1 f2 =
  let f10 = f1.(0ul) in
  let f11 = f1.(1ul) in
  let f12 = f1.(2ul) in
  let f13 = f1.(3ul) in
  let (carry, out4) = add1 (f10, f11, f12, f13) f2 in
  let (o0, o1, o2, o3) = out4 in
  out.(0ul) <- o0;
  out.(1ul) <- o1;
  out.(2ul) <- o2;
  out.(3ul) <- o3;
  carry

val sub: out:u256 -> f1:u256 -> f2:u256
  -> Stack uint64
    (requires fun h -> live h f1 /\ live h f2 /\ live h out)
    (ensures  fun h0 c h1 ->
      modifies (loc out) h0 h1 /\
      as_nat h1 out - v c * pow2 256 == as_nat h0 f1 - as_nat h0 f2)
[@ CInline]
let sub out f1 f2 =
  let f10 = f1.(0ul) in
  let f20 = f2.(0ul) in
  let f11 = f1.(1ul) in
  let f21 = f2.(1ul) in
  let f12 = f1.(2ul) in
  let f22 = f2.(2ul) in
  let f13 = f1.(3ul) in
  let f23 = f2.(3ul) in
  let (carry, out4) = sub4 (f10, f11, f12, f13) (f20, f21, f22, f23) in
  let (o0, o1, o2, o3) = out4 in
  out.(0ul) <- o0;
  out.(1ul) <- o1;
  out.(2ul) <- o2;
  out.(3ul) <- o3;
  carry

val sub1: out:u256 -> f1:u256 -> f2:uint64
  -> Stack uint64
    (requires fun h -> live h f1 /\ live h out)
    (ensures  fun h0 c h1 ->
      modifies (loc out) h0 h1 /\
      as_nat h1 out - v c * pow2 256 == as_nat h0 f1 - v f2)
[@ CInline]
let sub1 out f1 f2 =
  let f10 = f1.(0ul) in
  let f11 = f1.(1ul) in
  let f12 = f1.(2ul) in
  let f13 = f1.(3ul) in
  let (carry, out4) = sub1 (f10, f11, f12, f13) f2 in
  let (o0, o1, o2, o3) = out4 in
  out.(0ul) <- o0;
  out.(1ul) <- o1;
  out.(2ul) <- o2;
  out.(3ul) <- o3;
  carry


val mul1: out:u256 -> f1:u256 -> f2:uint64
  -> Stack uint64
    (requires fun h -> live h out /\ live h f1)
    (ensures  fun h0 c h1 ->
      modifies (loc out) h0 h1 /\
      as_nat h1 out + v c * pow2 256 == as_nat h0 f1 * v f2)
[@ CInline]
let mul1 out f1 u2 =
  let f20 = f1.(size 0) in
  let f21 = f1.(size 1) in
  let f22 = f1.(size 2) in
  let f23 = f1.(size 3) in
  let (carry, out4) = mul1 (f20, f21, f22, f23) u2 in
  let (o0, o1, o2, o3) = out4 in
  out.(size 0) <- o0;
  out.(size 1) <- o1;
  out.(size 2) <- o2;
  out.(size 3) <- o3;
  carry

val mul1_add: out:u256 -> f1:u256 -> f2:uint64 -> f3:u256
  -> Stack uint64
    (requires fun h ->
      live h out /\ live h f1 /\ live h f3 /\
      as_nat h f3 + as_nat h f1 * v f2 < pow2 320)
    (ensures  fun h0 c h1 ->
      modifies (loc out) h0 h1 /\
      as_nat h1 out + v c * pow2 256 == as_nat h0 f3 + as_nat h0 f1 * v f2)
[@ CInline]
let mul1_add out f1 u2 f3 =
  let f10 = f1.(0ul) in
  let f11 = f1.(1ul) in
  let f12 = f1.(2ul) in
  let f13 = f1.(3ul) in

  let f30 = f3.(0ul) in
  let f31 = f3.(1ul) in
  let f32 = f3.(2ul) in
  let f33 = f3.(3ul) in

  let (carry, out4) = mul1_add (f10, f11, f12, f13) u2 (f30, f31, f32, f33) in
  let (o0, o1, o2, o3) = out4 in
  out.(size 0) <- o0;
  out.(size 1) <- o1;
  out.(size 2) <- o2;
  out.(size 3) <- o3;
  carry

val mul: out:u512 -> f1:u256 -> r:u256
  -> Stack unit
    (requires fun h -> live h out /\ live h f1 /\ live h r)
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
      wide_as_nat h1 out == as_nat h0 f1 * as_nat h0 r)
[@ CInline]
let mul out f1 r =
  let f10 = f1.(0ul) in
  let f11 = f1.(1ul) in
  let f12 = f1.(2ul) in
  let f13 = f1.(3ul) in

  let r0 = r.(0ul) in
  let r1 = r.(1ul) in
  let r2 = r.(2ul) in
  let r3 = r.(3ul) in
  let out8 = mul4 (f10, f11, f12, f13) (r0, r1, r2, r3) in
  let (o0, o1, o2, o3, o4, o5, o6, o7) = out8 in
  out.(0ul) <- o0;
  out.(1ul) <- o1;
  out.(2ul) <- o2;
  out.(3ul) <- o3;
  out.(4ul) <- o4;
  out.(5ul) <- o5;
  out.(6ul) <- o6;
  out.(7ul) <- o7

val mul2: out:u1024 -> f1:u512 -> f2:u512
  -> Stack unit
    (requires fun h ->
      live h out /\ live h f1 /\ live h f2 /\
      disjoint out f1 /\ disjoint out f2)
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
     (let out1 = gsub out 0ul 8ul in
      let out2 = gsub out 8ul 8ul in
      let f10 = gsub f1 0ul 4ul in
      let f20 = gsub f2 0ul 4ul in
      let f11 = gsub f1 4ul 4ul in
      let f21 = gsub f2 4ul 4ul in
      wide_as_nat h1 out1 == as_nat h0 f10 * as_nat h0 f20 /\
      wide_as_nat h1 out2 == as_nat h0 f11 * as_nat h0 f21))
[@ CInline]
let mul2 out f1 f2 =
  let h0 = ST.get () in
  let out1 = B.sub out 0ul 8ul in
  let out2 = B.sub out 8ul 8ul in
  let f10 = B.sub f1 0ul 4ul in
  let f20 = B.sub f2 0ul 4ul in
  let f11 = B.sub f1 4ul 4ul in
  let f21 = B.sub f2 4ul 4ul in
  mul out1 f10 f20;
  mul out2 f11 f21

val sqr: out:u512 -> f:u256
  -> Stack unit
    (requires fun h -> live h out /\ live h f)
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
      wide_as_nat h1 out == as_nat h0 f * as_nat h0 f)
[@ CInline]
let sqr out f = mul out f f

val sqr2: out:u1024 -> f:u512
  -> Stack unit
    (requires fun h ->
      live h out /\ live h f /\ disjoint out f)
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
     (let out1 = gsub out 0ul 8ul in
      let out2 = gsub out 8ul 8ul in
      let f0 = gsub f 0ul 4ul in
      let f1 = gsub f 4ul 4ul in
      wide_as_nat h1 out1 == as_nat h0 f0 * as_nat h0 f0 /\
      wide_as_nat h1 out2 == as_nat h0 f1 * as_nat h0 f1))
[@ CInline]
let sqr2 out f =
  let out1 = B.sub out 0ul 8ul in
  let out2 = B.sub out 8ul 8ul in
  let f0 = B.sub f 0ul 4ul in
  let f1 = B.sub f 4ul 4ul in
  sqr out1 f0;
  sqr out2 f1

[@ CInline]
let fadd out f1 f2 =
  let f10 = f1.(0ul) in
  let f11 = f1.(1ul) in
  let f12 = f1.(2ul) in
  let f13 = f1.(3ul) in

  let f20 = f2.(0ul) in
  let f21 = f2.(1ul) in
  let f22 = f2.(2ul) in
  let f23 = f2.(3ul) in

  let (o0, o1, o2, o3) =
    fadd4 (f10, f11, f12, f13) (f20, f21, f22, f23) in
  out.(0ul) <- o0;
  out.(1ul) <- o1;
  out.(2ul) <- o2;
  out.(3ul) <- o3

[@ CInline]
let fsub out f1 f2 =
  let f10 = f1.(0ul) in
  let f11 = f1.(1ul) in
  let f12 = f1.(2ul) in
  let f13 = f1.(3ul) in

  let f20 = f2.(0ul) in
  let f21 = f2.(1ul) in
  let f22 = f2.(2ul) in
  let f23 = f2.(3ul) in

  let (o0, o1, o2, o3) =
    fsub4 (f10, f11, f12, f13) (f20, f21, f22, f23) in
  out.(0ul) <- o0;
  out.(1ul) <- o1;
  out.(2ul) <- o2;
  out.(3ul) <- o3

val carry_wide:
  out:u256 -> inp:u512
  -> Stack unit
    (requires fun h -> live h out /\ live h inp)
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
      fevalh h1 out == feval_wideh h0 inp)
[@ CInline]
let carry_wide out i =
  let i0 = i.(0ul) in
  let i1 = i.(1ul) in
  let i2 = i.(2ul) in
  let i3 = i.(3ul) in
  let i4 = i.(4ul) in
  let i5 = i.(5ul) in
  let i6 = i.(6ul) in
  let i7 = i.(7ul) in

  let (o0, o1, o2, o3) =
    carry_wide (i0, i1, i2, i3, i4, i5, i6, i7) in
  out.(0ul) <- o0;
  out.(1ul) <- o1;
  out.(2ul) <- o2;
  out.(3ul) <- o3

[@ CInline]
let fmul out f1 f2 =
  let f10 = f1.(0ul) in
  let f11 = f1.(1ul) in
  let f12 = f1.(2ul) in
  let f13 = f1.(3ul) in

  let f20 = f2.(0ul) in
  let f21 = f2.(1ul) in
  let f22 = f2.(2ul) in
  let f23 = f2.(3ul) in

  let (o0, o1, o2, o3) =
    fmul4 (f10, f11, f12, f13) (f20, f21, f22, f23) in
  out.(0ul) <- o0;
  out.(1ul) <- o1;
  out.(2ul) <- o2;
  out.(3ul) <- o3

[@ CInline]
let fmul2 out f1 f2 =
  push_frame();
  let tmp = create 16ul (u64 0) in
  mul2 tmp f1 f2;
  let out1 = B.sub out 0ul 4ul in
  let out2 = B.sub out 4ul 4ul in
  let tmp1 = B.sub tmp 0ul 8ul in
  let tmp2 = B.sub tmp 8ul 8ul in
  carry_wide out1 tmp1;
  carry_wide out2 tmp2;
  admit();
  pop_frame()

[@ CInline]
let fmul1 out f1 f2 =
  let f10 = f1.(0ul) in
  let f11 = f1.(1ul) in
  let f12 = f1.(2ul) in
  let f13 = f1.(3ul) in

  let (o0, o1, o2, o3) = fmul14 (f10, f11, f12, f13) f2 in
  out.(0ul) <- o0;
  out.(1ul) <- o1;
  out.(2ul) <- o2;
  out.(3ul) <- o3

[@ CInline]
let fsqr out f1 =
  let f10 = f1.(0ul) in
  let f11 = f1.(1ul) in
  let f12 = f1.(2ul) in
  let f13 = f1.(3ul) in

  let (o0, o1, o2, o3) = fsqr4 (f10, f11, f12, f13) in
  out.(0ul) <- o0;
  out.(1ul) <- o1;
  out.(2ul) <- o2;
  out.(3ul) <- o3

[@ CInline]
let fsqr2 out f =
  push_frame();
  let tmp = create 16ul (u64 0) in
  let tmp1 = B.sub tmp 0ul 8ul in
  let tmp2 = B.sub tmp 8ul 8ul in
  let out1 = B.sub out 0ul 4ul in
  let out2 = B.sub out 4ul 4ul in
  sqr2 tmp f;
  carry_wide out1 tmp1;
  carry_wide out2 tmp2;
  admit();
  pop_frame()
