module Hacl.Spec.Curve25519.Field64.Core

open Lib.Sequence
open Lib.IntTypes

#reset-options "--z3rlimit 50  --using_facts_from '* -FStar.Seq'"

let felem4 = (uint64 * uint64 * uint64 * uint64)
let felem_wide4 = (uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64)

open FStar.Mul

let prime:pos =
  assert_norm (pow2 255 - 19 > 0);
  pow2 255 - 19

noextract
val as_nat4: f:felem4 -> GTot nat
let as_nat4 f =
  let (s0, s1, s2, s3) = f in
  v s0 + v s1 * pow2 64 + v s2 * pow2 64 * pow2 64 +
  v s3 * pow2 64 * pow2 64 * pow2 64

noextract
val wide_as_nat4: f:felem_wide4 -> GTot nat
let wide_as_nat4 f =
  let (s0, s1, s2, s3, s4, s5, s6, s7) = f in
  v s0 + v s1 * pow2 64 + v s2 * pow2 64 * pow2 64 +
  v s3 * pow2 64 * pow2 64 * pow2 64 +
  v s4 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
  v s5 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
  v s6 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
  v s7 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64

let felem = x:nat{x < prime}
let feval (f:felem4) : GTot felem = (as_nat4 f) % prime
let feval_wide (f:felem_wide4) : GTot felem = (wide_as_nat4 f) % prime

val fadd: felem -> felem -> felem
let fadd f1 f2 = (f1 + f2) % prime

val fsub: felem -> felem -> felem
let fsub f1 f2 = (f1 - f2) % prime

val fmul: felem -> felem -> felem
let fmul f1 f2 = (f1 * f2) % prime

inline_for_extraction noextract
val lt_u64:a:uint64 -> b:uint64 -> Tot bool
let lt_u64 a b =
  let open Lib.RawIntTypes in
  FStar.UInt64.(u64_to_UInt64 a <^ u64_to_UInt64 b)

inline_for_extraction noextract
val le_u64:a:uint64 -> b:uint64 -> Tot bool
let le_u64 a b =
  let open Lib.RawIntTypes in
  FStar.UInt64.(u64_to_UInt64 a <=^ u64_to_UInt64 b)

inline_for_extraction noextract
val eq_u64:a:uint64 -> b:uint64 -> Tot bool
let eq_u64 a b =
  let open Lib.RawIntTypes in
  FStar.UInt64.(u64_to_UInt64 a =^ u64_to_UInt64 b)

val addcarry:
    x:uint64
  -> y:uint64
  -> cin:uint64
  -> Pure (uint64 & uint64)
    (requires True)
    (ensures fun (r, c) ->
      v r + v c * pow2 64 == v x + v y + v cin)
[@CInline]
let addcarry x y cin =
  let res1 = x +. cin in
  let c = if lt_u64 res1 cin then u64 1 else u64 0 in
  let res = res1 +. y in
  let c = if lt_u64 res res1 then c +. u64 1 else c in
  res, c

val subborrow:
    x:uint64
  -> y:uint64
  -> cin:uint64{v cin <= 1}
  -> Pure (uint64 & uint64)
    (requires True)
    (ensures fun (r, c) ->
      v r - v c * pow2 64 == v x - v y - v cin)
[@CInline]
let subborrow x y cin =
  let res = x -. y -. cin in
  let c =
    if eq_u64 cin (u64 1) then
      (if le_u64 x y then u64 1 else u64 0)
    else
      (if lt_u64 x y then u64 1 else u64 0) in
  res, c

val mul64:
    x:uint64
  -> y:uint64
  -> Pure (uint64 & uint64)
    (requires True)
    (ensures fun (l0, l1) ->
      v l0 + v l1 * pow2 64 = v x * v y)
[@CInline]
let mul64 x y =
  let res = mul64_wide x y in
  (to_u64 res, to_u64 (res >>. 64ul))

val add0carry:
    x:uint64
  -> y:uint64
  -> Pure (uint64 & uint64)
    (requires True)
    (ensures fun (r, c) ->
      v r + v c * pow2 64 == v x + v y)
[@CInline]
let add0carry x y =
  let res = x +. y in
  let c = if lt_u64 res x then u64 1 else u64 0 in
  res, c

val add1:
    f:felem4
  -> cin:uint64
  -> uint64 & felem4
let add1 f cin =
  let (f0, f1, f2, f3) = f in
  let o0, c0 = add0carry f0 cin in
  let o1, c1 = add0carry f1 c0 in
  let o2, c2 = add0carry f2 c1 in
  let o3, c3 = add0carry f3 c2 in
  let out = (o0, o1, o2, o3) in
  c3, out

val sub1:
    f:felem4
  -> cin:uint64
  -> uint64 & felem4
let sub1 f cin =
  let (f0, f1, f2, f3) = f in
  let o0, c0 = subborrow f0 cin (u64 0) in
  let o1, c1 = subborrow f1 (u64 0) c0 in
  let o2, c2 = subborrow f2 (u64 0) c1 in
  let o3, c3 = subborrow f3 (u64 0) c2 in
  let out = (o0, o1, o2, o3) in
  c3, out

val mul1:
    f:felem4
  -> u:uint64
  -> uint64 & felem4
let mul1 f u =
  let (f0, f1, f2, f3) = f in
  let l0, h0 = mul64 f0 u in
  let l1, h1 = mul64 f1 u in
  let l2, h2 = mul64 f2 u in
  let l3, h3 = mul64 f3 u in
  let o0 = l0 in
  let o1, c0 = addcarry l1 h0 (u64 0) in
  let o2, c1 = addcarry l2 h1 c0 in
  let o3, c2 = addcarry l3 h2 c1 in
  let c3 = h3 +. c2 in
  let out = (o0, o1, o2, o3) in
  c3, out

val mul1_add:
    f1:felem4
  -> u2:uint64
  -> f3:felem4
  -> uint64 & felem4
let mul1_add f1 u2 f3 =
  let c, out0 = mul1 f1 u2 in
  let (o0, o1, o2, o3) = out0 in
  let (f30, f31, f32, f33) = f3 in
  let o0, c0 = addcarry f30 o0 (u64 0) in
  let o1, c1 = addcarry f31 o1 c0 in
  let o2, c2 = addcarry f32 o2 c1 in
  let o3, c3 = addcarry f33 o3 c2 in
  let c4 = c +. c3 in
  let out = (o0, o1, o2, o3) in
  c4, out

val carry_pass:
    f:felem4
  -> cin:uint64
  -> out:felem4
let carry_pass f cin =
  let carry, out0 = add1 f (cin *. u64 38) in
  let (o0, o1, o2, o3) = out0 in
  let o0' = o0 +. carry *. u64 38 in
  (o0', o1, o2, o3)

val carry_wide:
    f:felem_wide4
  -> out:felem4
let carry_wide f =
  let (f0, f1, f2, f3, f4, f5, f6, f7) = f in
  let c0, out0 = mul1_add (f4, f5, f6, f7) (u64 38) (f0, f1, f2, f3) in
  carry_pass out0 c0

val add4:
    f1:felem4
  -> f2:felem4
  -> uint64 & felem4
let add4 f1 f2 =
  let (f10, f11, f12, f13) = f1 in
  let (f20, f21, f22, f23) = f2 in
  let o0, c0 = addcarry f10 f20 (u64 0) in
  let o1, c1 = addcarry f11 f21 c0 in
  let o2, c2 = addcarry f12 f22 c1 in
  let o3, c3 = addcarry f13 f23 c2 in
  let out = (o0, o1, o2, o3) in
  c3, out

val fadd4:
    f1:felem4
  -> f2:felem4
  -> felem4
let fadd4 f1 f2 =
  let c0, out0 = add4 f1 f2 in
  carry_pass out0 c0

val sub4:
    f1:felem4
  -> f2:felem4
  -> uint64 & felem4
let sub4 f1 f2 =
  let (f10, f11, f12, f13) = f1 in
  let (f20, f21, f22, f23) = f2 in
  let o0, c0 = subborrow f10 f20 (u64 0) in
  let o1, c1 = subborrow f11 f21 c0 in
  let o2, c2 = subborrow f12 f22 c1 in
  let o3, c3 = subborrow f13 f23 c2 in
  let out = (o0, o1, o2, o3) in
  c3, out

val fsub4:
    f1:felem4
  -> f2:felem4
  -> felem4
let fsub4 f1 f2 =
  let c0, out0 = sub4 f1 f2 in
  let c1, out1 = sub1 out0 (c0 *. u64 38) in
  let (o0, o1, o2, o3) = out1 in
  let o0' = o0 -. c1 *. u64 38 in
  (o0', o1, o2, o3)

val mul4:
    f1:felem4
  -> r:felem4
  -> out:felem_wide4
let mul4 f1 r =
  let (f0, f1, f2, f3) = f1 in
  let c0, out0 = mul1 r f0 in
  let (o0, o1, o2, o3) = out0 in
  let c1, out1 = mul1_add r f1 (o1, o2, o3, c0) in
  let (o1, o2, o3, o4) = out1 in
  let c2, out2 = mul1_add r f2 (o2, o3, o4, c1) in
  let (o2, o3, o4, o5) = out2 in
  let c3, out3 = mul1_add r f3 (o3, o4, o5, c2) in
  let (o3, o4, o5, o6) = out3 in
  let o7 = c3 in
  (o0, o1, o2, o3, o4, o5, o6, o7)

val fmul4: f1:felem4 -> r:felem4 -> out:felem4
let fmul4 f1 r =
  let tmp = mul4 f1 r in
  carry_wide tmp

val fmul14: f1:felem4 -> f2:uint64 -> out:felem4
let fmul14 f1 f2 =
  let c0, out0 = mul1 f1 f2 in
  carry_pass out0 c0

val sqr4: f:felem4 -> out:felem_wide4
let sqr4 f = mul4 f f

val fsqr4: f:felem4 -> out:felem4
let fsqr4 f =
  let tmp = sqr4 f in
  carry_wide tmp
