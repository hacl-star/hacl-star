module Spec.P256.Basic

open FStar.Mul
open Lib.Sequence
open Lib.IntTypes

open Spec.P256.Definitions

(* open Hacl.Spec.Curve25519.Field64.Lemmas *)

(*This code was written by Polubelova M *)
#reset-options "--z3refresh --z3rlimit 200"

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
    (ensures fun (r, c) -> v c <= 2 /\
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

inline_for_extraction noextract
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

#set-options "--z3rlimit 150"
val add1:
    f:felem4
  -> cin:uint64
  -> Pure (uint64 & felem4)
    (requires True)
    (ensures fun (c, r) ->
      as_nat4 r + v c * pow2 256 == as_nat4 f + v cin)
let add1 f cin =
  let (f0, f1, f2, f3) = f in
  let o0, c0 = add0carry f0 cin in
  let o1, c1 = add0carry f1 c0 in
  let o2, c2 = add0carry f2 c1 in
  let o3, c3 = add0carry f3 c2 in
  let out = (o0, o1, o2, o3) in
  admit();//lemma_mul_assos_5 (v c3) (pow2 64) (pow2 64) (pow2 64) (pow2 64);
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
  c3, out

#set-options "--z3rlimit 150"
noextract inline_for_extraction
val mul1:
    f:felem4
  -> u:uint64
  -> Pure (uint64 & felem4)
    (requires True)
    (ensures fun (c, r) ->
      as_nat4 r + v c * pow2 256 == as_nat4 f * v u)
let mul1 (f0, f1, f2, f3) u =
  let l0, h0 = mul64 f0 u in
  let l1, h1 = mul64 f1 u in
  let l2, h2 = mul64 f2 u in
  let l3, h3 = mul64 f3 u in
  let o0 = l0 in
  let o1, c0 = addcarry l1 h0 (u64 0) in
  let o2, c1 = addcarry l2 h1 c0 in
  let o3, c2 = addcarry l3 h2 c1 in
  let out = (o0, o1, o2, o3) in

  assert (as_nat4 out  ==
    v f0 * v u - v h0 * pow2 64 +
    (v f1 * v u - v h1 * pow2 64 + v h0 - v c0 * pow2 64) * pow2 64 +
    (v f2 * v u - v h2 * pow2 64 + v h1 + v c0 - v c1 * pow2 64) * pow2 64 * pow2 64 +
    (v f3 * v u - v h3 * pow2 64 + v h2 + v c1 - v c2 * pow2 64) * pow2 64 * pow2 64 * pow2 64);

  assert (as_nat4 out ==
    v f0 * v u +
    v f1 * v u * pow2 64  +
    v f2 * v u * pow2 64 * pow2 64 +
    v f3 * v u * pow2 64 * pow2 64 * pow2 64 -
    v h3 * pow2 64 * pow2 64 * pow2 64 * pow2 64 -
    v c2 * pow2 64 * pow2 64 * pow2 64 * pow2 64);
  admit();//lemma_mul1_simplify out (f0, f1, f2, f3) u h3 c2;
  assert (as_nat4 out + (v h3 + v c2) * pow2 256 == as_nat4 (f0, f1, f2, f3) * v u);

  //lemma_mul1 (f0, f1, f2, f3) u;
  //lemma_as_nat4 out;
  //lemma_mul1_no_carry (as_nat4 out) (as_nat4 (f0, f1, f2, f3) * v u) (v h3 + v c2);
  let c3 = h3 +! c2 in
  c3, (o0, o1, o2, o3)

noextract inline_for_extraction
val mul1_add:
    f1:felem4
  -> u2:uint64
  -> f3:felem4
  -> Pure (uint64 & felem4)
    (requires True)
    (ensures fun (c, r) ->
      as_nat4 r + v c * pow2 256 == as_nat4 f3 + as_nat4 f1 * v u2)
let mul1_add f1 u2 f3 =
  admit();//lemma_mul1_add_pre f1 u2 f3;
  assert (as_nat4 f3 + as_nat4 f1 * v u2 < pow2 320);
  let c, out0 = mul1 f1 u2 in
  let (o0, o1, o2, o3) = out0 in
  let (f30, f31, f32, f33) = f3 in
  let o0', c0 = addcarry f30 o0 (u64 0) in
  let o1', c1 = addcarry f31 o1 c0 in
  let o2', c2 = addcarry f32 o2 c1 in
  let o3', c3 = addcarry f33 o3 c2 in
  let out = (o0', o1', o2', o3') in
  //lemma_mul1_add out f3 out0 c0 c1 c2 c3;
  assert (as_nat4 out == as_nat4 f3 + as_nat4 out0 -
   v c3 * pow2 64 * pow2 64 * pow2 64 * pow2 64);
  //lemma_mul_assos_5 (v c3) (pow2 64) (pow2 64) (pow2 64) (pow2 64);
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
  assert (as_nat4 out == as_nat4 f3 + as_nat4 out0 - v c3 * pow2 256);
  assert (as_nat4 out == as_nat4 f3 + as_nat4 f1 * v u2 - v c * pow2 256 - v c3 * pow2 256);
  assert (as_nat4 out + v c * pow2 256 + v c3 * pow2 256 == as_nat4 f3 + as_nat4 f1 * v u2);
  FStar.Math.Lemmas.distributivity_add_left (v c) (v c3) (pow2 256);
  assert (as_nat4 out + (v c + v c3) * pow2 256 == as_nat4 f3 + as_nat4 f1 * v u2);
  //lemma_as_nat4 out;
  //lemma_as_nat4 f1;
  //lemma_as_nat4 f3;
  //lemma_mul1_add_no_carry (as_nat4 out) (as_nat4 f3) (as_nat4 f1) (v u2) (v c + v c3);
  let c4 = c +! c3 in
  c4, out

noextract inline_for_extraction
val add4:
    f1:felem4
  -> f2:felem4
  -> Pure (uint64 & felem4)
    (requires True)
    (ensures fun (c, r) -> v c <= 1 /\
      as_nat4 r + v c * pow2 256 == as_nat4 f1 + as_nat4 f2)
let add4 (f10, f11, f12, f13) (f20, f21, f22, f23) =
  let o0, c0 = addcarry f10 f20 (u64 0) in
  let o1, c1 = addcarry f11 f21 c0 in
  let o2, c2 = addcarry f12 f22 c1 in
  let o3, c3 = addcarry f13 f23 c2 in
  let out = (o0, o1, o2, o3) in
  //lemma_mul_assos_5 (v c3) (pow2 64) (pow2 64) (pow2 64) (pow2 64);
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
  c3, (o0, o1, o2, o3)


inline_for_extraction noextract
val sub4:
    f1:felem4
  -> f2:felem4
  -> Pure (uint64 & felem4)
    (requires True)
    (ensures fun (c, r) -> v c <= 1 /\
      as_nat4 r - v c * pow2 256 == as_nat4 f1 - as_nat4 f2)
let sub4 (f10, f11, f12, f13) (f20, f21, f22, f23) =
  let o0, c0 = subborrow f10 f20 (u64 0) in
  let o1, c1 = subborrow f11 f21 c0 in
  let o2, c2 = subborrow f12 f22 c1 in
  let o3, c3 = subborrow f13 f23 c2 in
  //lemma_mul_assos_5 (v c3) (pow2 64) (pow2 64) (pow2 64) (pow2 64);
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
  c3, (o0, o1, o2, o3)

noextract inline_for_extraction
val mul4:
    f:felem4
  -> r:felem4
  -> out:felem8{wide_as_nat4 out == as_nat4 f * as_nat4 r}
let mul4 (f0, f1, f2, f3) (r0, r1, r2, r3) =
  let c0, (o00, o01, o02, o03) = mul1 (r0, r1, r2, r3) f0 in
  let c1, (o11, o12, o13, o14) = mul1_add (r0, r1, r2, r3) f1 (o01, o02, o03, c0) in
  let c2, (o22, o23, o24, o25) = mul1_add (r0, r1, r2, r3) f2 (o12, o13, o14, c1) in
  let c3, (o33, o34, o35, o36)  = mul1_add (r0, r1, r2, r3) f3 (o23, o24, o25, c2) in admit();
  (*let out = (o00, o11, o22, o33, o34, o35, o36, o37) in *)
  //lemma_mul4 (as_nat4 (r0, r1, r2, r3)) (v f0) (v f1) (v f2) (v f3) (v c0) (v c1) (v c2) (v c3)
  //(v o01) (v o02) (v o03) (v o12) (v o13) (v o14) (v o23) (v o24) (v o25) (v o34) (v o35) (v o36);
  //lemma_mul4_expand (f0, f1, f2, f3) (r0, r1, r2, r3); 
  (o00, o11, o22, o33, o34, o35, o36, c3)
