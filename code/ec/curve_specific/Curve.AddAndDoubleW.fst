module Curve.AddAndDouble

open FStar.Mul
open FStar.ST
open FStar.HyperStack
open FStar.Ghost
open Hacl.SBuffer
open Math.Lib
open Math.Field
open Curve.Parameters
open Curve.Bigint
open Curve.Bignum
open Curve.Point

module U32 = FStar.UInt32
module S64 = Hacl.UInt64
module S128 = Hacl.UInt128
module HS = FStar.HyperStack

let w: u32 -> Tot int = U32.v
let vv: s128 -> GTot int = S128.v

let op_Plus_Bar = U32.add
let op_Subtraction_Bar = U32.sub

let op_Bar_Bar_Bar : s64 -> s64 -> Tot s64 = Hacl.UInt64.logor

val assign: bigint -> bigint -> ST unit (requires (fun h -> True)) (ensures (fun h0 _ h1 -> True))
let assign output input =
  upd output 0ul (index input 0ul);
  upd output 1ul (index input 1ul);
  upd output 2ul (index input 2ul);
  upd output 3ul (index input 3ul);
  upd output 4ul (index input 4ul);
  upd output 5ul (index input 5ul);
  upd output 6ul (index input 6ul);
  upd output 7ul (index input 7ul)

val assign_masked: bigint -> bigint -> s64 -> ST unit (requires (fun h -> True)) (ensures (fun h0 _ h1 -> True))
let assign_masked output input maski =
  let masko = Hacl.UInt64.lognot maski in
  let in0 = index input 0ul in
  let in1 = index input 1ul in
  let in2 = index input 2ul in
  let in3 = index input 3ul in
  let in4 = index input 4ul in
  let in5 = index input 5ul in
  let in6 = index input 6ul in
  let in7 = index input 7ul in
  let out0 = index output 0ul in
  let out1 = index output 1ul in
  let out2 = index output 2ul in
  let out3 = index output 3ul in
  let out4 = index output 4ul in
  let out5 = index output 5ul in
  let out6 = index output 6ul in
  let out7 = index output 7ul in
  upd output 0ul (Hacl.UInt64.logor (Hacl.UInt64.logand maski in0) (Hacl.UInt64.logand masko out0));
  upd output 1ul (Hacl.UInt64.logor (Hacl.UInt64.logand maski in1) (Hacl.UInt64.logand masko out1));
  upd output 2ul (Hacl.UInt64.logor (Hacl.UInt64.logand maski in2) (Hacl.UInt64.logand masko out2));
  upd output 3ul (Hacl.UInt64.logor (Hacl.UInt64.logand maski in3) (Hacl.UInt64.logand masko out3));
  upd output 4ul (Hacl.UInt64.logor (Hacl.UInt64.logand maski in4) (Hacl.UInt64.logand masko out4));
  upd output 5ul (Hacl.UInt64.logor (Hacl.UInt64.logand maski in5) (Hacl.UInt64.logand masko out5));
  upd output 6ul (Hacl.UInt64.logor (Hacl.UInt64.logand maski in6) (Hacl.UInt64.logand masko out6));
  upd output 7ul (Hacl.UInt64.logor (Hacl.UInt64.logand maski in7) (Hacl.UInt64.logand masko out7))

// Naive implementation from http://hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-3.html#doubling-dbl-2001-b
val double: point -> point -> ST unit (requires (fun h -> True)) (ensures (fun h0 _ h1 -> True))
let double two_p p =
  let tmp = create (Hacl.Cast.uint64_to_sint64 0uL) nlength in
  let tmp2 = create (Hacl.Cast.uint64_to_sint64 0uL) nlength in
  let delta = create (Hacl.Cast.uint64_to_sint64 0uL) nlength in
  let gamma = create (Hacl.Cast.uint64_to_sint64 0uL) nlength in
  let beta = create (Hacl.Cast.uint64_to_sint64 0uL) nlength in
  let alpha = create (Hacl.Cast.uint64_to_sint64 0uL) nlength in
  let ftmp = create (Hacl.Cast.uint64_to_sint64 0uL) nlength in
  let ftmp2 = create (Hacl.Cast.uint64_to_sint64 0uL) nlength in
  let small1 = create (Hacl.Cast.uint64_to_sint64 0uL) nlength in
  let small2 = create (Hacl.Cast.uint64_to_sint64 0uL) nlength in

  let x_in = get_x p in
  let y_in = get_y p in
  let z_in = get_z p in
  let x_out = get_x two_p in
  let y_out = get_y two_p in
  let z_out = get_z two_p in

  fsquare delta z_in;
  fsquare gamma y_in;
  fmul beta x_in gamma;

  assign ftmp delta;
  assign ftmp2 delta;
  fdifference ftmp x_in;
  fsum ftmp2 x_in;
  fmul tmp ftmp ftmp2;
  fscalar alpha tmp (Hacl.UInt64.of_string "3");
  fsquare ftmp alpha;
  fscalar x_out beta (Hacl.UInt64.of_string "8");
  fdifference x_out ftmp;

  assign z_out gamma;
  fsum z_out delta;
  assign ftmp y_in;
  fsum ftmp z_in;
  fsquare ftmp2 ftmp;
  fdifference z_out ftmp2;

  fsquare ftmp gamma;
  fscalar y_out ftmp (Hacl.UInt64.of_string "8");

  assign ftmp x_out;
  fscalar ftmp2 beta (Hacl.UInt64.of_string "4");
  fdifference ftmp ftmp2;
  fmul ftmp2 ftmp alpha;
  fdifference y_out ftmp2

val is_zero: bigint -> ST s64 (requires (fun h -> True)) (ensures (fun h0 _ h1 -> True))
let is_zero z =
  let z0 = index z 0ul in 
  let z1 = index z 1ul in
  let z2 = index z 2ul in 
  let z3 = index z 3ul in
  let z4 = index z 4ul in 
  let z5 = index z 5ul in
  let z6 = index z 6ul in 
    let z7 = index z 7ul in
  let mask = z0 ||| z1 ||| z2 ||| z3 ||| z4 ||| z5 ||| z6 ||| z7 in
  Hacl.UInt64.eq_mask mask (Hacl.Cast.uint64_to_sint64 0uL)

val add: point -> point -> point -> ST unit (requires (fun h -> True)) (ensures (fun h0 _ h1 -> True))
let add p_plus_q p q =
  let ftmp = create (Hacl.Cast.uint64_to_sint64 0uL) nlength in 
  let ftmp2 = create (Hacl.Cast.uint64_to_sint64 0uL) nlength in 
  let ftmp3 = create (Hacl.Cast.uint64_to_sint64 0uL) nlength in 
  let x_out = create (Hacl.Cast.uint64_to_sint64 0uL) nlength in 
  let y_out = create (Hacl.Cast.uint64_to_sint64 0uL) nlength in 
  let z_out = create (Hacl.Cast.uint64_to_sint64 0uL) nlength in 
  let tmp = create (Hacl.Cast.uint64_to_sint64 0uL) nlength in
  let tmp2 = create (Hacl.Cast.uint64_to_sint64 0uL) nlength in
  let z1z1 = create (Hacl.Cast.uint64_to_sint64 0uL) nlength in
  let z2z2 = create (Hacl.Cast.uint64_to_sint64 0uL) nlength in
  let u1 = create (Hacl.Cast.uint64_to_sint64 0uL) nlength in
  let u2 = create (Hacl.Cast.uint64_to_sint64 0uL) nlength in
  let s1 = create (Hacl.Cast.uint64_to_sint64 0uL) nlength in 
  let s2 = create (Hacl.Cast.uint64_to_sint64 0uL) nlength in 
  let h = create (Hacl.Cast.uint64_to_sint64 0uL) nlength in 
  let i = create (Hacl.Cast.uint64_to_sint64 0uL) nlength in 
  let j = create (Hacl.Cast.uint64_to_sint64 0uL) nlength in 
  let r = create (Hacl.Cast.uint64_to_sint64 0uL) nlength in 
  let v = create (Hacl.Cast.uint64_to_sint64 0uL) nlength in 

  let x3 = get_x p_plus_q in
  let y3 = get_y p_plus_q in
  let z3 = get_z p_plus_q in
  
  let x1 = get_x p in
  let y1 = get_y p in
  let z1 = get_z p in

  let x2 = get_x q in
  let y2 = get_y q in
  let z2 = get_z q in

  let z1_is_zero = is_zero z1 in
  let z2_is_zero = is_zero z2 in

  fsquare z1z1 z1; // z1z1 = z1²
  fsquare z2z2 z2; // z2z2 = z2²
  fmul u1 x1 z2z2; // u1 = x1 * z2z2
  fmul u2 x2 z1z1; // u2 = x2 * z1z1
  fmul ftmp z2 z2z2; 
  fmul ftmp2 z1 z1z1;
  fmul s1 y1 ftmp; // s1 = y1 * z2 * z2z2
  fmul s2 y2 ftmp2; // s2 = y2 * z1 * z1z1
  assign h u1; 
  fdifference h u2; // h = u2 - u1
  fscalar ftmp h (Hacl.UInt64.of_string "2"); 
  fsquare i ftmp; // i = (2*h)²
  fmul j h i; // j = h * i
  assign ftmp s1; 
  fdifference ftmp s2;
  fscalar r ftmp (Hacl.UInt64.of_string "2"); // r = 2 * (s2 - s1)
  fmul v u1 i; // v = u1 * i
  fscalar x3 v (Hacl.UInt64.of_string "2"); 
  fsum x3 j;
  fsquare ftmp2 r;
  fdifference x3 ftmp2; // x3 = r² - j - 2*v
  fscalar ftmp s1 (Hacl.UInt64.of_string "2");
  fmul y3 ftmp j;
  assign ftmp x3;
  fdifference ftmp v;
  fmul ftmp2 r ftmp;
  fdifference y3 ftmp2; // y3 = (r * (v-x3)) - (j * 2 * s1)
  fsum z1z1 z2z2;
  assign ftmp z1;
  fsum ftmp z2;
  fsquare ftmp2 ftmp;
  fdifference z1z1 ftmp2;
  fmul z3 z1z1 h; // ( z3 = (z1+z2)² - z1z1 - z2z2 ) * h

  assign_masked x3 x2 z1_is_zero;
  assign_masked x3 x1 z2_is_zero;
  assign_masked y3 y2 z1_is_zero;
  assign_masked y3 y1 z2_is_zero;
  assign_masked z3 z2 z1_is_zero;
  assign_masked z3 z1 z2_is_zero

let double_and_add two_p two_p_plus_q p p_plus_q q =
  double two_p p;
  add two_p_plus_q p p_plus_q

let double_and_add' = double_and_add
