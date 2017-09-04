(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi Parameters --admit_fsi Modulo --admit_fsi Bignum --admit_fsi ConcretePoint --verify_module DoubleAndAdd --lax;
    variables:MATH=../math_interfaces BIGNUM=../bignum_proof;
    other-files:FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst seq.fsi FStar.Seq.Base.fst FStar.Seq.Properties.fst FStar.Seq.fst FStar.Array.fst FStar.Ghost.fst $BIGNUM/axiomatic.fst $BIGNUM/intlib.fst $BIGNUM/lemmas.fst $BIGNUM/parameters.fsti $BIGNUM/uint.fst $BIGNUM/bigint.fst $BIGNUM/eval.fst $MATH/definitions.fst $MATH/field.fst $BIGNUM/modulo.fsti $BIGNUM/bignum.fsti $MATH/curve.fst concrete_point.fst;
  --*)

module DoubleAndAdd

open Parameters
open Bigint
open ConcretePoint
open Bignum
open UInt

let op_Bar_Bar_Bar x y = log_or_limb x y

val assign: bigint -> bigint -> ST unit (requires (fun h -> True)) (ensures (fun h0 _ h1 -> True))
let assign output input =
  upd_limb output 0 (index_limb input 0);
  upd_limb output 1 (index_limb input 1);
  upd_limb output 2 (index_limb input 2);
  upd_limb output 3 (index_limb input 3);
  upd_limb output 4 (index_limb input 4);
  upd_limb output 5 (index_limb input 5);
  upd_limb output 6 (index_limb input 6);
  upd_limb output 7 (index_limb input 7)

val assign_masked: bigint -> bigint -> limb -> ST unit (requires (fun h -> True)) (ensures (fun h0 _ h1 -> True))
let assign_masked output input maski =
  let masko = log_not_limb maski in
  let in0 = index_limb input 0 in
  let in1 = index_limb input 1 in
  let in2 = index_limb input 2 in
  let in3 = index_limb input 3 in
  let in4 = index_limb input 4 in
  let in5 = index_limb input 5 in
  let in6 = index_limb input 6 in
  let in7 = index_limb input 7 in
  let out0 = index_limb output 0 in
  let out1 = index_limb output 1 in
  let out2 = index_limb output 2 in
  let out3 = index_limb output 3 in
  let out4 = index_limb output 4 in
  let out5 = index_limb output 5 in
  let out6 = index_limb output 6 in
  let out7 = index_limb output 7 in
  upd_limb output 0 (log_or_limb (log_and_limb maski in0) (log_and_limb masko out0));
  upd_limb output 1 (log_or_limb (log_and_limb maski in1) (log_and_limb masko out1));
  upd_limb output 2 (log_or_limb (log_and_limb maski in2) (log_and_limb masko out2));
  upd_limb output 3 (log_or_limb (log_and_limb maski in3) (log_and_limb masko out3));
  upd_limb output 4 (log_or_limb (log_and_limb maski in4) (log_and_limb masko out4));
  upd_limb output 5 (log_or_limb (log_and_limb maski in5) (log_and_limb masko out5));
  upd_limb output 6 (log_or_limb (log_and_limb maski in6) (log_and_limb masko out6));
  upd_limb output 7 (log_or_limb (log_and_limb maski in7) (log_and_limb masko out7))

// Naive implementation from http://hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-3.html#doubling-dbl-2001-b
val double: point -> point -> ST unit (requires (fun h -> True)) (ensures (fun h0 _ h1 -> True))
let double two_p p =
  let tmp = create_limb norm_length in
  let tmp2 = create_limb norm_length in
  let delta = create_limb norm_length in
  let gamma = create_limb norm_length in
  let beta = create_limb norm_length in
  let alpha = create_limb norm_length in
  let ftmp = create_limb norm_length in
  let ftmp2 = create_limb norm_length in
  let small1 = create_limb norm_length in
  let small2 = create_limb norm_length in

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
  fscalar alpha tmp #platform_size (to_limb "3");
  fsquare ftmp alpha;
  fscalar x_out beta #platform_size (to_limb "8");
  fdifference x_out ftmp;

  assign z_out gamma;
  fsum z_out delta;
  assign ftmp y_in;
  fsum ftmp z_in;
  fsquare ftmp2 ftmp;
  fdifference z_out ftmp2;

  fsquare ftmp gamma;
  fscalar y_out ftmp #platform_size (to_limb "8");

  assign ftmp x_out;
  fscalar ftmp2 beta #platform_size (to_limb "4");
  fdifference ftmp ftmp2;
  fmul ftmp2 ftmp alpha;
  fdifference y_out ftmp2

val is_zero: bigint -> ST limb (requires (fun h -> True)) (ensures (fun h0 _ h1 -> True))
let is_zero z =
  let z0 = index_limb z 0 in 
  let z1 = index_limb z 1 in
  let z2 = index_limb z 2 in 
  let z3 = index_limb z 3 in
  let z4 = index_limb z 4 in 
  let z5 = index_limb z 5 in
  let z6 = index_limb z 6 in 
  let z7 = index_limb z 7 in
  let mask = z0 ||| z1 ||| z2 ||| z3 ||| z4 ||| z5 ||| z6 ||| z7 in
  eq_limb mask zero_limb

val add: point -> point -> point -> ST unit (requires (fun h -> True)) (ensures (fun h0 _ h1 -> True))
let add p_plus_q p q =
  let ftmp = create_limb norm_length in 
  let ftmp2 = create_limb norm_length in 
  let ftmp3 = create_limb norm_length in 
  let x_out = create_limb norm_length in 
  let y_out = create_limb norm_length in 
  let z_out = create_limb norm_length in 
  let tmp = create_limb norm_length in
  let tmp2 = create_limb norm_length in
  let z1z1 = create_limb norm_length in
  let z2z2 = create_limb norm_length in
  let u1 = create_limb norm_length in
  let u2 = create_limb norm_length in
  let s1 = create_limb norm_length in 
  let s2 = create_limb norm_length in 
  let h = create_limb norm_length in 
  let i = create_limb norm_length in 
  let j = create_limb norm_length in 
  let r = create_limb norm_length in 
  let v = create_limb norm_length in 

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
  fscalar ftmp h #platform_size (to_limb "2"); 
  fsquare i ftmp; // i = (2*h)²
  fmul j h i; // j = h * i
  assign ftmp s1; 
  fdifference ftmp s2;
  fscalar r ftmp #platform_size (to_limb "2"); // r = 2 * (s2 - s1)
  fmul v u1 i; // v = u1 * i
  fscalar x3 v #platform_size (to_limb "2"); 
  fsum x3 j;
  fsquare ftmp2 r;
  fdifference x3 ftmp2; // x3 = r² - j - 2*v
  fscalar ftmp s1 #platform_size (to_limb "2");
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
