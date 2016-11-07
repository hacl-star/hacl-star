module Hacl.EC.Curve25519.Bignum.Fproduct

open FStar.Mul
open FStar.ST
open FStar.HyperStack
open FStar.Ghost
open FStar.Math.Lib
open FStar.Math.Lemmas
open FStar.Buffer
open FStar.Buffer.Quantifiers

open Hacl.UInt64

open Hacl.EC.Curve25519.Parameters
open Hacl.EC.Curve25519.Bigint
open Hacl.EC.Curve25519.Utils

#reset-options "--initial_fuel 0 --max_fuel 0"

(* Module abbreviations *)
module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module U8  = FStar.UInt8
module U32 = FStar.UInt32
module H8  = Hacl.UInt8
module H32  = Hacl.UInt32
module H64  = Hacl.UInt64
module H128  = Hacl.UInt128

let u51 = x:H64.t{v x < pow2 51}

let op_Star_Bar (x:H64.t) (y:H64.t) : H128.t = H128.mul_wide x y

let isMultiplication (h0:mem) (h1:mem) (a:bigint) (b:bigint) (c:bigint_wide) : GTot Type0 =
  live h0 a /\ live h0 b /\ live h1 c
  /\ length a >= norm_length /\ length b >= norm_length /\ length c >= 2*norm_length-1
  /\ (
    let a0 = v (get h0 a 0) in let a1 = v (get h0 a 1) in let a2 = v (get h0 a 2) in
    let a3 = v (get h0 a 3) in let a4 = v (get h0 a 4) in let b0 = v (get h0 b 0) in
    let b1 = v (get h0 b 1) in let b2 = v (get h0 b 2) in let b3 = v (get h0 b 3) in
    let b4 = v (get h0 b 4) in
    let open Hacl.UInt128 in
    let c0 = v (get h1 c 0) in let c1 = v (get h1 c 1) in
    let c2 = v (get h1 c 2) in let c3 = v (get h1 c 3) in let c4 = v (get h1 c 4) in
    let c5 = v (get h1 c 5) in let c6 = v (get h1 c 6) in let c7 = v (get h1 c 7) in
    let c8 = v (get h1 c 8) in
    ( c0 = a0 * b0
      /\ c1 = a0 * b1 + a1 * b0
      /\ c2 = a0 * b2 + a1 * b1 + a2 * b0
      /\ c3 = a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0
      /\ c4 = a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0
      /\ c5 = a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1
      /\ c6 = a2 * b4 + a3 * b3 + a4 * b2
      /\ c7 = a3 * b4 + a4 * b3
      /\ c8 = a4 * b4 ) )

let isMultiplication_
  (h1:mem)
  (a0:int) (a1:int) (a2:int) (a3:int) (a4:int)
  (b0:int) (b1:int) (b2:int) (b3:int) (b4:int)
  (c:bigint_wide) : GTot Type0 =
  live h1 c /\ length c >= 2*norm_length-1
  /\ (let open Hacl.UInt128 in
      let c0 = v (get h1 c 0) in let c1 = v (get h1 c 1) in
      let c2 = v (get h1 c 2) in let c3 = v (get h1 c 3) in let c4 = v (get h1 c 4) in
      let c5 = v (get h1 c 5) in let c6 = v (get h1 c 6) in let c7 = v (get h1 c 7) in
      let c8 = v (get h1 c 8) in
      ( c0 = a0 * b0
	/\ c1 = a0 * b1 + a1 * b0
	/\ c2 = a0 * b2 + a1 * b1 + a2 * b0
	/\ c3 = a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0
	/\ c4 = a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0
	/\ c5 = a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1
	/\ c6 = a2 * b4 + a3 * b3 + a4 * b2
	/\ c7 = a3 * b4 + a4 * b3
	/\ c8 = a4 * b4 ) )

private val multiplication_0:
  c:bigint_wide{length c >= 2*norm_length-1} ->
  a0:u51 -> a1:u51 -> a2:u51 -> a3:u51 -> a4:u51 ->
  b0:u51 -> b1:u51 -> b2:u51 -> b3:u51 -> b4:u51 ->
  Stack unit
    (requires (fun h -> live h c))
    (ensures  (fun h0 _ h1 -> modifies_1 c h0 h1 /\ live h1 c
      /\ isMultiplication_ h1 (v a0) (v a1) (v a2) (v a3) (v a4) (v b0) (v b1) (v b2) (v b3) (v b4) c))
let multiplication_0 c a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 =
  (* lemma_multiplication_0 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4; *)
  let ab00 = a0 *| b0 in
  let ab01 = a0 *| b1 in
  let ab02 = a0 *| b2 in
  let ab03 = a0 *| b3 in
  let ab04 = a0 *| b4 in
  let ab10 = a1 *| b0 in
  let ab11 = a1 *| b1 in
  let ab12 = a1 *| b2 in
  let ab13 = a1 *| b3 in
  let ab14 = a1 *| b4 in
  let ab20 = a2 *| b0 in
  let ab21 = a2 *| b1 in
  let ab22 = a2 *| b2 in
  let ab23 = a2 *| b3 in
  let ab24 = a2 *| b4 in
  let ab30 = a3 *| b0 in
  let ab31 = a3 *| b1 in
  let ab32 = a3 *| b2 in
  let ab33 = a3 *| b3 in
  let ab34 = a3 *| b4 in
  let ab40 = a4 *| b0 in
  let ab41 = a4 *| b1 in
  let ab42 = a4 *| b2 in
  let ab43 = a4 *| b3 in
  let ab44 = a4 *| b4 in
  let c0 = ab00 in
  cut (H128.v c0 = v a0 * v b0);
  let c1 = H128 (ab01 +^ ab10) in
  cut (H128.v c1 = v a0 * v b1 + v a1 * v b0);
  let c2 = H128 (ab02 +^ ab11 +^ ab20) in
  cut(H128.v c2 = v a0 * v b2 + v a1 * v b1 + v a2 * v b0);
  let c3 = H128 (ab03 +^ ab12 +^ ab21 +^ ab30) in
  cut(H128.v c3 = v a0 * v b3 + v a1 * v b2 + v a2 * v b1 + v a3 * v b0);
  let c4 = H128 (ab04 +^ ab13 +^ ab22 +^ ab31 +^ ab40) in
  cut(H128.v c4 = v a0 * v b4 + v a1 * v b3 + v a2 * v b2 + v a3 * v b1 + v a4 * v b0);
  let c5 = H128 (ab14 +^ ab23 +^ ab32 +^ ab41) in
  cut(H128.v c5 = v a1 * v b4 + v a2 * v b3 + v a3 * v b2 + v a4 * v b1);
  let c6 = H128 (ab24 +^ ab33 +^ ab42) in
  cut(H128.v c6 = v a2 * v b4 + v a3 * v b3 + v a4 * v b2);
  let c7 = H128 (ab34 +^ ab43) in
  cut(H128.v c7 = v a3 * v b4 + v a4 * v b3);
  let c8 = ab44 in
  cut(H128.v c8 = v a4 * v b4 );
  update_wide_9 c c0 c1 c2 c3 c4 c5 c6 c7 c8


private val multiplication_:
  c:bigint_wide{length c >= 2 * norm_length - 1} ->
  a:bigint{disjoint c a} ->
  b:bigint{disjoint c b} ->
  Stack unit
     (requires (fun h -> norm h a /\ norm h b /\ live h c))
     (ensures (fun h0 u h1 -> norm h0 a /\ norm h0 b /\ live h1 c /\ modifies_1 c h0 h1
       /\ isMultiplication h0 h1 a b c
     ))
let multiplication_ c a b =
  let h0 = ST.get() in
  let a0 = a.(0ul) in let a1 = a.(1ul) in let a2 = a.(2ul) in let a3 = a.(3ul) in let a4 = a.(4ul) in
  let b0 = b.(0ul) in let b1 = b.(1ul) in let b2 = b.(2ul) in let b3 = b.(3ul) in let b4 = b.(4ul) in
  multiplication_0 c a0 a1 a2 a3 a4 b0 b1 b2 b3 b4


val multiplication:
  c:bigint_wide{length c >= 2 * norm_length - 1} ->
  a:bigint{disjoint c a} ->
  b:bigint{disjoint c b} ->
  Stack unit
     (requires (fun h -> norm h a /\ norm h b /\ live h c))
     (ensures (fun h0 u h1 -> norm h0 a /\ norm h0 b /\ live h1 c /\ modifies_1 c h0 h1
       /\ eval_wide h1 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length)
       /\ maxValue_wide h1 c (2*norm_length-1) <= norm_length * pow2 53))
let multiplication c a b =
  let h0 = ST.get() in
  multiplication_ c a b(* ; *)
  (* let h1 = ST.get() in *)
  (* lemma_multiplication h0 h1 c a b *)

(*
val multiplication_step_0: a:bigint -> b:bigint ->
  ctr:u32{U32.v ctr<norm_length /\ U32.v ctr<2*norm_length-1} ->
  c:bigint_wide{disjoint a c /\ disjoint b c} ->
  tmp:bigint_wide{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} -> Stack unit
     (requires (fun h -> live h a /\ live h b /\ live h c /\ live h tmp /\ length c >= 2*norm_length-1
       (* norm h a /\ norm h b /\ live h c /\ live h tmp *)
       (*  /\ length c >= 2*norm_length -1 *)
       (* 	/\ maxValueNorm h a < pow2 max_limb *)
       (* 	/\ maxValueNorm h b < pow2 max_limb *)
       (* 	/\ maxValue_wide h c (length c) <= w ctr * maxValueNorm h a * maxValueNorm h b *)
       ))
     (ensures (fun h0 _ h1 -> live h1 tmp /\ modifies_1 tmp h0 h1
       (* norm h0 a /\ norm h0 b /\ live h0 c /\ live h1 tmp *)
       (* /\ live h0 tmp /\ length tmp = length tmp *)
       (* /\ length c >= 2*norm_length-1 /\ length tmp >= norm_length *)
       (* /\ modifies_1 tmp h0 h1 *)
       (* /\ isScalarProduct h1 tmp h0 a (get h0 b (w ctr)) *)
       (* /\ eval_wide h1 tmp norm_length = eval h0 a norm_length * vv (get h0 b (w ctr)) *)
     ))
let multiplication_step_0 a b ctr c tmp =
  (* admit(); // OK *)
  (* let h0 = ST.get() in *)
  let s = b.(ctr) in
  (* assert(forall (n:nat). {:pattern (vv (get h0 b n))} n < norm_length ==> vv (get h0 b n) <= pow2 max_limb);  *)
  (* assert(forall (n:nat). n = w ctr ==> n < norm_length);  *)
  (* assert(True /\ vv s < pow2 max_limb);  *)
  (* assert(forall (i:nat). {:pattern (vv  (get h0 a i))}  *)
  (* 	   i < norm_length ==> vv (get h0 a i) < pow2 max_limb); *)
  (* assert(vv s < pow2 max_limb);  *)
  (* cut(forall (i:nat). (i < norm_length) ==> vv (get h0 a i) * vv s < pow2 platform_wide);  *)
  Hacl.EC.Curve25519.Bignum.Fscalar.scalar_multiplication_tr tmp a s 0ul(* ; *)
  (* let h1 = ST.get() in *)
  (* cut(True /\ vv s = vv (get h0 b (w ctr)));  *)
  (* assert(Fscalar.isScalarProduct h0 h1 0 norm_length a s tmp);  *)
  (* is_scalar_product_lemma h0 h1 a s tmp; *)
  (* Hacl.EC.Curve25519.Bignum.Fscalar.theorem_scalar_multiplication h0 h1 a s norm_length tmp *)

val multiplication_step_p1:
  a:bigint -> b:bigint -> ctr:u32{U32.v ctr<norm_length} ->
  c:bigint_wide{disjoint a c /\ disjoint b c} ->
  tmp:bigint_wide{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} -> Stack unit
     (requires (fun h -> live h a /\ live h b /\ live h c /\ live h tmp /\ length c >= 2*norm_length-1
        (* /\ norm h a /\ norm h b /\ live h c /\ live h tmp *)
        (* /\ length c >= 2*norm_length -1 *)
	(* /\ maxValueNorm h a < pow2 max_limb *)
	(* /\ maxValueNorm h b < pow2 max_limb *)
	(* /\ maxValue_wide h c (length c) <= w ctr * maxValueNorm h a * maxValueNorm h b *)
	(* /\ eval_wide h c (2*norm_length-1) = eval h a (norm_length) * eval h b (w ctr)  *)
    ))
     (ensures (fun h0 u h1 -> live h1 c /\ live h1 tmp /\ modifies_2 c tmp h0 h1
       (* /\ norm h0 a /\ norm h0 b /\ live h0 c /\ live h0 tmp *)
       (* /\ norm h1 a /\ norm h1 b /\ live h1 c /\ live h1 tmp *)
       (* /\ length c >= 2*norm_length -1 *)
       (* /\ modifies_2 c tmp h0 h1 *)
       (* /\ maxValue_wide h0 c (length c) <= w ctr * maxValueNorm h0 a * maxValueNorm h0 b *)
       (* /\ maxValue_wide h1 c (length c) <= (w ctr+1) * (maxValueNorm h0 a * maxValueNorm h0 b) *)
       (* /\ eval_wide h0 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (w ctr) *)
       (* /\ (eval_wide h1 c (2*norm_length-1) = eval_wide h0 c (2*norm_length-1) + pow2 (bitweight (templ) (w ctr)) * eval h0 a norm_length * vv (get h0 b (w ctr))) *)
     ))
let multiplication_step_p1 a b ctr c tmp =
  (* admit(); // OK *)
  (* let h0 = ST.get() in *)
  multiplication_step_0 a b ctr c tmp;
  (* let h1 = ST.get() in *)
  (* multiplication_step_lemma_01 h0 h1 a b (w ctr) c tmp;  *)
  Hacl.EC.Curve25519.Bignum.FsumWide.fsum_index c ctr tmp 0ul nlength 0ul(* ; *)
  (* let h2 = ST.get() in  *)
  (* multiplication_step_lemma_02 h0 h1 h2 a b ctr c tmp *)

(* Code : does 1 step of the multiplication (1 scalar multiplication),
   and infers the appropriate properties on sizes, values and evaluated
   values for the resulting bigint *)
val multiplication_step: a:bigint -> b:bigint -> ctr:u32{U32.v ctr < norm_length} ->
  c:bigint_wide{disjoint a c /\ disjoint b c} ->
  tmp:bigint_wide{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} -> STL unit
     (requires (fun h -> live h a /\ live h b /\ live h c /\ live h tmp /\ length c >= 2*norm_length-1
       (* norm h a /\ norm h b /\ live h c /\ live h tmp *)
       (* 	/\ length c >= 2 * norm_length - 1 *)
       (* 	/\ maxValueNorm h a < pow2 max_limb *)
       (* 	/\ maxValueNorm h b < pow2 max_limb *)
       (* 	/\ maxValue_wide h c (length c) <= w ctr * maxValueNorm h a * maxValueNorm h b *)
       (* 	/\ eval_wide h c (2*norm_length-1) = eval h a (norm_length) * eval h b (w ctr) *)
    ))
     (ensures (fun h0 u h1 -> live h1 c /\ live h1 tmp /\ modifies_2 c tmp h0 h1
       (* /\ norm h0 a /\ norm h1 a /\ norm h0 b /\ norm h1 b *)
       (* /\ live h0 c /\ live h1 c  /\ live h0 tmp /\ live h1 tmp *)
       (* /\ length c >= 2 * norm_length - 1 *)
       (* /\ modifies_2 c tmp h0 h1 *)
       (* /\ maxValueNorm h0 a < pow2 max_limb *)
       (* /\ maxValueNorm h0 b < pow2 max_limb *)
       (* /\ maxValue_wide h0 c (length c) <= w ctr * maxValueNorm h0 a * maxValueNorm h0 b *)
       (* /\ maxValue_wide h1 c (length c) <= (w ctr+1) * maxValueNorm h0 a * maxValueNorm h0 b *)
       (* /\ eval_wide h0 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (w ctr) *)
       (* /\ eval_wide h1 c (2*norm_length-1) = eval h0 a (norm_length) * vv (get h0 b (w ctr)) * pow2 (bitweight (templ) (w ctr)) + eval_wide h0 c (2*norm_length-1) *)
     ))
let multiplication_step a b ctr c tmp =
  (* let h0 = ST.get() in *)
  multiplication_step_p1 a b ctr c tmp(* ;   *)
  (* let h1 = ST.get() in *)
  (* helper_lemma_6 h0 h1 a b (w ctr) c tmp *)

(* Code : tail recursive calls to run the multiplication *)
val multiplication_aux:
  a:bigint -> b:bigint -> ctr:u32{U32.v ctr <= norm_length} ->
  c:bigint_wide{disjoint a c /\ disjoint b c} ->
  tmp:bigint_wide{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} -> STL unit
     (requires (fun h -> live h a /\ live h b /\ live h c /\ live h tmp /\ length c >= 2*norm_length-1
       (* (norm h a) /\ (norm h b) /\ (live h c) /\ (live h tmp) *)
       (* 	/\ (length c >= 2 * norm_length - 1) *)
       (* 	/\ (maxValueNorm h a < pow2 max_limb) *)
       (* 	/\ (maxValueNorm h b < pow2 max_limb) *)
       (* 	/\ (maxValue_wide h c (length c) <= (norm_length - w ctr) * (maxValueNorm h a * maxValueNorm h b)) *)
       (* 	/\ (eval_wide h c (2*norm_length-1) = eval h a (norm_length) * eval h b (norm_length - w ctr)) *)
    ))
     (ensures (fun h0 u h1 -> live h1 c /\ live h1 tmp /\ modifies_2 c tmp h0 h1
       (* (norm h0 a) /\ (norm h0 b) /\ (live h0 c) /\ (live h0 tmp) *)
       (* /\ (norm h1 a) /\ (norm h1 b) /\ (live h1 c) /\ (live h1 tmp) *)
       (* /\ (length c >= 2 * norm_length - 1) *)
       (* /\ (modifies_2 c tmp h0 h1) *)
       (* /\ (maxValueNorm h0 a < pow2 max_limb) *)
       (* /\ (maxValueNorm h0 b < pow2 max_limb) *)
       (* /\ (eval_wide h1 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length)) *)
       (* /\ (maxValue_wide h1 c (length c) <= norm_length * (maxValueNorm h0 a * maxValueNorm h0 b)) *)
     ))
let rec multiplication_aux a b ctr c tmp =
  (* let h0 = ST.get() in *)
  if U32 (ctr =^ 0ul) then ()
  else begin
    (* FproductLemmas.helper_lemma_8 norm_length ctr; *)
    multiplication_step a b (U32 (nlength -^ ctr)) c tmp;
    (* let h1 = ST.get() in     *)
    (* multiplication_aux_lemma h0 h1 a b (w ctr) c tmp; *)
    multiplication_aux a b (U32 (ctr -^ 1ul)) c tmp(* ; *)
    (* let h2 = ST.get() in *)
    (* multiplication_aux_lemma_2 h0 h1 h2 a b (w ctr) c tmp *)
  end

(* Code : core multiplication function *)
val multiplication:
  c:bigint_wide ->
  a:bigint{disjoint c a} ->
  b:bigint{disjoint c b} -> Stack unit
    (requires (fun h -> live h c /\ live h a /\ live h b /\ length c >= 2*norm_length-1
     (* norm h a /\ norm h b /\ live h c /\ null_wide h c /\ length c >= 2*norm_length-1 *)
     (* 	/\ maxValueNorm h a < pow2 max_limb *)
     (* 	/\ maxValueNorm h b < pow2 max_limb  *)
    ))
    (ensures (fun h0 u h1 -> live h1 c /\ modifies_1 c h0 h1
      (* /\ norm h0 a /\ norm h0 b /\ live h0 c /\ norm h1 a /\ norm h1 b /\ live h1 c *)
      (*  /\ length c >= 2*norm_length-1 *)
      (*  /\ null_wide h0 c /\ modifies_1 c h0 h1 *)
      (*  /\ maxValueNorm h0 a < pow2 max_limb *)
      (*  /\ maxValueNorm h0 b < pow2 max_limb *)
      (*  /\ eval_wide h1 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length) *)
      (*  /\ maxValue_wide h1 c (length c) <= norm_length * maxValueNorm h0 a * maxValueNorm h0 b  *)
    ))
let multiplication c a b =
  push_frame();
  (* admit(); // OK *)
  (* let h0 = ST.get() in *)
  let tmp = create (Hacl.Cast.uint64_to_sint128 0uL) nlength in
  (* let h1 = ST.get() in *)
  (* assert(modifies Set.empty h0 h1);  *)
  (* multiplication_lemma_1 h0 h1 c a b; *)
  (* cut(True /\ length tmp >= norm_length); *)
  (* constant_template_lemma c a;  *)
  multiplication_aux a b nlength c tmp;
  (* let h2 = ST.get() in  *)
  (* multiplication_lemma_2 h0 h1 h2 c a b tmp *)
  pop_frame()
