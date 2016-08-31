module Hacl.EC.Curve25519.Bignum.Fproduct

open FStar.Mul
open FStar.HST
open FStar.HyperStack
open FStar.Ghost
open Hacl.UInt64
open Hacl.SBuffer
open Math.Lib
open Hacl.EC.Curve25519.Parameters
open Hacl.EC.Curve25519.Bigint


#reset-options "--initial_fuel 0 --max_fuel 0"

(* Module abbreviations *)
module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module U8  = FStar.UInt8
module U32 = FStar.UInt32
module H8  = Hacl.UInt8
module H32  = Hacl.UInt32
module H64  = Hacl.UInt64

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
  (* let h0 = HST.get() in *)
  let s = b.(ctr) in
  (* assert(forall (n:nat). {:pattern (vv (get h0 b n))} n < norm_length ==> vv (get h0 b n) <= pow2 max_limb);  *)
  (* assert(forall (n:nat). n = w ctr ==> n < norm_length);  *)
  (* assert(True /\ vv s < pow2 max_limb);  *)
  (* assert(forall (i:nat). {:pattern (vv  (get h0 a i))}  *)
  (* 	   i < norm_length ==> vv (get h0 a i) < pow2 max_limb); *)
  (* assert(vv s < pow2 max_limb);  *)
  (* cut(forall (i:nat). (i < norm_length) ==> vv (get h0 a i) * vv s < pow2 platform_wide);  *)
  Hacl.EC.Curve25519.Bignum.Fscalar.scalar_multiplication_tr tmp a s 0ul(* ; *)
  (* let h1 = HST.get() in *)
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
  (* let h0 = HST.get() in *)
  multiplication_step_0 a b ctr c tmp;
  (* let h1 = HST.get() in *)
  (* multiplication_step_lemma_01 h0 h1 a b (w ctr) c tmp;  *)
  Hacl.EC.Curve25519.Bignum.FsumWide.fsum_index c ctr tmp 0ul nlength 0ul(* ; *)
  (* let h2 = HST.get() in  *)
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
  (* let h0 = HST.get() in *)
  multiplication_step_p1 a b ctr c tmp(* ;   *)
  (* let h1 = HST.get() in *)
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
  (* let h0 = HST.get() in *)
  if U32 (ctr =^ 0ul) then ()
  else begin
    (* FproductLemmas.helper_lemma_8 norm_length ctr; *)
    multiplication_step a b (U32 (nlength -^ ctr)) c tmp;
    (* let h1 = HST.get() in     *)
    (* multiplication_aux_lemma h0 h1 a b (w ctr) c tmp; *)
    multiplication_aux a b (U32 (ctr -^ 1ul)) c tmp(* ; *)
    (* let h2 = HST.get() in *)
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
  (* let h0 = HST.get() in *)
  let tmp = create (Hacl.UInt128.of_string "0") nlength in
  (* let h1 = HST.get() in *)
  (* assert(modifies Set.empty h0 h1);  *)
  (* multiplication_lemma_1 h0 h1 c a b; *)
  (* cut(True /\ length tmp >= norm_length); *)
  (* constant_template_lemma c a;  *)
  multiplication_aux a b nlength c tmp;
  (* let h2 = HST.get() in  *)
  (* multiplication_lemma_2 h0 h1 h2 c a b tmp *)
  pop_frame()
