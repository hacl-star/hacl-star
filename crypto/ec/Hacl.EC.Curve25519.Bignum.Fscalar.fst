module Hacl.EC.Curve25519.Bignum.Fscalar

open FStar.Mul
open FStar.ST
open FStar.HyperStack
open FStar.Buffer
open FStar.Buffer.Quantifiers
(* open Hacl.SBuffer *)
open FStar.Math.Lib
open FStar.Ghost
open Hacl.UInt64

open Hacl.EC.Curve25519.Parameters
open Hacl.EC.Curve25519.Bigint
open Hacl.EC.Curve25519.Utils
open Hacl.EC.Curve25519.Bignum.Fscalar.Lemmas

#reset-options "--initial_fuel 0 --max_fuel 0"

(* Module abbreviations *)
module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module U8  = FStar.UInt8
module U32 = FStar.UInt32
module H8  = Hacl.UInt8
module H32  = Hacl.UInt32
module H64  = Hacl.UInt64


val fscalar_:
  res:bigint_wide ->
  a:bigint{disjoint res a} ->
  s:s64 ->
  Stack unit
    (requires (fun h -> norm h a))
    (ensures (fun h0 _ h1 -> live h1 res /\ modifies_1 res h0 h1 /\ isScalarMult h0 h1 res a s))
let fscalar_ res a s =
  Math.Lemmas.pow2_lt_compat 64 51; Math.Lemmas.pow2_plus 51 64; Math.Lemmas.pow2_plus 64 64;
  let a0 = a.(0ul) in
  let a1 = a.(1ul) in
  let a2 = a.(2ul) in
  let a3 = a.(3ul) in
  let a4 = a.(4ul) in
  let open Hacl.UInt128 in
  let r0 = a0 *^ s in
  let r1 = a1 *^ s in
  let r2 = a2 *^ s in
  let r3 = a3 *^ s in
  let r4 = a4 *^ s in
  update_5 res r0 r1 r2 r3 r4

(*


val scalar_multiplication_tr_1: 
  res:bigint_wide -> a:bigint{disjoint res a} -> s:s64 -> 
  ctr:u32{U32.v ctr<norm_length} -> Stack unit
     (requires (fun h -> live h a /\ live h res
       (* (live h res) /\ (live h a) /\ (length a >= norm_length) /\ (length res >= norm_length) *)
       (* /\ (forall (i:nat). (i >= w ctr /\ i < norm_length) ==> v (get h a i) * v s < pow2 platform_wide) *)
     ))
     (ensures (fun h0 u h1 -> live h1 res /\ modifies_1 res h0 h1
       (* (live h0 res) /\ (live h1 res) /\ (live h0 a) /\ (live h1 a) *)
       (* /\ (length res >= norm_length) /\ (length res = length res) *)
       (* /\ (modifies_1 res h0 h1) /\ (length a >= norm_length) *)
       (* /\ (forall (i:nat). (i >= w ctr+1 /\ i < norm_length) ==> v (get h0 a i) * v s < pow2 platform_wide)  *)
       (* /\ (forall (i:nat). (i < length res /\ i <> w ctr) ==> (get h1 res i == get h0 res i)) *)
       (* /\ (Hacl.UInt128.v (get h1 res (w ctr)) = v (get h0 a (w ctr)) * v s) *)
     ))
let rec scalar_multiplication_tr_1 res a s ctr =
    let ai = a.(ctr) in
    let z = Hacl.UInt128.mul_wide ai s in
    res.(ctr) <- z

val scalar_multiplication_tr: res:bigint_wide -> a:bigint{disjoint res a} -> s:s64 -> ctr:u32{U32.v ctr<=norm_length} -> Stack unit
     (requires (fun h -> live h res /\ live h a
       (* (live h res) /\ (live h a) /\ (length a >= norm_length) /\ (length res >= norm_length) *)
       (* /\ (forall (i:nat). (i >= w ctr /\ i < norm_length) ==> v (get h a i) * v s < pow2 platform_wide) *)
     ))
     (ensures (fun h0 u h1 -> live h1 res /\ modifies_1 res h0 h1
       (* (live h0 res) /\ (live h1 res) /\ (live h0 a) /\ (live h1 a) *)
       (* /\ (modifies_1 res h0 h1) /\ (length a >= norm_length) *)
       (* /\ (forall (i:nat). (i >= w ctr /\ i < norm_length) ==> v (get h0 a i) * v s < pow2 platform_wide) *)
       (* /\ (length res >= norm_length) /\ (length res = length res) *)
       (* /\ (forall (i:nat{(i>= w ctr /\ i < norm_length)}). vv (get h1 res i) = v (get h0 a i) * v s) *)
       (* /\ (forall (i:nat{(i < length res /\ (i < w ctr \/ i >= norm_length))}).  *)
       (* 	   (get h1 res i == get h0 res i)) *)
       (* /\ (Seq.equal (sel h0 (a)) (sel h1 (a))) *)
     ))
let rec scalar_multiplication_tr res a s ctr =
  (* let h0 = ST.get() in *)
  if U32 (ctr =^ nlength) then ()
  else begin
     (* FscalarLemmas.lemma_4 norm_length ctr;  *)
     scalar_multiplication_tr_1 res a s ctr; 
     (* let h1 = ST.get() in  *)
     (* no_upd_lemma h0 h1 a (only res); *)
     scalar_multiplication_tr res a s (U32 (ctr +^ 1ul))
     (* let h2 = ST.get() in *)
     (* scalar_multiplication_tr_2 h0 h1 h2 res a s (w ctr) *)
  end

val scalar': res:bigint_wide -> a:bigint{disjoint res a} -> s:s64 -> STL unit
     (requires (fun h -> live h a /\ live h res
       (* norm h a /\ live h res *)
     ))
     (ensures (fun h0 u h1 -> live h1 res /\ modifies_1 res h0 h1
       (* /\ live h0 res /\ live h1 res /\ norm h0 a /\ norm h1 a *)
       (* /\ modifies_1 res h0 h1 *)
       (* /\ eval_wide h1 res norm_length = eval h0 a norm_length * v s *)
     ))
let scalar' res a s =
  (* let h0 = ST.get() in   *)
  (* auxiliary_lemma_0 h0 a s;  *)
  scalar_multiplication_tr res a s 0ul
  (* let h1 = ST.get() in *)
  (* (\* no_upd_lemma h0 h1 a (only res); *\) *)
  (* auxiliary_lemma_1 h0 h1 a (res);  *)
  (* theorem_scalar_multiplication h0 h1 a s norm_length res;  *)
  (* () *)

	       
