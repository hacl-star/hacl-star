module Hacl.EC.Curve25519.AddAndDouble


open FStar.Mul
open FStar.HST
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer
open Hacl.UInt64
open Hacl.SBuffer
open Math.Lib
open Hacl.EC.Curve25519.Parameters
open Hacl.EC.Curve25519.Bigint
open Hacl.EC.Curve25519.Bignum
open Hacl.EC.Curve25519.PPoint


#reset-options "--initial_fuel 0 --max_fuel 0"

(* Module abbreviations *)
module B  = Hacl.SBuffer
module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module U8  = FStar.UInt8
module U32 = FStar.UInt32
module H8  = Hacl.UInt8
module H32  = Hacl.UInt32
module H64  = Hacl.UInt64
module H128  = Hacl.UInt128

#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 20"

val double_and_add:
  two_p:point -> two_p_plus_q:point{distinct two_p two_p_plus_q /\ same_frame_2 two_p two_p_plus_q} ->
  p:point{distinct two_p p /\ distinct two_p_plus_q p /\ same_frame_2 two_p_plus_q p} ->
  p_plus_q:point{distinct two_p p_plus_q /\ distinct two_p_plus_q p_plus_q /\ distinct p_plus_q p /\ same_frame_2 p p_plus_q} ->
  q:point{same_frame q /\ frame_of q <> frame_of p} -> STStack unit
    (requires (fun h -> live h two_p /\ live h two_p_plus_q /\ live h p /\ live h p_plus_q /\ live h q))
      (* /\ onCurve h p /\ onCurve h p_plus_q /\ (onCurve h q) )) *)
    (ensures (fun h0 _ h1 -> live h1 two_p /\ live h1 two_p_plus_q /\ live h1 p /\ live h1 p_plus_q
      /\ HS.modifies_one (frame_of p) h0 h1
      /\ HS.modifies_ref (frame_of p) (refs two_p ++ refs two_p_plus_q ++ refs p ++ refs p_plus_q) h0 h1 ))
(*       live h0 two_p /\ live h0 two_p_plus_q *)
(*       /\ onCurve h0 p /\ onCurve h0 p_plus_q /\ onCurve h0 q *)
(*       /\ onCurve h1 two_p /\ onCurve h1 two_p_plus_q *)
(*       /\ live h1 p /\ live h1 p_plus_q /\ onCurve h1 q *)
(*        (\* /\ (modifies (refs two_p +++ refs two_p_plus_q +++ refs p +++ refs p_plus_q) h0 h1) *\) *)
(*        /\ (Buffer.live h1 (get_x q) /\ Buffer.live h1 (get_x p) /\ Buffer.live h1 (get_z p)  *)
(* 	 /\ Buffer.live h1 (get_x p_plus_q)  *)
(* 	 /\ Buffer.live h1 (get_z p_plus_q) /\ Buffer.live h1 (get_x two_p)  *)
(* 	 /\ Buffer.live h1 (get_z two_p) /\ Buffer.live h1 (get_x two_p_plus_q)  *)
(* 	 /\ Buffer.live h1 (get_z two_p_plus_q)) *)
(*       /\ ( *)
(* 	  let x1 = valueOf h1 (get_x q) in  *)
(* 	  let x2 = valueOf h1 (get_x p) in let z2 = valueOf h1 (get_z p) in *)
(* 	  let x3 = valueOf h1 (get_x p_plus_q) in let z3 = valueOf h1 (get_z p_plus_q) in *)
(* 	  (valueOf h1 (get_x two_p) = equation_1 x2 z2	  *)
(* //	       (((x2 ^+ z2) ^^ 2) ^* ((x2 ^- z2) ^^ 2)) *)
(* 	   /\ valueOf h1 (get_z two_p) = equation_2 x2 z2 *)
(* //	       ((4 +* x2 ^* z2) ^* (((x2 ^- z2) ^^ 2) ^+ (a24' +* (4 +* x2 ^* z2)))) *)
(* 	   /\ valueOf h1 (get_x two_p_plus_q) = equation_3 x2 z2 x3 z3 *)
(* //	       ((((x3 ^- z3) ^* (x2^+z2)) ^+ ((x3 ^+ z3) ^* (x2 ^- z2))) ^^ 2) *)
(* 	   /\ valueOf h1 (get_z two_p_plus_q) = equation_4 x2 z2 x3 z3 x1  *)
(* //	       (x1 ^* (((x3 ^- z3) ^* (x2^+z2)) ^- ((x3 ^+ z3) ^* (x2 ^- z2))) ^^ 2) *)
(* 	)) *)
let double_and_add two_p two_p_plus_q p p_plus_q q =
  (* TODO *)
  let hinit = HST.get() in
  push_frame();
  let h0 = HST.get() in
  (* *)
  let qmqp = get_x q in
  let x = get_x p in
  let z = get_z p in
  let xprime = get_x p_plus_q in
  let zprime = get_z p_plus_q in
  let x2 = get_x two_p in
  let z2 = get_z two_p in
  (* Big temporary buffer *)
  let open FStar.UInt32 in
  let nl = nlength in
  let nl2 = U32 (2ul *^ nlength -^ 1ul) in
  let tmp = create (Hacl.Cast.uint64_to_sint64 0uL) (nl +^ nl +^ nl2 +^ nl2 +^ nl2  +^ nl2  +^ nl2  +^ nl2  +^ nl2) in
  let origx      = B.sub tmp 0ul nl in
  let origxprime = B.sub tmp nl  nl in
  let zzz        = B.sub tmp (nl +^ nl) nl2 in
  let xx         = B.sub tmp (nl +^ nl +^ nl2) nl2 in
  let zz         = B.sub tmp (nl +^ nl +^ nl2 +^ nl2) nl2 in
  let xxprime    = B.sub tmp (nl +^ nl +^ nl2 +^ nl2 +^ nl2) nl2 in
  let zzprime    = B.sub tmp (nl +^ nl +^ nl2 +^ nl2 +^ nl2 +^ nl2) nl2 in
  let xxxprime   = B.sub tmp (nl +^ nl +^ nl2 +^ nl2 +^ nl2 +^ nl2 +^ nl2) nl2 in
  let zzzprime   = B.sub tmp (nl +^ nl +^ nl2 +^ nl2 +^ nl2 +^ nl2 +^ nl2 +^ nl2) nl2 in

  (* let origx = create (Hacl.Cast.uint64_to_sint64 0uL) nlength in *)
  (* let origxprime = create (Hacl.Cast.uint64_to_sint64 0uL) nlength in *)
  (* let zzz = create (Hacl.Cast.uint64_to_sint64 0uL) (U32 (2ul *^ nlength -^ 1ul)) in *)
  (* let xx = create (Hacl.Cast.uint64_to_sint64 0uL) (U32 (2ul *^ nlength -^ 1ul)) in *)
  (* let zz = create (Hacl.Cast.uint64_to_sint64 0uL) (U32 (2ul *^ nlength -^ 1ul)) in *)
  (* let xxprime = create (Hacl.Cast.uint64_to_sint64 0uL) (U32 (2ul *^ nlength -^ 1ul)) in *)
  (* let zzprime = create (Hacl.Cast.uint64_to_sint64 0uL) (U32 (2ul *^ nlength -^ 1ul)) in *)
  (* let xxxprime = create (Hacl.Cast.uint64_to_sint64 0uL) (U32 (2ul *^ nlength -^ 1ul)) in *)
  (* let zzzprime = create (Hacl.Cast.uint64_to_sint64 0uL) (U32 (2ul *^ nlength -^ 1ul)) in *)
  blit x 0ul origx 0ul nlength;
  fsum x z;
  fdifference z origx;
  blit xprime 0ul origxprime 0ul nlength;
  fsum xprime zprime;
  fdifference zprime origxprime;
  fmul xxprime xprime z;
  fmul zzprime x zprime;
  blit xxprime 0ul origxprime 0ul nlength;
  fsum xxprime zzprime;
  fdifference zzprime origxprime;
  fsquare xxxprime xxprime;
  fsquare zzzprime zzprime;
  fmul zzprime zzzprime qmqp;
  blit xxxprime 0ul (get_x two_p_plus_q) 0ul nlength;
  blit zzprime 0ul (get_z two_p_plus_q) 0ul nlength;
  fsquare xx x;
  fsquare zz z;
  fmul x2 xx zz;
  fdifference zz xx;
  Hacl.EC.Curve25519.Bignum.erase zzz nlength (U32 (nlength -^ 1ul)) 0ul;
  fscalar zzz zz (Hacl.Cast.uint64_to_sint64 a24);
  fsum zzz xx;
  fmul z2 zz zzz;
  pop_frame()

(* (\* Stateful double and add function on concrete points *\) *)
(* val double_and_add: two_p:point -> two_p_plus_q:point -> p:point -> p_plus_q:point -> q:point -> STL unit *)
(*     (requires (fun h -> live h two_p /\ live h two_p_plus_q  *)
(*       /\ onCurve h p /\ onCurve h p_plus_q /\ onCurve h q )) *)
(*     (ensures (fun h0 _ h1 -> live h0 two_p /\ live h0 two_p_plus_q *)
(*       /\ onCurve h0 p /\ onCurve h0 p_plus_q /\ onCurve h0 q *)
(*       /\ onCurve h1 two_p /\ onCurve h1 two_p_plus_q *)
(*       /\ live h1 p /\ live h1 p_plus_q /\ onCurve h1 q *)
(*        (\* /\ (modifies (refs two_p +++ refs two_p_plus_q +++ refs p +++ refs p_plus_q) h0 h1) *\) *)
(*       /\ (pointOf h1 two_p == Math.Curve.add (pointOf h0 p) (pointOf h0 p)) *)
(*       /\ (pointOf h1 two_p_plus_q == Math.Curve.add (pointOf h0 p) (pointOf h0 p_plus_q)) *)
(*     )) *)
(* let double_and_add two_p two_p_plus_q p p_plus_q q = *)
(* //  admit(); *)
(*   double_and_add' two_p two_p_plus_q p p_plus_q q *)
