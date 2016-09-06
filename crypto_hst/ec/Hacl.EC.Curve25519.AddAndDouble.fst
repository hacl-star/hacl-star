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

#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 5"

let lemma_helper_0 h0 h1 b : Lemma
  (requires (B.live h0 b /\ modifies_1 b h0 h1))
  (ensures  (HS.modifies_one (frameOf b) h0 h1 /\ HS.modifies_ref (frameOf b) (arefs (only b)) h0 h1))
  = lemma_reveal_modifies_1 b h0 h1;
    assert(TSet.mem (Buff b) (only b));
    TSet.lemma_equal_intro (arefs (only b)) !{as_ref b}

#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 5"

val double_and_add_0: p:point -> p_plus_q:point{distinct p_plus_q p /\ same_frame_2 p p_plus_q} ->
  tmp:bigint{length tmp = 73 /\ frameOf tmp <> frame_of p} -> Stack unit
    (requires (fun h -> live h p /\ live h p_plus_q /\ B.live h tmp))
    (ensures  (fun h0 _ h1 -> B.live h1 tmp
      /\ HS.modifies_one (frameOf tmp) h0 h1
      /\ HS.modifies_ref (frameOf tmp) (arefs (only tmp)) h0 h1))
let double_and_add_0 p p_plus_q tmp =
  let x = get_x p in
  let xprime = get_x p_plus_q in
  let origx      = B.sub tmp 0ul 5ul in
  let origxprime = B.sub tmp 5ul  5ul in
  let h0 = HST.get() in
  blit x 0ul origx 0ul nlength;                                // origix = tmp
  blit xprime 0ul origxprime 0ul nlength;                      // origxprime = tmp
  let h1 = HST.get() in
  lemma_helper_0 h0 h1 tmp

let lemma_helper_2 r h0 h1 (sub:TSet.set Heap.aref) (s:TSet.set Heap.aref) : Lemma
  (requires (TSet.subset sub s /\ modifies_ref r sub h0 h1))
  (ensures  (modifies_ref r s h0 h1))
  = ()

let lemma_helper_3 r s h0 h1 h2 h3 h4 : Lemma
  (requires (modifies_ref r s h0 h1 /\ modifies_ref r s h1 h2 /\ modifies_ref r s h2 h3 /\ modifies_ref r s h3 h4))
  (ensures  (modifies_ref r s h0 h4))
  = ()

let lemma_helper_1 h0 h1 h2 h3 h4 p pq : Lemma
  (requires (
    let x = get_x p in let z = get_z p in let xprime = get_x pq in let zprime = get_z pq in
    (B.live h0 x /\ B.live h1 z /\ B.live h2 xprime /\ B.live h3 zprime
    /\ modifies_1 x h0 h1 /\ modifies_1 z h1 h2 /\ modifies_1 xprime h2 h3 /\ modifies_1 zprime h3 h4
    /\ same_frame_2 p pq /\ distinct p pq)))
  (ensures  (same_frame_2 p pq
    /\ HS.modifies_one (frame_of p) h0 h4 /\ HS.modifies_ref (frame_of p) (refs p ++ refs pq) h0 h4))
  = lemma_helper_0 h0 h1 (get_x p);
    lemma_helper_0 h1 h2 (get_z p);
    lemma_helper_0 h2 h3 (get_x pq);
    lemma_helper_0 h3 h4 (get_z pq);
    let r = frame_of p in
    let s = refs p ++ refs pq in
    lemma_helper_2 r h0 h1 (arefs (only (get_x p))) s;
    lemma_helper_2 r h1 h2 (arefs (only (get_z p))) s;
    lemma_helper_2 r h2 h3 (arefs (only (get_x pq))) s;
    lemma_helper_2 r h3 h4 (arefs (only (get_z pq))) s;
    lemma_helper_3 r s h0 h1 h2 h3 h4

#reset-options "--z3timeout 20 --initial_fuel 0 --max_fuel 0"

val double_and_add_1: p:point -> p_plus_q:point{distinct p_plus_q p /\ same_frame_2 p p_plus_q} ->
  tmp:bigint{length tmp = 73 /\ frameOf tmp <> frame_of p} -> Stack unit
    (requires (fun h -> live h p /\ live h p_plus_q /\ B.live h tmp))
    (ensures  (fun h0 _ h1 -> live h1 p /\ live h1 p_plus_q
      /\ HS.modifies_one (frame_of p) h0 h1
      /\ HS.modifies_ref (frame_of p) (refs p ++ refs p_plus_q) h0 h1))
let double_and_add_1 p p_plus_q tmp =
  let x = get_x p in
  let z = get_z p in
  let xprime = get_x p_plus_q in
  let zprime = get_z p_plus_q in
  let origx      = B.sub tmp 0ul 5ul in
  let origxprime = B.sub tmp 5ul  5ul in
  let h0 = HST.get() in
  fsum x z;                                                    // x
  let h1 = HST.get() in
  cut (live h1 p /\ live h1 p_plus_q);
  fdifference z origx;                                         // z
  let h2 = HST.get() in
  cut (live h2 p /\ live h2 p_plus_q);
  fsum xprime zprime;                                          // xprime
  let h3 = HST.get() in
  cut (live h3 p /\ live h3 p_plus_q);
  fdifference zprime origxprime;                               // zprime
  let h4 = HST.get() in
  cut (live h4 p /\ live h4 p_plus_q);
  lemma_helper_1 h0 h1 h2 h3 h4 p p_plus_q

val lemma_helper_4: p:point -> p':point -> Lemma
  (requires (same_frame p /\ same_frame p' /\ frame_of p <> frame_of p'))
  (ensures  (distinct p p'))
let lemma_helper_4 p p' = ()

val lemma_helper_5: p:point -> b:bigint -> Lemma
  (requires (same_frame p /\ frame_of p <> frameOf b))
  (ensures  (disjoint (get_x p) b /\ disjoint (get_y p) b /\ disjoint (get_z p) b ))
let lemma_helper_5 p p' = ()

#reset-options "--z3timeout 100 --initial_fuel 0 --max_fuel 0"

val double_and_add_2:
  two_p:point -> two_p_plus_q:point{distinct two_p two_p_plus_q /\ same_frame_2 two_p two_p_plus_q} ->
  p:point{distinct two_p p /\ distinct two_p_plus_q p /\ same_frame_2 two_p_plus_q p} ->
  p_plus_q:point{distinct two_p p_plus_q /\ distinct two_p_plus_q p_plus_q /\ distinct p_plus_q p /\ same_frame_2 p p_plus_q} ->
  q:point{same_frame q /\ frame_of q <> frame_of p} ->
  tmp:bigint{length tmp = 73 /\ frameOf tmp <> frame_of p /\ frameOf tmp <> frame_of q} -> Stack unit
    (requires (fun h -> live h two_p /\ live h two_p_plus_q /\ live h p /\ live h p_plus_q /\ live h q
      /\ B.live h tmp))
    (ensures (fun h0 _ h1 -> B.live h1 tmp
      /\ HS.modifies_one (frameOf tmp) h0 h1
      /\ HS.modifies_ref (frameOf tmp) (arefs (only tmp)) h0 h1 ))
let double_and_add_2 pp ppq p pq q tmp =
  let qmqp = get_x q in
  let x = get_x p in
  let z = get_z p in
  let xprime = get_x pq in
  let zprime = get_z pq in
  (* Big temporary buffer *)
  let open FStar.UInt32 in
  let nl = nlength in
  let nl2 = U32 (2ul *^ nlength -^ 1ul) in
  let origxprime = B.sub tmp nl  nl in
  let xxprime    = B.sub tmp (nl +^ nl +^ nl2 +^ nl2 +^ nl2) nl2 in
  let zzprime    = B.sub tmp (nl +^ nl +^ nl2 +^ nl2 +^ nl2 +^ nl2) nl2 in
  let xxxprime   = B.sub tmp (nl +^ nl +^ nl2 +^ nl2 +^ nl2 +^ nl2 +^ nl2) nl2 in
  let zzzprime   = B.sub tmp (nl +^ nl +^ nl2 +^ nl2 +^ nl2 +^ nl2 +^ nl2 +^ nl2) nl2 in
  let h0 = HST.get() in
  fmul xxprime xprime z;                                       // xxprime = tmp
  fmul zzprime x zprime;                                       // zzprime = tmp
  let h1 = HST.get() in assert(modifies_1 tmp h0 h1);
  blit xxprime 0ul origxprime 0ul nlength;                     // origxprime = tmp
  fsum xxprime zzprime;                                        // xxprime = tmp
  let h2 = HST.get() in assert(modifies_1 tmp h1 h2);
  fdifference zzprime origxprime;                              // zzprime = tmp
  fsquare xxxprime xxprime;                                    // xxxprime = tmp
  let h3 = HST.get() in assert(modifies_1 tmp h2 h3);
  fsquare zzzprime zzprime;                                    // zzzprime = tmp
  fmul zzprime zzzprime qmqp;                                  // zzprime = tmp
  let h4 = HST.get() in assert(modifies_1 tmp h3 h4);
  assert(modifies_1 tmp h0 h4);
  lemma_helper_0 h0 h4 tmp

#reset-options "--z3timeout 5 --initial_fuel 0 --max_fuel 0"

let lemma_helper_6 r s h0 h1 h2 : Lemma
  (requires (HS.modifies_ref r s h0 h1 /\ HS.modifies_ref r s h1 h2))
  (ensures  (HS.modifies_ref r s h0 h2))
  = ()

val double_and_add_3: two_p_plus_q:point{same_frame two_p_plus_q} ->
  tmp:bigint{length tmp = 73 /\ frameOf tmp <> frame_of two_p_plus_q} -> Stack unit
  (requires (fun h -> live h two_p_plus_q /\ B.live h tmp))
  (ensures  (fun h0 _ h1 -> live h1 two_p_plus_q
    /\ HS.modifies_one (frame_of two_p_plus_q) h0 h1
    /\ HS.modifies_ref (frame_of two_p_plus_q) (refs two_p_plus_q) h0 h1))
let double_and_add_3 two_p_plus_q tmp =
  let open FStar.UInt32 in
  let nl = nlength in
  let nl2 = U32 (2ul *^ nlength -^ 1ul) in
  let h = HST.get() in
  let zzprime    = B.sub tmp (nl +^ nl +^ nl2 +^ nl2 +^ nl2 +^ nl2) nl2 in
  let xxxprime   = B.sub tmp (nl +^ nl +^ nl2 +^ nl2 +^ nl2 +^ nl2 +^ nl2) nl2 in
  let h0 = HST.get() in
  blit xxxprime 0ul (get_x two_p_plus_q) 0ul nlength;          // ppq_x
  let h1 = HST.get() in
  blit zzprime 0ul (get_z two_p_plus_q) 0ul nlength;           // ppq_z
  let h2 = HST.get() in
  lemma_helper_0 h0 h1 (get_x two_p_plus_q);
  lemma_helper_0 h1 h2 (get_z two_p_plus_q);
  lemma_helper_2 (frame_of two_p_plus_q) h0 h1 (arefs (only (get_x two_p_plus_q))) (refs two_p_plus_q);
  lemma_helper_2 (frame_of two_p_plus_q) h1 h2 (arefs (only (get_z two_p_plus_q))) (refs two_p_plus_q);
  lemma_helper_6 (frame_of two_p_plus_q) (refs two_p_plus_q) h0 h1 h2;
  ()

val double_and_add_4: p:point{same_frame p} ->
  tmp:bigint{length tmp = 73 /\ frameOf tmp <> frame_of p} -> Stack unit
    (requires (fun h -> live h p /\ B.live h tmp))
    (ensures  (fun h0 _ h1 -> B.live h1 tmp
      /\ HS.modifies_one (frameOf tmp) h0 h1
      /\ HS.modifies_ref (frameOf tmp) (arefs (only tmp)) h0 h1))
let double_and_add_4 p tmp =
  let open FStar.UInt32 in
  let nl = nlength in
  let nl2 = U32 (2ul *^ nlength -^ 1ul) in
  let x = get_x p in
  let z = get_z p in
  let h0 = HST.get() in
  let xx         = B.sub tmp (nl +^ nl +^ nl2) nl2 in
  let zz         = B.sub tmp (nl +^ nl +^ nl2 +^ nl2) nl2 in
  fsquare xx x;
  fsquare zz z;
  let h1 = HST.get() in
  lemma_helper_0 h0 h1 tmp;
  ()

#reset-options "--z3timeout 5 --initial_fuel 0 --max_fuel 0"

val double_and_add_5: tmp:bigint{length tmp = 73} -> Stack unit
    (requires (fun h -> B.live h tmp))
    (ensures  (fun h0 _ h1 -> B.live h1 tmp
      /\ HS.modifies_one (frameOf tmp) h0 h1
      /\ HS.modifies_ref (frameOf tmp) (arefs (only tmp)) h0 h1))
let double_and_add_5 tmp =
  let open FStar.UInt32 in
  let nl = nlength in
  let nl2 = U32 (2ul *^ nlength -^ 1ul) in
  let zzz        = B.sub tmp (nl +^ nl) nl2 in
  let xx         = B.sub tmp (nl +^ nl +^ nl2) nl2 in
  let zz         = B.sub tmp (nl +^ nl +^ nl2 +^ nl2) nl2 in
  let h0 = HST.get() in
  fdifference zz xx;
  Hacl.EC.Curve25519.Bignum.erase zzz nlength (U32 (nlength -^ 1ul)) 0ul;
  let h1 = HST.get() in assert(modifies_1 tmp h0 h1);
  fscalar zzz zz (Hacl.Cast.uint64_to_sint64 a24);
  fsum zzz xx;
  let h2 = HST.get() in assert(modifies_1 tmp h1 h2);
  cut(modifies_1 tmp h0 h2);
  lemma_helper_0 h0 h2 tmp

#reset-options "--z3timeout 1000 --initial_fuel 0 --max_fuel 0"

val double_and_add:
  two_p:point -> two_p_plus_q:point{distinct two_p two_p_plus_q /\ same_frame_2 two_p two_p_plus_q} ->
  p:point{distinct two_p p /\ distinct two_p_plus_q p /\ same_frame_2 two_p_plus_q p} ->
  p_plus_q:point{distinct two_p p_plus_q /\ distinct two_p_plus_q p_plus_q /\ distinct p_plus_q p /\ same_frame_2 p p_plus_q} ->
  q:point{same_frame q /\ frame_of q <> frame_of p} -> Stack unit
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

  double_and_add_0 p p_plus_q tmp;
  double_and_add_1 p p_plus_q tmp;
  let h = HST.get() in assume (live h two_p /\ live h two_p_plus_q /\ live h p /\ live h p_plus_q /\ live h q /\ B.live h tmp);
  double_and_add_2 two_p two_p_plus_q p p_plus_q q tmp;
  double_and_add_3 two_p_plus_q tmp;
  let h = HST.get() in assume (live h p /\ B.live h tmp);
  double_and_add_4 p tmp;

  let h = HST.get() in assume (live h two_p /\ B.live h tmp);
  fmul x2 xx zz;
  let h' = HST.get() in
  lemma_reveal_modifies_1 x2 h h';

  double_and_add_5 tmp;

  (* fdifference zz xx; *)
  (* Hacl.EC.Curve25519.Bignum.erase zzz nlength (U32 (nlength -^ 1ul)) 0ul; *)
  (* fscalar zzz zz (Hacl.Cast.uint64_to_sint64 a24); *)
  (* fsum zzz xx; *)

  let h = HST.get() in
  fmul z2 zz zzz;
  let h' = HST.get() in
  lemma_reveal_modifies_1 z2 h h';

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
