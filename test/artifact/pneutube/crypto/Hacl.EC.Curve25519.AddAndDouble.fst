module Hacl.EC.Curve25519.AddAndDouble


open FStar.Mul
open FStar.ST
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer
open Hacl.UInt64

open FStar.Buffer
open FStar.Math.Lib
open Hacl.EC.Curve25519.Parameters
open Hacl.EC.Curve25519.Bigint
open Hacl.EC.Curve25519.Bignum
open Hacl.EC.Curve25519.PPoint


#reset-options "--initial_fuel 0 --max_fuel 0"

(* Module abbreviations *)
module B = FStar.Buffer
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


#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 100"

private val double_and_add_0:
  pp:point -> ppq:point{distinct pp ppq /\ same_frame_2 pp ppq} ->
  p:point{distinct pp p /\ distinct ppq p /\ same_frame_2 ppq p} ->
  pq:point{distinct pp pq /\ distinct ppq pq /\ distinct pq p /\ same_frame_2 p pq} ->
  q:point{same_frame q /\ frame_of q <> frame_of p} ->
  tmp:bigint{length tmp = 75 /\ frameOf tmp <> frame_of q /\ frameOf tmp <> frame_of p} -> Stack unit
    (requires (fun h -> live h pp /\ live h ppq /\ live h q /\ live h p /\ live h pq /\ B.live h tmp))
    (ensures  (fun h0 _ h1 -> B.live h1 tmp /\ live h1 pp /\ live h1 ppq /\ live h1 p /\ live h1 pq
      /\ live h1 q
      /\ HS.modifies_one (frameOf tmp) h0 h1
      /\ HS.modifies_ref (frameOf tmp) (arefs (only tmp)) h0 h1))
let double_and_add_0 pp ppq p p_plus_q q tmp =
  let x = get_x p in
  let xprime = get_x p_plus_q in
  let origx      = B.sub tmp 0ul 6ul in
  let origxprime = B.sub tmp 6ul 6ul in
  let h0 = ST.get() in
  blit x 0ul origx 0ul nlength;                                // origix = tmp
  blit xprime 0ul origxprime 0ul nlength;                      // origxprime = tmp
  let h1 = ST.get() in
  lemma_helper_0 h0 h1 tmp;
  ()


#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 20"

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


#reset-options "--z3timeout 100 --initial_fuel 0 --max_fuel 0"

private val double_and_add_1:
  pp:point -> ppq:point{distinct pp ppq /\ same_frame_2 pp ppq} ->
  p:point{distinct pp p /\ distinct ppq p /\ same_frame_2 ppq p} ->
  pq:point{distinct pp pq /\ distinct ppq pq /\ distinct pq p /\ same_frame_2 p pq} ->
  q:point{same_frame q /\ frame_of q <> frame_of p} ->
  tmp:bigint{length tmp = 75 /\ frameOf tmp <> frame_of q /\ frameOf tmp <> frame_of p} -> Stack unit
    (requires (fun h -> live h pp /\ live h ppq /\ live h q /\ live h p /\ live h pq /\ B.live h tmp))
    (ensures  (fun h0 _ h1 -> live h1 p /\ live h1 pq /\ live h1 pp /\ live h1 ppq /\ live h1 q
      /\ B.live h1 tmp
      /\ HS.modifies_one (frame_of p) h0 h1
      /\ HS.modifies_ref (frame_of p) (refs p ++ refs pq) h0 h1))
let double_and_add_1 pp ppq p p_plus_q q tmp =
  let x = get_x p in
  let z = get_z p in
  let xprime = get_x p_plus_q in
  let zprime = get_z p_plus_q in
  let origx      = B.sub tmp 0ul 6ul in
  let origxprime = B.sub tmp 6ul 6ul in
  let h0 = ST.get() in
  fsum x z;                                                    // x
  let h1 = ST.get() in
  cut (live h1 p /\ live h1 p_plus_q);
  fdifference z origx;                                         // z
  let h2 = ST.get() in
  cut (live h2 p /\ live h2 p_plus_q);
  fsum xprime zprime;                                          // xprime
  let h3 = ST.get() in
  cut (live h3 p /\ live h3 p_plus_q);
  fdifference zprime origxprime;                               // zprime
  let h4 = ST.get() in
  cut (live h4 p /\ live h4 p_plus_q);
  lemma_helper_1 h0 h1 h2 h3 h4 p p_plus_q;
  ()


val lemma_helper_4: p:point -> p':point -> Lemma
  (requires (same_frame p /\ same_frame p' /\ frame_of p <> frame_of p'))
  (ensures  (distinct p p'))
let lemma_helper_4 p p' = ()

val lemma_helper_5: p:point -> b:bigint -> Lemma
  (requires (same_frame p /\ frame_of p <> frameOf b))
  (ensures  (disjoint (get_x p) b /\ disjoint (get_y p) b /\ disjoint (get_z p) b ))
let lemma_helper_5 p p' = ()

#reset-options "--z3timeout 50 --initial_fuel 0 --max_fuel 0"

let lemma_helper_8 pp ppq p pq q tmp h0 h1 : Lemma
  (requires (HS.modifies_one (frameOf tmp) h0 h1 /\ live h0 pp /\ live h0 ppq /\ live h0 p /\ live h0 pq /\ live h0 q
    /\ same_frame_2 pp ppq /\ same_frame_2 ppq p /\ same_frame_2 p pq /\ same_frame q /\ frame_of q <> frameOf tmp /\ frame_of p <> frameOf tmp))
  (ensures  (live h1 pp /\ live h1 ppq /\ live h1 p /\ live h1 pq /\ live h1 q))
  = ()


#reset-options "--z3timeout 100 --initial_fuel 0 --max_fuel 0"

private val double_and_add_2:
  pp:point -> ppq:point{distinct pp ppq /\ same_frame_2 pp ppq} ->
  p:point{distinct pp p /\ distinct ppq p /\ same_frame_2 ppq p} ->
  pq:point{distinct pp pq /\ distinct ppq pq /\ distinct pq p /\ same_frame_2 p pq} ->
  q:point{same_frame q /\ frame_of q <> frame_of p} ->
  tmp:bigint{length tmp = 75 /\ frameOf tmp <> frame_of q /\ frameOf tmp <> frame_of p} -> Stack unit
    (requires (fun h -> live h pp /\ live h ppq /\ live h q /\ live h p /\ live h pq /\ B.live h tmp))
    (ensures (fun h0 _ h1 -> live h1 pp /\ live h1 ppq /\ live h1 p /\ live h1 pq /\ live h1 q
      /\ B.live h1 tmp
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
  let nl = U32 (nlength +^ 1ul) in
  let nl2 = U32 (2ul *^ nlength -^ 1ul) in
  let origxprime = B.sub tmp nl  nl in
  let xxprime    = B.sub tmp (nl +^ nl +^ nl2 +^ nl2 +^ nl2) nl2 in
  let zzprime    = B.sub tmp (nl +^ nl +^ nl2 +^ nl2 +^ nl2 +^ nl2) nl2 in
  let xxxprime   = B.sub tmp (nl +^ nl +^ nl2 +^ nl2 +^ nl2 +^ nl2 +^ nl2) nl2 in
  let zzzprime   = B.sub tmp (nl +^ nl +^ nl2 +^ nl2 +^ nl2 +^ nl2 +^ nl2 +^ nl2) nl2 in
  let h0 = ST.get() in
  fmul xxprime xprime z;                                       // xxprime = tmp
  fmul zzprime x zprime;                                       // zzprime = tmp
  let h1 = ST.get() in cut(modifies_1 tmp h0 h1 /\ equal_domains h0 h1);
  blit xxprime 0ul origxprime 0ul nlength;                     // origxprime = tmp
  fsum xxprime zzprime;                                        // xxprime = tmp
  let h2 = ST.get() in cut(modifies_1 tmp h1 h2 /\ equal_domains h1 h2);
  fdifference zzprime origxprime;                              // zzprime = tmp
  fsquare xxxprime xxprime;                                    // xxxprime = tmp
  let h3 = ST.get() in cut(modifies_1 tmp h2 h3 /\ equal_domains h2 h3);
  fsquare zzzprime zzprime;                                    // zzzprime = tmp
  fmul zzprime zzzprime qmqp;                                  // zzprime = tmp
  let h4 = ST.get() in cut(modifies_1 tmp h3 h4 /\ equal_domains h3 h4);
  cut(modifies_1 tmp h0 h4);
  lemma_helper_0 h0 h4 tmp;
  lemma_helper_8 pp ppq p pq q tmp h0 h4


#reset-options "--z3timeout 50 --initial_fuel 0 --max_fuel 0"

let lemma_helper_6 r s h0 h1 h2 : Lemma
  (requires (HS.modifies_ref r s h0 h1 /\ HS.modifies_ref r s h1 h2))
  (ensures  (HS.modifies_ref r s h0 h2))
  = ()

private val double_and_add_3:
  pp:point -> ppq:point{distinct pp ppq /\ same_frame_2 pp ppq} ->
  p:point{distinct pp p /\ distinct ppq p /\ same_frame_2 ppq p} ->
  pq:point{distinct pp pq /\ distinct ppq pq /\ distinct pq p /\ same_frame_2 p pq} ->
  q:point{same_frame q /\ frame_of q <> frame_of p} ->
  tmp:bigint{length tmp = 75 /\ frameOf tmp <> frame_of q /\ frameOf tmp <> frame_of p} -> Stack unit
    (requires (fun h -> live h pp /\ live h ppq /\ live h q /\ live h p /\ live h pq /\ B.live h tmp))
    (ensures  (fun h0 _ h1 -> live h1 pp /\ live h1 ppq /\ live h1 p /\ live h1 pq /\ live h1 q
      /\ B.live h1 tmp
      /\ HS.modifies_one (frame_of ppq) h0 h1
      /\ HS.modifies_ref (frame_of ppq) (refs ppq) h0 h1))
let double_and_add_3 pp two_p_plus_q p pq q tmp =
  let open FStar.UInt32 in
  let nl = U32 (nlength +^ 1ul) in
  let nl2 = U32 (2ul *^ nlength -^ 1ul) in
  let h = ST.get() in
  let zzprime    = B.sub tmp (nl +^ nl +^ nl2 +^ nl2 +^ nl2 +^ nl2) nl2 in
  let xxxprime   = B.sub tmp (nl +^ nl +^ nl2 +^ nl2 +^ nl2 +^ nl2 +^ nl2) nl2 in
  let h0 = ST.get() in
  blit xxxprime 0ul (get_x two_p_plus_q) 0ul nlength;          // ppq_x
  let h1 = ST.get() in
  blit zzprime 0ul (get_z two_p_plus_q) 0ul nlength;           // ppq_z
  let h2 = ST.get() in
  lemma_helper_0 h0 h1 (get_x two_p_plus_q);
  lemma_helper_0 h1 h2 (get_z two_p_plus_q);
  lemma_helper_2 (frame_of two_p_plus_q) h0 h1 (arefs (only (get_x two_p_plus_q))) (refs two_p_plus_q);
  lemma_helper_2 (frame_of two_p_plus_q) h1 h2 (arefs (only (get_z two_p_plus_q))) (refs two_p_plus_q);
  lemma_helper_6 (frame_of two_p_plus_q) (refs two_p_plus_q) h0 h1 h2;
  ()


#reset-options "--z3timeout 20 --initial_fuel 0 --max_fuel 0"

private val double_and_add_4:
  pp:point -> ppq:point{distinct pp ppq /\ same_frame_2 pp ppq} ->
  p:point{distinct pp p /\ distinct ppq p /\ same_frame_2 ppq p} ->
  pq:point{distinct pp pq /\ distinct ppq pq /\ distinct pq p /\ same_frame_2 p pq} ->
  q:point{same_frame q /\ frame_of q <> frame_of p} ->
  tmp:bigint{length tmp = 75 /\ frameOf tmp <> frame_of q /\ frameOf tmp <> frame_of p} -> Stack unit
    (requires (fun h -> live h pp /\ live h ppq /\ live h q /\ live h p /\ live h pq /\ B.live h tmp))
    (ensures  (fun h0 _ h1 -> live h1 pp /\ live h1 ppq /\ live h1 p /\ live h1 pq /\ live h1 q
      /\ B.live h1 tmp
      /\ HS.modifies_one (frameOf tmp) h0 h1
      /\ HS.modifies_ref (frameOf tmp) (arefs (only tmp)) h0 h1))
let double_and_add_4 pp ppq p pq q tmp =
  let open FStar.UInt32 in
  let nl = U32 (nlength +^ 1ul) in
  let nl2 = U32 (2ul *^ nlength -^ 1ul) in
  let x = get_x p in
  let z = get_z p in
  let h0 = ST.get() in
  let xx         = B.sub tmp (nl +^ nl +^ nl2) nl2 in
  let zz         = B.sub tmp (nl +^ nl +^ nl2 +^ nl2) nl2 in
  fsquare xx x;
  fsquare zz z;
  let h1 = ST.get() in
  lemma_helper_0 h0 h1 tmp;
  ()


#reset-options "--z3timeout 100 --initial_fuel 0 --max_fuel 0"

private val double_and_add_5:
  pp:point -> ppq:point{distinct pp ppq /\ same_frame_2 pp ppq} ->
  p:point{distinct pp p /\ distinct ppq p /\ same_frame_2 ppq p} ->
  pq:point{distinct pp pq /\ distinct ppq pq /\ distinct pq p /\ same_frame_2 p pq} ->
  q:point{same_frame q /\ frame_of q <> frame_of p} ->
  tmp:bigint{length tmp = 75 /\ frameOf tmp <> frame_of q /\ frameOf tmp <> frame_of p} -> Stack unit
    (requires (fun h -> live h pp /\ live h ppq /\ live h q /\ live h p /\ live h pq /\ B.live h tmp))
    (ensures  (fun h0 _ h1 -> live h1 pp /\ live h1 ppq /\ live h1 p /\ live h1 pq /\ live h1 q
      /\ B.live h1 tmp
      /\ HS.modifies_one (frameOf tmp) h0 h1
      /\ HS.modifies_ref (frameOf tmp) (arefs (only tmp)) h0 h1))
let double_and_add_5 pp ppq p pq q tmp =
  let open FStar.UInt32 in
  let nl = U32 (nlength +^ 1ul) in
  let nl2 = U32 (2ul *^ nlength -^ 1ul) in
  let zzz        = B.sub tmp (nl +^ nl) nl2 in
  let xx         = B.sub tmp (nl +^ nl +^ nl2) nl2 in
  let zz         = B.sub tmp (nl +^ nl +^ nl2 +^ nl2) nl2 in
  let h0 = ST.get() in
  fdifference zz xx;
  (* zzz.(nlength) <- 0uL; *)
  (* zzz.(U32 (nlength +^ 1ul)) <- 0uL; *)
  (* zzz.(U32 (nlength +^ 2ul)) <- 0uL; *)
  (* zzz.(U32 (nlength +^ 3ul)) <- 0uL; *)
  (* Hacl.EC.Curve25519.Bignum.erase zzz nlength (U32 (nlength -^ 1ul)) 0ul; *)
  let h1 = ST.get() in assert(modifies_1 tmp h0 h1);
  fscalar zzz zz (Hacl.Cast.uint64_to_sint64 a24);
  fsum zzz xx;
  let h2 = ST.get() in assert(modifies_1 tmp h1 h2);
  cut(modifies_1 tmp h0 h2);
  lemma_helper_0 h0 h2 tmp;
  ()


#reset-options "--z3timeout 20 --initial_fuel 0 --max_fuel 0"

let lemma_helper_x (r:HH.rid) h0 h1 h2 h3 h4 h5 h6 h7 h8 : Lemma
  (requires (h0.tip <> r
    /\ HS.modifies_one h0.tip h0 h1 /\ h0.tip = h1.tip
    /\ HS.modifies_one r h1 h2 /\ h1.tip = h2.tip
    /\ HS.modifies_one h0.tip h2 h3 /\ h2.tip = h3.tip
    /\ HS.modifies_one r h3 h4 /\ h3.tip = h4.tip
    /\ HS.modifies_one h0.tip h4 h5 /\ h4.tip = h5.tip
    /\ HS.modifies_one r h5 h6 /\ h5.tip = h6.tip
    /\ HS.modifies_one h0.tip h6 h7 /\ h6.tip = h7.tip
    /\ HS.modifies_one r h7 h8 /\ h7.tip = h8.tip))
  (ensures  (HH.modifies_just (Set.union (Set.singleton h0.tip) (Set.singleton r)) h0.h h8.h))
  = ()


#reset-options "--z3timeout 20 --initial_fuel 0 --max_fuel 0"

let lemma_helper_y r sub s h0 h1 : Lemma
  (requires (HS.modifies_ref r sub h0 h1 /\ TSet.subset sub s))
  (ensures  (HS.modifies_ref r s h0 h1))
  = ()

let lemma_helper_z r r' s h0 h1 : Lemma
  (requires (HS.modifies_one r h0 h1 /\ r <> r' /\ h0.tip = h1.tip /\ Map.contains h0.h r'))
  (ensures  (HS.modifies_ref r' s h0 h1))
  = ()

let lemma_helper_w pp ppq p pq : Lemma
  (TSet.subset (arefs (only (get_x pp))) (refs pp ++ refs ppq ++ refs p ++ refs pq)
    /\ TSet.subset (arefs (only (get_z pp))) (refs pp ++ refs ppq ++ refs p ++ refs pq))
  = ()

let lemma_helper_xx (r:HH.rid) s h0 h1 h2 h3 h4 h5 h6 h7 h8 : Lemma
  (requires (
    HS.modifies_ref r s h0 h1
    /\ HS.modifies_ref r s h1 h2
    /\ HS.modifies_ref r s h2 h3
    /\ HS.modifies_ref r s h3 h4
    /\ HS.modifies_ref r s h4 h5
    /\ HS.modifies_ref r s h5 h6
    /\ HS.modifies_ref r s h6 h7
    /\ HS.modifies_ref r s h7 h8))
  (ensures  (HS.modifies_ref r s h0 h8))
  = ()


#reset-options "--z3timeout 100 --initial_fuel 0 --max_fuel 0"

private val double_and_add_:
  two_p:point -> two_p_plus_q:point{distinct two_p two_p_plus_q /\ same_frame_2 two_p two_p_plus_q} ->
  p:point{distinct two_p p /\ distinct two_p_plus_q p /\ same_frame_2 two_p_plus_q p} ->
  p_plus_q:point{distinct two_p p_plus_q /\ distinct two_p_plus_q p_plus_q /\ distinct p_plus_q p /\ same_frame_2 p p_plus_q} ->
  q:point{same_frame q /\ frame_of q <> frame_of p} ->
  tmp:bigint{length tmp = 75 /\ frameOf tmp <> frame_of q /\ frameOf tmp <> frame_of p} ->
  Stack unit
    (requires (fun h -> live h two_p /\ live h two_p_plus_q /\ live h p /\ live h p_plus_q /\ live h q
      /\ B.live h tmp /\ h.tip = frameOf tmp))
    (ensures (fun h0 _ h1 -> live h1 two_p /\ live h1 two_p_plus_q /\ live h1 p /\ live h1 p_plus_q
      /\ B.live h1 tmp
      /\ HH.modifies_just (Set.union (Set.singleton (frameOf tmp)) (Set.singleton (frame_of p))) h0.h h1.h
      /\ HS.modifies_ref (frame_of p) (refs two_p ++ refs two_p_plus_q ++ refs p ++ refs p_plus_q) h0 h1 ))
let double_and_add_ pp ppq p pq q tmp =
  let open FStar.UInt32 in
  let nl = U32 (nlength +^ 1ul) in
  let nl2 = U32 (2ul *^ nlength -^ 1ul) in
  let zzz        = B.sub tmp (nl +^ nl) nl2 in
  let xx         = B.sub tmp (nl +^ nl +^ nl2) nl2 in
  let zz         = B.sub tmp (nl +^ nl +^ nl2 +^ nl2) nl2 in
  let h0 = ST.get() in
  double_and_add_0 pp ppq p pq q tmp;
  let h1 = ST.get() in
  lemma_helper_z (frameOf tmp) (frame_of p) (refs pp ++ refs ppq ++ refs p ++ refs pq) h0 h1;
  double_and_add_1 pp ppq p pq q tmp;
  let h2 = ST.get() in
  lemma_helper_y (frame_of p) (refs p ++ refs pq) (refs pp ++ refs ppq ++ refs p ++ refs pq) h1 h2;
  double_and_add_2 pp ppq p pq q tmp;
  let h3 = ST.get() in
  lemma_helper_z (frameOf tmp) (frame_of p) (refs pp ++ refs ppq ++ refs p ++ refs pq) h2 h3;
  double_and_add_3 pp ppq p pq q tmp;
  let h4 = ST.get() in
  lemma_helper_y (frame_of ppq) (refs ppq) (refs pp ++ refs ppq ++ refs p ++ refs pq) h3 h4;
  double_and_add_4 pp ppq p pq q tmp;
  let h5 = ST.get() in
  lemma_helper_z (frameOf tmp) (frame_of p) (refs pp ++ refs ppq ++ refs p ++ refs pq) h4 h5;
  fmul (get_x pp) xx zz;
  let h6 = ST.get() in
  lemma_helper_0 h5 h6 (get_x pp);
  lemma_helper_w pp ppq p pq;
  lemma_helper_y (frame_of p) (arefs (only (get_x pp))) (refs pp ++ refs ppq ++ refs p ++ refs pq) h5 h6;
  double_and_add_5 pp ppq p pq q tmp;
  let h7 = ST.get() in
  lemma_helper_z (frameOf tmp) (frame_of p) (refs pp ++ refs ppq ++ refs p ++ refs pq) h6 h7;
  fmul (get_z pp) zz zzz;
  let h8 = ST.get() in
  lemma_helper_0 h7 h8 (get_z pp);
  lemma_helper_y (frame_of p) (arefs (only (get_z pp))) (refs pp ++ refs ppq ++ refs p ++ refs pq) h7 h8;
  lemma_helper_x (frame_of p) h0 h1 h2 h3 h4 h5 h6 h7 h8;
  lemma_helper_xx (frame_of p) (refs pp ++ refs ppq ++ refs p ++ refs pq) h0 h1 h2 h3 h4 h5 h6 h7 h8;
  ()

#reset-options "--z3timeout 20 --initial_fuel 0 --max_fuel 0"

let lemma_helper_7 hinit h0 h1 h2 hfin r : Lemma
  (requires (fresh_frame hinit h0 /\ HS.modifies_one h0.tip h0 h1 /\ HH.modifies_just (Set.union (Set.singleton h0.tip) (Set.singleton r)) h1.h h2.h /\ popped h2 hfin /\ equal_domains hinit hfin /\ equal_domains h1 h2))
  (ensures  (HS.modifies_one r hinit hfin))
  = ()


#reset-options "--z3timeout 20 --initial_fuel 0 --max_fuel 0"

val double_and_add:
  two_p:point -> two_p_plus_q:point{distinct two_p two_p_plus_q /\ same_frame_2 two_p two_p_plus_q} ->
  p:point{distinct two_p p /\ distinct two_p_plus_q p /\ same_frame_2 two_p_plus_q p} ->
  p_plus_q:point{distinct two_p p_plus_q /\ distinct two_p_plus_q p_plus_q /\ distinct p_plus_q p /\ same_frame_2 p p_plus_q} ->
  q:point{same_frame q /\ frame_of q <> frame_of p} -> Stack unit
    (requires (fun h -> live h two_p /\ live h two_p_plus_q /\ live h p /\ live h p_plus_q /\ live h q))
    (ensures (fun h0 _ h1 -> live h1 two_p /\ live h1 two_p_plus_q /\ live h1 p /\ live h1 p_plus_q
      /\ HS.modifies_one (frame_of p) h0 h1
      /\ HS.modifies_ref (frame_of p) (refs two_p ++ refs two_p_plus_q ++ refs p ++ refs p_plus_q) h0 h1 ))
let double_and_add two_p two_p_plus_q p p_plus_q q =
  let hinit = ST.get() in
  push_frame();
  let h0 = ST.get() in
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
  let nl = U32 (nlength +^ 1ul) in
  let nl2 = U32 (2ul *^ nlength -^ 1ul) in
  let tmp = create (Hacl.Cast.uint64_to_sint64 0uL) (nl +^ nl +^ nl2 +^ nl2 +^ nl2  +^ nl2  +^ nl2  +^ nl2  +^ nl2) in
  let h1 = ST.get() in
  lemma_reveal_modifies_0 h0 h1;
  double_and_add_ two_p two_p_plus_q p p_plus_q q tmp;
  let h2 = ST.get() in
  pop_frame();
  let hfin = ST.get() in
  lemma_helper_7 hinit h0 h1 h2 hfin (frame_of p);
  ()
