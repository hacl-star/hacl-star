module Hacl.EC.Curve25519.PPoint

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

noeq type point = | Point: x:bigint -> y:bigint -> z:bigint -> point

val get_x: point -> Tot bigint
let get_x p = Point.x p
val get_y: point -> Tot bigint
let get_y p = Point.y p
val get_z: point -> Tot bigint
let get_z p = Point.z p


// Separation between the references of all three coordinates
type separateCoordinates (p:point) =
  disjoint (get_x p) (get_y p) /\ disjoint (get_x p) (get_z p) /\ disjoint (get_y p) (get_z p)

// Point "live" in memory 'h'
type live (h:heap) (p:point) =
  live h (get_x p) /\ live h (get_y p) /\ live h (get_z p) /\ separateCoordinates p

// Two distincts points from a memory point of view
type distinct (a:point) (b:point) =
  disjoint (get_x a) (get_x b) /\ disjoint (get_x a) (get_y b) /\ disjoint (get_x a) (get_z b)
  /\ disjoint (get_y a) (get_x b) /\ disjoint (get_y a) (get_y b) /\ disjoint (get_y a) (get_z b)
  /\ disjoint (get_z a) (get_x b) /\ disjoint (get_z a) (get_y b) /\ disjoint (get_z a) (get_z b)

let op_Plus_Plus (#a:Type) (s:TSet.set a) (s':TSet.set a) : GTot (TSet.set a) = TSet.union s s'

val refs: p:point -> GTot (TSet.set Heap.aref)
let refs p = arefs (only (get_x p) ++ only (get_y p) ++ (only (get_z p)))


val make: bigint -> bigint -> bigint -> Tot point
let make x y z = Point x y z

val swap_conditional_aux': a:bigint -> b:bigint{disjoint a b} ->
  is_swap:s64{v is_swap = pow2 platform_size -1 \/ v is_swap = 0} ->
  ctr:u32{U32.v ctr<=norm_length} -> STL unit
    (requires (fun h -> B.live h a /\ B.live h b))
      (* norm h a /\ norm h b)) *)
    (ensures (fun h0 _ h1 -> B.live h1 a /\ B.live h1 b /\ modifies_2 a b h0 h1))
      (* /\ norm h0 a /\ norm h0 b /\ norm h1 a /\ norm h1 b *)
      (* (\* /\ EqSub h0 a 0 h1 a 0 ctr /\ EqSub h0 b 0 h1 b 0 ctr *\) *)
      (* /\ partialSwap h0 h1 is_swap (w ctr) a b)) *)
let rec swap_conditional_aux' a b swap ctr =
  (* let h0 = HST.get() in *)
  if U32 (nlength =^ ctr) then ()
  else begin
    (* admitP (True /\ w ctr < norm_length);  *)
    let ai = a.(ctr) in
    let bi = b.(ctr) in
    let y = ai ^^ bi in
    let x = swap &^ y in
    let ai' =  x ^^ ai in
    let bi' = x ^^ bi in
    // Definition of the bitwise operations
    (* admitP (v swap = 0 ==> (v ai' = v ai /\ v bi' = v bi)); *)
    (* admitP (v swap = pow2 platform_size - 1 ==> (v ai' = v bi /\ v bi' = v ai));  *)
    a.(ctr) <- ai';
    (* let h2 = HST.get() in *)
    b.(ctr) <- bi';
    (* let h3 = HST.get() in  *)
    (* upd_lemma h0 h2 a ctr ai';  *)
    (* no_upd_lemma h0 h2 b (only a);  *)
    (* upd_lemma h2 h3 b ctr bi';   *)
    (* no_upd_lemma h2 h3 a (only b);  *)
    swap_conditional_aux' a b swap (U32 (ctr +^ 1ul));
    (* let h1 = HST.get() in *)
    (* admitP (forall (i:nat). (i >= w ctr + 1 /\ i < norm_length) ==>  *)
    (*   ((v swap = 0 ==> (v (get h1 a i) = v (get h0 a i)  *)
    (* 	         /\ v (get h1 b i) = v (get h0 b i))) *)
    (*    /\ (v swap = pow2 platform_size - 1 ==> (v (get h1 a i) = v (get h0 b i)  *)
    (* 					       /\ v (get h1 b i) = v (get h0 a i))))); *)
    (* admitP (forall (i:nat). {:pattern (get h1 a i) \/ (get h1 b i)} 0+i = i);  *)
    (* cut (forall (i:nat). {:pattern (get h1 a i)} i < w ctr ==> v (get h1 a i) = v (get h3 a i));  *)
    (* cut (forall (i:nat). {:pattern (get h1 b i)} i < w ctr ==> v (get h1 b i) = v (get h3 b i)); *)
    ()
 end

val swap_conditional_aux: a:bigint -> b:bigint{disjoint a b} ->
  is_swap:s64{v is_swap = pow2 platform_size -1 \/ v is_swap = 0} ->
  Stack unit
    (requires (fun h -> B.live h a /\ B.live h b))
      (* norm h a /\ norm h b)) *)
    (ensures (fun h0 _ h1 -> B.live h1 a /\ B.live h1 b /\ modifies_2 a b h0 h1))
      (* /\ norm h0 a /\ norm h0 b /\ norm h1 a /\ norm h1 b *)
      (* /\ (v is_swap = 0 ==> ((valueOf h1 a = valueOf h0 a) /\ (valueOf h1 b = valueOf h0 b))) *)
      (* /\ (v is_swap = pow2 platform_size - 1 ==>  *)
      (* 	  ((valueOf h1 a = valueOf h0 b) /\ (valueOf h1 b = valueOf h0 a))) )) *)
let rec swap_conditional_aux a b swap =
  (* let h0 = HST.get() in *)
  swap_conditional_aux' a b swap 0ul(* ;  *)
  (* let h1 = HST.get() in  *)
  (* swap_conditional_aux_lemma h0 h1 a b swap   *)

#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 5"

(* For simplicity, assuming that the point coordinates have been allocated on the same frame.
   Ideally in the same buffer *)
type same_frame (p:point) =
  frameOf (get_x p) = frameOf (get_y p) /\ frameOf (get_x p) = frameOf (get_z p)
type same_frame_2 (p:point) (p':point) =
  same_frame p /\ same_frame p' /\ frameOf (get_x p) = frameOf (get_x p')

let frame_of (p:point{same_frame p}) : GTot HH.rid = frameOf (get_x p)

val helper_lemma: #t:Type -> a:buffer t -> b:buffer t -> Lemma
  (requires (True))
  (ensures  (arefs (only a ++ only b) == !{as_ref a, as_ref b}))
let helper_lemma #t a b =
  let s =  only a ++ only b in
  let s' = !{as_ref a, as_ref b} in
  assert(TSet.mem (Buff a) s);
  assert(TSet.mem (Buff b) s);
  TSet.lemma_equal_intro (arefs s) s'

let helper_lemma_2 r h0 h1 (sub:TSet.set Heap.aref) (s:TSet.set Heap.aref) : Lemma
  (requires (TSet.subset sub s /\ modifies_ref r sub h0 h1))
  (ensures  (modifies_ref r s h0 h1))
  = ()

let helper_lemma_3 r h0 h1 h2 s : Lemma
  (requires (HS.modifies_ref r s h0 h1 /\ HS.modifies_ref r s h1 h2))
  (ensures  (HS.modifies_ref r s h0 h2))
  = ()

let prop_1 h0 h1 (a:point) (b:point) : GTot Type0 =
  same_frame_2 a b
  /\ (forall (#t:Type) (b':buffer t). (frameOf b' = frame_of a /\ B.live h0 b'
       /\ disjoint_from_bufs b' (only (get_x a) ++ only (get_y a) ++ only (get_z a)
				    ++ only (get_x b) ++ only (get_y b) ++ only (get_z b) ))
				    ==> equal h0 b' h1 b')

#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 20"

let helper_lemma_4 r h0 h1 h2 h3 a b : Lemma
  (requires ( (forall (#t:Type) (b':buffer t). (frameOf b' = frame_of a /\ B.live h0 b'
      /\ disjoint b' (get_x a) /\ disjoint b' (get_x b))  ==> equal h0 b' h1 b')
    /\ (forall (#t:Type) (b':buffer t). (frameOf b' = frame_of a /\ B.live h1 b'
      /\ disjoint b' (get_y a) /\ disjoint b' (get_y b))  ==> equal h1 b' h2 b')
    /\ (forall (#t:Type) (b':buffer t). (frameOf b' = frame_of a /\ B.live h2 b'
      /\ disjoint b' (get_z a) /\ disjoint b' (get_z b))  ==> equal h2 b' h3 b')
     /\ same_frame_2 a b ))
   (ensures  (prop_1 h0 h3 a b))
  = let s = only (get_x a) ++ only (get_y a) ++ only (get_z a)
	    ++ only (get_x b) ++ only (get_y b) ++ only (get_z b) in
    assert(TSet.mem (Buff (get_x a)) s);
    assert(TSet.mem (Buff (get_y a)) s);
    assert(TSet.mem (Buff (get_z a)) s);
    assert(TSet.mem (Buff (get_x b)) s);
    assert(TSet.mem (Buff (get_y b)) s);
    assert(TSet.mem (Buff (get_z b)) s);
    assert(forall (#t:Type) (b':buffer t). disjoint_from_bufs b' s
	     ==> (disjoint b' (get_x a) /\ disjoint b' (get_x b)));
    assert(forall (#t:Type) (b':buffer t). disjoint_from_bufs b' s
	     ==> (disjoint b' (get_y a) /\ disjoint b' (get_y b)));
    assert(forall (#t:Type) (b':buffer t). disjoint_from_bufs b' s
	     ==> (disjoint b' (get_z a) /\ disjoint b' (get_z b)))

val swap_conditional:
  a:point{same_frame a} -> b:point{distinct a b /\ same_frame b} ->
  is_swap:s64(* {v is_swap = pow2 platform_size -1 \/ v is_swap = 0} *) ->
  Stack unit
    (requires (fun h -> live h a /\ live h b /\ same_frame_2 a b))
      (* onCurve h a /\ onCurve h b)) *)
    (ensures (fun h0 _ h1 -> live h1 a /\ live h1 b
      /\ HS.modifies_one (frame_of a) h0 h1
      /\ HS.modifies_ref (frame_of a) (refs a ++ refs b) h0 h1
      /\ prop_1 h0 h1 a b))
      (* (onCurve h0 a /\ onCurve h0 b) /\ (onCurve h1 a /\ onCurve h1 b) *)
      (* (\* /\ modifies (refs a ++ refs b) h0 h1  *\) *)
      (* /\ (v is_swap = 0 ==>  *)
      (* 	  ((pointOf h1 a) == (pointOf h0 a) /\ (pointOf h1 b) == (pointOf h0 b))) *)
      (* /\ (v is_swap = pow2 platform_size - 1 ==>  *)
      (* 	  ((pointOf h1 a) == (pointOf h0 b) /\ (pointOf h1 b) == (pointOf h0 a))) )) *)
let swap_conditional a b is_swap =
  let h0 = HST.get() in
  swap_conditional_aux (get_x a) (get_x b) is_swap;
  let h1 = HST.get() in
  lemma_reveal_modifies_2 (get_x a) (get_x b) h0 h1;
  (* assert(disjoint (get_x a) (get_y a)); assert(disjoint (get_x b) (get_y a)); *)
  (* no_upd_lemma_2 h0 h1 (get_x a) (get_x b) (get_y a); *)
  cut (live h1 a /\ live h1 b);
  (* norm_lemma h0 h1 (get_y a) !{getRef (get_x a), getRef (get_x b)}; *)
  (* norm_lemma h0 h1 (get_y b) !{getRef (get_x a), getRef (get_x b)}; *)
  swap_conditional_aux (get_y a) (get_y b) is_swap;
  let h2 = HST.get() in
  cut (live h2 a /\ live h2 b);
  lemma_reveal_modifies_2 (get_y a) (get_y b) h1 h2;
  (* let mods = (hide !{getRef (get_x a), getRef (get_x b), getRef (get_y a), getRef (get_y b)}) in *)
  (* cut(modifies (reveal mods) h0 h2);  *)
  (* cut(not(FStar.Set.mem (Ref (getRef (get_z b))) (reveal mods)) /\ not(FStar.Set.mem (Ref (getRef (get_z a))) (reveal mods)));  *)
  (* enorm_lemma h0 h2 (get_z a) mods; *)
  (* enorm_lemma h0 h2 (get_z b) mods; *)
  swap_conditional_aux (get_z a) (get_z b) is_swap;
  let h3 = HST.get() in
  cut (live h3 a /\ live h3 b);
  lemma_reveal_modifies_2 (get_z a) (get_z b) h2 h3;
  assert(HS.modifies_one (frame_of a) h0 h3);
  helper_lemma (get_x a) (get_x b);
  helper_lemma (get_y a) (get_y b);
  helper_lemma (get_z a) (get_z b);
  helper_lemma_2 (frame_of a) h0 h1 (arefs (only (get_x a) ++ only (get_x b))) (refs a ++ refs b);
  helper_lemma_2 (frame_of a) h1 h2 (arefs (only (get_y a) ++ only (get_y b))) (refs a ++ refs b);
  helper_lemma_2 (frame_of a) h2 h3 (arefs (only (get_z a) ++ only (get_z b))) (refs a ++ refs b);
  helper_lemma_3 (frame_of a) h0 h1 h2 (refs a ++ refs b);
  helper_lemma_3 (frame_of a) h0 h2 h3 (refs a ++ refs b);
  helper_lemma_4 (frame_of a) h0 h1 h2 h3 a b;
  assert(HS.modifies_ref (frame_of a) (refs a ++ refs b) h0 h3);
  ()

val helper_lemma': #t:Type -> a:buffer t -> Lemma
  (requires (True))
  (ensures  (arefs (only a) == !{as_ref a}))
let helper_lemma' #t a =
  let s =  only a in
  let s' = !{as_ref a} in
  assert(TSet.mem (Buff a) s);
  TSet.lemma_equal_intro (arefs s) s'

let prop_2 h0 h1 (a:point) : GTot Type0 =
  same_frame a
  /\ (forall (#t:Type) (b':buffer t). (frameOf b' = frame_of a /\ B.live h0 b'
       /\ disjoint_from_bufs b' (only (get_x a) ++ only (get_y a) ++ only (get_z a)))
				    ==> equal h0 b' h1 b')

let helper_lemma_4' r h0 h1 h2 h3 a : Lemma
  (requires ( (forall (#t:Type) (b':buffer t). (frameOf b' = frame_of a /\ B.live h0 b'
      /\ disjoint b' (get_x a))  ==> equal h0 b' h1 b')
    /\ (forall (#t:Type) (b':buffer t). (frameOf b' = frame_of a /\ B.live h1 b'
      /\ disjoint b' (get_y a))  ==> equal h1 b' h2 b')
    /\ (forall (#t:Type) (b':buffer t). (frameOf b' = frame_of a /\ B.live h2 b'
      /\ disjoint b' (get_z a))  ==> equal h2 b' h3 b')
     /\ same_frame a ))
   (ensures  (prop_2 h0 h3 a))
  = let s = only (get_x a) ++ only (get_y a) ++ only (get_z a) in
    assert(TSet.mem (Buff (get_x a)) s);
    assert(TSet.mem (Buff (get_y a)) s);
    assert(TSet.mem (Buff (get_z a)) s);
    assert(forall (#t:Type) (b':buffer t). disjoint_from_bufs b' s
	     ==> (disjoint b' (get_x a)));
    assert(forall (#t:Type) (b':buffer t). disjoint_from_bufs b' s
	     ==> (disjoint b' (get_y a)));
    assert(forall (#t:Type) (b':buffer t). disjoint_from_bufs b' s
	     ==> (disjoint b' (get_z a)))

#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 100"

val copy:
  a:point{same_frame a} -> b:point{distinct a b} ->
  Stack unit
    (requires (fun h -> live h a /\ live h b))
      (* /\ onCurve h b)) *)
    (ensures (fun h0 _ h1 -> live h1 a /\ live h1 b
      /\ HS.modifies_one (frame_of a) h0 h1
      /\ HS.modifies_ref (frame_of a) (refs a) h0 h1
      /\ prop_2 h0 h1 a))
      (* (live h0 a) /\ (onCurve h1 a) /\ (onCurve h0 b) /\ (onCurve h1 b) *)
      (* /\ (pointOf h1 a = pointOf h0 b) /\ (pointOf h1 b = pointOf h0 b) *)
      (* /\ (modifies (refs a) h0 h1) *)
let copy a b =
  let h0 = HST.get() in
  blit (get_x b) 0ul (get_x a) 0ul nlength;
  let h1 = HST.get() in
  cut (live h1 a /\ live h1 b);
  lemma_reveal_modifies_1 (get_x a) h0 h1;
  (* norm_lemma h0 h1 (get_x b) (!{getRef (get_x a)});  *)
  (* norm_lemma h0 h1 (get_y b) (!{getRef (get_x a)});  *)
  (* norm_lemma h0 h1 (get_z b) (!{getRef (get_x a)});  *)
  (* bignum_live_lemma h0 h1 (get_y a) (!{getRef (get_x a)});  *)
  (* bignum_live_lemma h0 h1 (get_z a) (!{getRef (get_x a)});  *)
  blit (get_y b) 0ul (get_y a) 0ul nlength;
  let h2 = HST.get() in
  cut (live h2 a /\ live h2 b);
  lemma_reveal_modifies_1 (get_y a) h1 h2;
  (* norm_lemma h1 h2 (get_x b) (!{getRef (get_y a)});  *)
  (* norm_lemma h1 h2 (get_y b) (!{getRef (get_y a)}); *)
  (* norm_lemma h1 h2 (get_z b) (!{getRef (get_y a)});  *)
  (* norm_lemma_2 h0 h1 (get_x b) (get_x a);  *)
  (* norm_lemma h1 h2 (get_x a) (!{getRef (get_y a)});  *)
  (* bignum_live_lemma h1 h2 (get_z a) (!{getRef (get_y a)}); *)
  blit (get_z b) 0ul (get_z a) 0ul nlength;
  let h3 = HST.get() in
  cut (live h2 a /\ live h2 b);
  lemma_reveal_modifies_1 (get_z a) h2 h3;
  (* norm_lemma h2 h3 (get_x b) (!{getRef (get_z a)}); *)
  (* norm_lemma h2 h3 (get_y b) (!{getRef (get_z a)}); *)
  (* norm_lemma h2 h3 (get_z b) (!{getRef (get_z a)}); *)
  (* norm_lemma h2 h3 (get_x a) (!{getRef (get_z a)}); *)
  (* norm_lemma_2 h1 h2 (get_y b) (get_y a);  *)
  (* norm_lemma h2 h3 (get_y a) (!{getRef (get_z a)});  *)
  (* norm_lemma_2 h2 h3 (get_z b) (get_z a) *)
  helper_lemma' (get_x a);
  helper_lemma' (get_y a);
  helper_lemma' (get_z a);
  helper_lemma_2 (frame_of a) h0 h1 (arefs (only (get_x a))) (refs a);
  helper_lemma_2 (frame_of a) h1 h2 (arefs (only (get_y a))) (refs a);
  helper_lemma_2 (frame_of a) h2 h3 (arefs (only (get_z a))) (refs a);
  helper_lemma_3 (frame_of a) h0 h1 h2 (refs a);
  helper_lemma_3 (frame_of a) h0 h2 h3 (refs a);
  helper_lemma_4' (frame_of a) h0 h1 h2 h3 a;
  assert(HS.modifies_ref (frame_of a) (refs a) h0 h3);
  ()

#reset-options "--initial_fuel 0 --max_fuel 0"

val swap:
  a:point -> b:point{distinct a b /\ same_frame b} ->
  Stack unit
    (requires (fun h -> live h a /\ live h b))
      (* onCurve h a /\ live h b)) *)
    (ensures (fun h0 _ h1 -> live h1 b /\ live h1 a
      /\ HS.modifies_one (frame_of b) h0 h1
      /\ HS.modifies_ref (frame_of b) (refs b) h0 h1
      /\ prop_2 h0 h1 b ))
      (* onCurve h0 a /\ live h0 b /\ onCurve h1 b /\ live h1 a *)
      (* /\ (pointOf h0 a) == (pointOf h1 b) *)
      (* (\* /\ modifies (FStar.Set.union (refs a) (refs b)) h0 h1)) *\) *)
let swap a b =
  copy b a

val helper_lemma_5: h0:mem -> h1:mem -> a:point -> b:point -> Lemma
  (requires (prop_2 h0 h1 a /\ distinct a b /\ live h0 b /\ same_frame_2 a b))
  (ensures  (live h1 b))
let helper_lemma_5 h0 h1 a b =
  let x = get_x b in
  let y = get_y b in
  let z = get_z b in
  let s = (only (get_x a) ++ only (get_y a) ++ only (get_z a)) in
  assert(disjoint_from_bufs x s);
  assert(disjoint_from_bufs y s);
  assert(disjoint_from_bufs z s)

#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 100"

val swap_both:
  a:point -> b:point{distinct a b /\ same_frame_2 a b} ->
  c:point{distinct c a /\ distinct c b /\ same_frame_2 b c} ->
  d:point{distinct d a /\ distinct d b /\ distinct d c /\ same_frame_2 c d} -> Stack unit
    (requires (fun h -> live h a /\ live h b /\ live h c /\ live h d))
      (* onCurve h a /\ onCurve h b /\ live h c /\ live h d)) *)
    (ensures (fun h0 _ h1 -> live h1 a /\ live h1 b /\ live h1 c /\ live h1 d
      /\ HS.modifies_one (frame_of a) h0 h1
      /\ HS.modifies_ref (frame_of a) (refs a ++ refs b ++ refs c ++ refs d) h0 h1 ))
      (* onCurve h0 a /\ onCurve h0 b /\ live h0 c /\ live h0 d *)
      (* /\ onCurve h1 c /\ onCurve h1 d /\ live h1 a /\ live h1 b *)
      (* /\ (pointOf h0 a) == (pointOf h1 c) /\ (pointOf h0 b) == (pointOf h1 d) *)
let swap_both a b c d =
  (* admit(); // OK *)
  let h0 = HST.get() in
  copy c a;
  let h1 = HST.get() in
  helper_lemma_5 h0 h1 c a;
  helper_lemma_5 h0 h1 c b;
  helper_lemma_5 h0 h1 c d;
  (* let set01 = erefs c in  *)
  (* distinct_lemma c b;  *)
  (* distinct_lemma c d;  *)
  (* on_curve_lemma h0 h1 b set01;  *)
  (* live_lemma h0 h1 d set01;  *)
  copy d b;
  let h2 = HST.get() in
  helper_lemma_5 h1 h2 d a;
  helper_lemma_5 h1 h2 d b;
  helper_lemma_5 h1 h2 d c;
  (* distinct_lemma d c;  *)
  (* distinct_lemma d a; *)
  (* distinct_lemma d b; *)
  (* on_curve_lemma h1 h2 c (erefs d); *)
  (* live_lemma h1 h2 a (erefs d); *)
  (* live_lemma h1 h2 b (erefs d) *)
  helper_lemma_2 (frame_of a) h0 h1 (refs c) (refs a ++ refs b ++ refs c ++ refs d);
  helper_lemma_2 (frame_of a) h1 h2 (refs d) (refs a ++ refs b ++ refs c ++ refs d);
  helper_lemma_3 (frame_of a) h0 h1 h2 (refs a ++ refs b ++ refs c ++ refs d);
  ()

#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 100"

val copy2: p':point -> q':point{distinct p' q' /\ same_frame_2 p' q'} ->
  p:point{distinct p p' /\ distinct p q' /\ same_frame_2 p q'} ->
  q:point{distinct q p' /\ distinct q q' /\ same_frame_2 p q} -> Stack unit
    (requires (fun h -> live h p' /\ live h q' /\ live h p /\ live h q))
      (* live h p' /\ live h q' /\ onCurve h p /\ onCurve h q )) *)
    (ensures (fun h0 _ h1 -> live h1 p' /\ live h1 q' /\ live h1 p /\ live h1 q
      /\ HS.modifies_one (frame_of p) h0 h1
      /\ HS.modifies_ref (frame_of p) (refs p' ++ refs q') h0 h1 ))
      (* onCurve h1 p' /\ onCurve h1 q' /\ onCurve h1 p /\ onCurve h1 q  *)
      (* /\ onCurve h0 p /\ onCurve h0 q *)
      (* (\* /\ (modifies (FStar.Set.union (refs p') (refs q')) h0 h1) *\) *)
      (* /\ (pointOf h1 p' == pointOf h0 p) *)
      (* /\ (pointOf h1 q' == pointOf h0 q) )) *)
let copy2 p' q' p q =
  (* admit(); // OK *)
  let h0 = HST.get() in
  copy p' p;
  let h1 = HST.get() in
  helper_lemma_5 h0 h1 p' q';
  helper_lemma_5 h0 h1 p' p;
  helper_lemma_5 h0 h1 p' q;
  (* let set01 = (erefs p') in  *)
  (* distinct_lemma p' q;  *)
  (* distinct_lemma p' q';  *)
  (* on_curve_lemma h0 h1 q set01;  *)
  (* live_lemma h0 h1 q' set01;   *)
  copy q' q;
  let h2 = HST.get() in
  helper_lemma_5 h1 h2 q' p';
  helper_lemma_5 h1 h2 q' p;
  helper_lemma_5 h1 h2 q' q;
  (* distinct_lemma q' p';  *)
  (* distinct_lemma q' p; *)
  (* distinct_lemma q' q;  *)
  (* on_curve_lemma h1 h2 p' (erefs q');  *)
  (* on_curve_lemma h1 h2 p (erefs q');  *)
  (* on_curve_lemma h1 h2 q (erefs q') *)
  helper_lemma_2 (frame_of p) h0 h1 (refs p') (refs p' ++ refs q');
  helper_lemma_2 (frame_of p) h1 h2 (refs q') (refs p' ++ refs q');
  helper_lemma_3 (frame_of p) h0 h1 h2 (refs p' ++ refs q');
  ()

#reset-options "--initial_fuel 0 --max_fuel 0"
