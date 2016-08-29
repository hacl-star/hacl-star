module Hacl.EC.Curve25519.Point

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

let op_Plus_Plus_Plus = TSet.union

let refs p = TSet.singleton (Buff (get_x p)) +++ TSet.singleton (Buff (get_y p)) +++ TSet.singleton (Buff (get_z p))

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
  (* admit(); // TODO *)
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
  STStack unit
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

#reset-options "--lax"

(* TODO: lift from the modifies_2 to the modifies_bufs_and_refs *)
val swap_conditional:
  a:point -> b:point{distinct a b} ->
  is_swap:s64{v is_swap = pow2 platform_size -1 \/ v is_swap = 0} ->
  STStack unit
    (requires (fun h -> live h a /\ live h b))
      (* onCurve h a /\ onCurve h b)) *)
    (ensures (fun h0 _ h1 -> live h1 a /\ live h1 b
      /\ modifies_bufs_and_refs (refs a +++ refs b) TSet.empty h0 h1))
      (* (onCurve h0 a /\ onCurve h0 b) /\ (onCurve h1 a /\ onCurve h1 b) *)
      (* (\* /\ modifies (refs a +++ refs b) h0 h1  *\) *)
      (* /\ (v is_swap = 0 ==>  *)
      (* 	  ((pointOf h1 a) == (pointOf h0 a) /\ (pointOf h1 b) == (pointOf h0 b))) *)
      (* /\ (v is_swap = pow2 platform_size - 1 ==>  *)
      (* 	  ((pointOf h1 a) == (pointOf h0 b) /\ (pointOf h1 b) == (pointOf h0 a))) )) *)
let swap_conditional a b is_swap =
  (* let h0 = HST.get() in *)
  swap_conditional_aux (get_x a) (get_x b) is_swap;
  (* let h1 = HST.get() in *)
  (* norm_lemma h0 h1 (get_y a) !{getRef (get_x a), getRef (get_x b)}; *)
  (* norm_lemma h0 h1 (get_y b) !{getRef (get_x a), getRef (get_x b)}; *)
  swap_conditional_aux (get_y a) (get_y b) is_swap;
  (* let h2 = HST.get() in *)
  (* let mods = (hide !{getRef (get_x a), getRef (get_x b), getRef (get_y a), getRef (get_y b)}) in *)
  (* cut(modifies (reveal mods) h0 h2);  *)
  (* cut(not(FStar.Set.mem (Ref (getRef (get_z b))) (reveal mods)) /\ not(FStar.Set.mem (Ref (getRef (get_z a))) (reveal mods)));  *)
  (* enorm_lemma h0 h2 (get_z a) mods; *)
  (* enorm_lemma h0 h2 (get_z b) mods; *)
  swap_conditional_aux (get_z a) (get_z b) is_swap(* ; *)
  (* let h3 = HST.get() in *)
  (* swap_conditional_lemma h0 h1 h2 h3 a b is_swap *)

val copy:
  a:point -> b:point{distinct a b} ->
  STStack unit
    (requires (fun h -> live h a /\ live h b))
      (* /\ onCurve h b)) *)
    (ensures (fun h0 _ h1 -> live h1 a /\ modifies_bufs_and_refs (refs a) TSet.empty h0 h1
      (* (live h0 a) /\ (onCurve h1 a) /\ (onCurve h0 b) /\ (onCurve h1 b) *)
      (* /\ (pointOf h1 a = pointOf h0 b) /\ (pointOf h1 b = pointOf h0 b) *)
      (* /\ (modifies (refs a) h0 h1) *)
      ))
let copy a b =
  (* admit(); // TODO *)
  (* let h0 = HST.get() in *)
  blit (get_x b) 0ul (get_x a) 0ul nlength;
  (* let h1 = HST.get() in  *)
  (* norm_lemma h0 h1 (get_x b) (!{getRef (get_x a)});  *)
  (* norm_lemma h0 h1 (get_y b) (!{getRef (get_x a)});  *)
  (* norm_lemma h0 h1 (get_z b) (!{getRef (get_x a)});  *)
  (* bignum_live_lemma h0 h1 (get_y a) (!{getRef (get_x a)});  *)
  (* bignum_live_lemma h0 h1 (get_z a) (!{getRef (get_x a)});  *)
  blit (get_y b) 0ul (get_y a) 0ul nlength;
  (* let h2 = HST.get() in *)
  (* norm_lemma h1 h2 (get_x b) (!{getRef (get_y a)});  *)
  (* norm_lemma h1 h2 (get_y b) (!{getRef (get_y a)}); *)
  (* norm_lemma h1 h2 (get_z b) (!{getRef (get_y a)});  *)
  (* norm_lemma_2 h0 h1 (get_x b) (get_x a);  *)
  (* norm_lemma h1 h2 (get_x a) (!{getRef (get_y a)});  *)
  (* bignum_live_lemma h1 h2 (get_z a) (!{getRef (get_y a)}); *)
  blit (get_z b) 0ul (get_z a) 0ul nlength;
  (* let h3 = HST.get() in *)
  (* norm_lemma h2 h3 (get_x b) (!{getRef (get_z a)}); *)
  (* norm_lemma h2 h3 (get_y b) (!{getRef (get_z a)}); *)
  (* norm_lemma h2 h3 (get_z b) (!{getRef (get_z a)}); *)
  (* norm_lemma h2 h3 (get_x a) (!{getRef (get_z a)}); *)
  (* norm_lemma_2 h1 h2 (get_y b) (get_y a);  *)
  (* norm_lemma h2 h3 (get_y a) (!{getRef (get_z a)});  *)
  (* norm_lemma_2 h2 h3 (get_z b) (get_z a) *)
  ()

#reset-options "--initial_fuel 0 --max_fuel 0"

val swap:
  a:point -> b:point{distinct a b} ->
  STStack unit
    (requires (fun h -> live h a /\ live h b))
      (* onCurve h a /\ live h b)) *)
    (ensures (fun h0 _ h1 -> live h1 b /\ modifies_bufs_and_refs (refs b) TSet.empty h0 h1
      (* onCurve h0 a /\ live h0 b /\ onCurve h1 b /\ live h1 a *)
      (* /\ (pointOf h0 a) == (pointOf h1 b) *)
      (* (\* /\ modifies (FStar.Set.union (refs a) (refs b)) h0 h1)) *\) *)
      ))
let swap a b =
  copy b a

(* TODO *)
#reset-options "--lax"

val swap_both:
  a:point -> b:point{distinct a b} -> c:point{distinct c a /\ distinct c b} ->
  d:point{distinct d a /\ distinct d b /\ distinct d c} ->
  STStack unit
    (requires (fun h -> live h a /\ live h b /\ live h c /\ live h d))
      (* onCurve h a /\ onCurve h b /\ live h c /\ live h d)) *)
    (ensures (fun h0 _ h1 -> live h1 a /\ live h1 b /\ live h1 c /\ live h1 d
      /\ modifies_bufs_and_refs ((refs a) +++ (refs b) +++ (refs c) +++ (refs d)) TSet.empty h0 h1
      (* onCurve h0 a /\ onCurve h0 b /\ live h0 c /\ live h0 d *)
      (* /\ onCurve h1 c /\ onCurve h1 d /\ live h1 a /\ live h1 b *)
      (* /\ (pointOf h0 a) == (pointOf h1 c) /\ (pointOf h0 b) == (pointOf h1 d) *)
    ))
let swap_both a b c d =
  (* admit(); // OK *)
  (* let h0 = HST.get() in *)
  copy c a;
  (* let h1 = HST.get() in *)
  (* let set01 = erefs c in  *)
  (* distinct_lemma c b;  *)
  (* distinct_lemma c d;  *)
  (* on_curve_lemma h0 h1 b set01;  *)
  (* live_lemma h0 h1 d set01;  *)
  copy d b;
  (* let h2 = HST.get() in *)
  (* distinct_lemma d c;  *)
  (* distinct_lemma d a; *)
  (* distinct_lemma d b; *)
  (* on_curve_lemma h1 h2 c (erefs d); *)
  (* live_lemma h1 h2 a (erefs d); *)
  (* live_lemma h1 h2 b (erefs d) *)
  ()

val copy2: p':point -> q':point{distinct p' q'} -> p:point{distinct p p' /\ distinct p q'} ->
  q:point{distinct q p' /\ distinct q q'} -> STStack unit
    (requires (fun h -> live h p' /\ live h q' /\ live h p /\ live h q))
      (* live h p' /\ live h q' /\ onCurve h p /\ onCurve h q )) *)
    (ensures (fun h0 _ h1 -> live h1 p' /\ live h1 q' /\ modifies_bufs_and_refs (refs p' +++ refs q') TSet.empty h0 h1))
      (* onCurve h1 p' /\ onCurve h1 q' /\ onCurve h1 p /\ onCurve h1 q  *)
      (* /\ onCurve h0 p /\ onCurve h0 q *)
      (* (\* /\ (modifies (FStar.Set.union (refs p') (refs q')) h0 h1) *\) *)
      (* /\ (pointOf h1 p' == pointOf h0 p) *)
      (* /\ (pointOf h1 q' == pointOf h0 q) )) *)
let copy2 p' q' p q =
  (* admit(); // OK *)
  (* let h0 = HST.get() in *)
  copy p' p;
  (* let h1 = HST.get() in *)
  (* let set01 = (erefs p') in  *)
  (* distinct_lemma p' q;  *)
  (* distinct_lemma p' q';  *)
  (* on_curve_lemma h0 h1 q set01;  *)
  (* live_lemma h0 h1 q' set01;   *)
  copy q' q;
  (* let h2 = HST.get() in *)
  (* distinct_lemma q' p';  *)
  (* distinct_lemma q' p; *)
  (* distinct_lemma q' q;  *)
  (* on_curve_lemma h1 h2 p' (erefs q');  *)
  (* on_curve_lemma h1 h2 p (erefs q');  *)
  (* on_curve_lemma h1 h2 q (erefs q') *)
  ()

#reset-options "--initial_fuel 0 --max_fuel 0"
