module Hacl.EC.Curve25519.Ladder

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

// Will be specified using the bitwise operators' semantics
val mk_mask: x:s8 -> Tot (y:s64(* {v y < pow2 platform_size /\ (Hacl.UInt8.v x = 0 ==> v y = 0) /\ (Hacl.UInt8.v x = 1 ==> v y = pow2 platform_size - 1)} *))
let mk_mask x =
  (* admit(); // OK *)
  let y = Hacl.Cast.sint8_to_sint64 x in
  H64 (Hacl.Cast.uint64_to_sint64 0uL -%^ y)

val nth_bit: byt:s8 -> idx:u32{U32.v idx < 8} -> Tot (b:s8(* {S8.logand (S8.shift_right byt (7ul-|idx)) (uint8_to_sint8 1uy) == b /\ (b == uint8_to_sint8 0uy \/ b == uint8_to_sint8 1uy) } *))
let nth_bit byte idx =
  let open Hacl.UInt8 in
  let bit = (byte >>^ (U32 (7ul -^ idx))) &^ (Hacl.Cast.uint8_to_sint8 1uy) in
  (* and_one_lemma (S8.shift_right byte (7-idx)); *)
  bit

type distinct2 (n:bytes) (p:point) =
  disjoint n (get_x p) /\ disjoint n (get_y p) /\ disjoint n (get_z p)

(* TODO *)
#reset-options "--lax"

val small_step_exit: 
  two_p:point -> two_p_plus_q:point{distinct two_p two_p_plus_q} -> 
  p:point{distinct p two_p /\ distinct p two_p_plus_q} -> 
  p_plus_q:point{distinct p_plus_q two_p /\ distinct p_plus_q two_p_plus_q /\ distinct p_plus_q p} -> 
  q:point{distinct q two_p /\ distinct q two_p_plus_q /\ distinct q p /\ distinct q p_plus_q} -> 
  n:erased nat -> byte:s8 ->
  scalar:erased nat(* {reveal n = reveal scalar * (pow2 8) + (S8.v byte / (pow2 (8-8)))} *) ->
  Stack unit
     (requires (fun h -> live h two_p /\ live h two_p_plus_q /\ live h p /\ live h q /\ live h p_plus_q
       (* (live h two_p) /\ (live h two_p_plus_q) /\ (onCurve h p) /\ (onCurve h p_plus_q) /\ (onCurve h q) *)
       (* /\ (nTimesQ n (pointOf h q) h p p_plus_q)  *)
     ))
     (ensures (fun h0 _ h1 -> live h1 two_p /\ live h1 two_p_plus_q /\ live h1 p /\ live h1 p_plus_q
       /\ HS.modifies_one (frame_of p) h0 h1
       /\ HS.modifies_ref (frame_of p) (refs two_p ++ refs two_p_plus_q ++ refs p ++ refs p_plus_q) h0 h1 ))
       (* (onCurve h0 p) /\ (onCurve h0 p_plus_q) /\ (onCurve h0 q) *)
       (* /\ (onCurve h1 two_p) /\ (onCurve h1 two_p_plus_q) /\ (live h1 p) /\ (live h1 p_plus_q) /\ (onCurve h1 q)  *)
       (* /\ (modifies (refs two_p +++ refs two_p_plus_q +++ refs p +++ refs p_plus_q) h0 h1) *)
       // Formula_0 replaces (scalar * pow2 8 + byte)
       (* /\ (nTimesQ  (formula_0 scalar byte) (pointOf h0 q) h1 two_p two_p_plus_q) *)
let small_step_exit pp ppq p pq q n byte scalar =
  (* admit(); // OK *)
  (* let h0 = HST.get() in *)
  Hacl.EC.Curve25519.PPoint.copy2 pp ppq p pq;
  (* let h1 = HST.get() in *)
  (* distinct_lemma q p; distinct_lemma q pq; distinct_lemma q pp; distinct_lemma q ppq; *)
  (* let s = (erefs pp +*+ erefs ppq +*+ erefs p +*+ erefs pq) in *)
  (* cut(modifies (reveal s) h0 h1); *)
  (* admitP(True /\ FStar.TSet.intersect (reveal s) (refs q) = !{}); *)
  (* on_curve_lemma h0 h1 q (erefs pp +*+ erefs ppq +*+ erefs p +*+ erefs pq); *)
  (* cut(onCurve h1 q);  *)
  (* cut(nTimesQ (hide (reveal scalar * pow2 8 + (S8.v byte / pow2 (8-8)))) (pointOf h0 q) h0 p pq);  *)
  ()
  (* helper_lemma_1 scalar byte *)

val small_step_core: 
   two_p:point -> two_p_plus_q:point{distinct two_p two_p_plus_q} -> 
   p:point{distinct p two_p /\ distinct p two_p_plus_q} -> 
   p_plus_q:point{distinct p_plus_q two_p /\ distinct p_plus_q two_p_plus_q /\ distinct p_plus_q p} -> 
   q:point{distinct q two_p /\ distinct q two_p_plus_q /\ distinct q p /\ distinct q p_plus_q} -> 
   n:erased nat -> ctr:u32{U32.v ctr<8} -> byt:s8 -> scalar:erased nat(* {reveal n = reveal scalar * (pow2 (w ctr)) + (S8.v byt / (pow2 (8-w ctr)))} *) -> 
   Stack unit
     (requires (fun h -> live h two_p /\ live h two_p_plus_q /\ live h p /\ live h q /\ live h p_plus_q))
     (ensures (fun h0 _ h1 -> live h1 two_p /\ live h1 two_p_plus_q /\ live h1 p /\ live h1 p_plus_q
       /\ HS.modifies_one (frame_of p) h0 h1
       /\ HS.modifies_ref (frame_of p) (refs two_p ++ refs two_p_plus_q ++ refs p ++ refs p_plus_q) h0 h1 ))
     (* (requires (fun h ->  *)
     (*   (live h two_p) /\ (live h two_p_plus_q) /\ (onCurve h p) /\ (onCurve h p_plus_q) /\ (onCurve h q) *)
     (*   /\ (nTimesQ n (pointOf h q) h p p_plus_q)  *)
     (* )) *)
     (* (ensures (fun h0 _ h1 -> *)
     (*   (onCurve h0 p) /\ (onCurve h0 p_plus_q) /\ (onCurve h0 q) *)
     (*   /\ (onCurve h1 two_p) /\ (onCurve h1 two_p_plus_q) /\ (live h1 p) /\ (live h1 p_plus_q) /\ (onCurve h1 q)  *)
     (*   (\* /\ (modifies (refs two_p +++ refs two_p_plus_q +++ refs p +++ refs p_plus_q) h0 h1) *\) *)
     (*   // Formula_0 replaces (scalar * pow2 8 + byte) *)
     (*   /\ (nTimesQ  (formula_2 (reveal n) (nth_bit byt ctr)) (pointOf h0 q) h1 two_p two_p_plus_q) *)
     (* )) *)
let small_step_core pp ppq p pq q n ctr b scalar =
  (* admit(); // TODO *)
  (* let h0 = HST.get() in *)
  (* distinct_commutative p pq; *)
  let bit = nth_bit b ctr in
  let mask = mk_mask bit in
  (* cut (v mask = pow2 platform_size - 1 \/ v mask = 0);  *)
  swap_conditional p pq mask; 
  (* let h = HST.get() in *)
  (* small_step_core_lemma_1 h0 h pp ppq p pq q; *)
  Hacl.EC.Curve25519.AddAndDouble.double_and_add pp ppq p pq q;
  (* let h2 = HST.get() in *)
  swap_conditional pp ppq mask; 
  (* lemma_5 scalar b ctr; *)
  (* let h1 = HST.get() in *)
  (* assert ((live h2 p) /\ (live h2 pq) /\ (onCurve h2 q));  *)
  (* assert (onCurve h1 pp /\ onCurve h1 ppq);  *)
  (* let set2 = (erefs pp +*+ erefs ppq +*+ erefs p +*+ erefs pq) in *)
  (* let set21 = (erefs pp +*+ erefs ppq) in *)
  (* assert(modifies (reveal set21) h2 h1);  *)
  (* small_step_core_lemma_1 h2 h1 p pq pp ppq q;  *)
  (* small_step_core_lemma_2 h0 h h2 h1 pp ppq p pq q;  *)
  (* cut ( bit == uint8_to_sint8 0uy ==> ((pointOf h p) = (pointOf h0 p) /\ (pointOf h pq) = (pointOf h0 pq)) ); *)
  (* cut ( bit == uint8_to_sint8 1uy ==> ((pointOf h pq) = (pointOf h0 p) /\ (pointOf h p) = (pointOf h0 pq)) ); *)
  (* cut ( ((pointOf h2 pp) = (Math.Curve.add (pointOf h p) (pointOf h p)) /\ (pointOf h2 ppq) = (Math.Curve.add (pointOf h p) (pointOf h pq))) ); *)
  (* cut (bit == uint8_to_sint8 0uy ==> ((pointOf h1 pp) = (pointOf h2 pp) /\ (pointOf h1 ppq) = (pointOf h2 ppq))); *)
  (* cut (bit == uint8_to_sint8 1uy ==> ((pointOf h1 pp) = (pointOf h2 ppq) /\ (pointOf h1 ppq) = (pointOf h2 pp)));  *)
  (* cut (nTimesQ n (pointOf h0 q) h0 p pq);  *)
  (* small_step_core_lemma_3 h0 h h2 h1 pp ppq p pq q n ctr b scalar *)
  ()

val small_step: two_p:point -> two_p_plus_q:point{distinct two_p two_p_plus_q} ->
   p:point{distinct p two_p /\ distinct p two_p_plus_q} ->
   p_plus_q:point{distinct p_plus_q two_p /\ distinct p_plus_q two_p_plus_q /\ distinct p_plus_q p} ->
   q:point{distinct q two_p /\ distinct q two_p_plus_q /\ distinct q p /\ distinct q p_plus_q} ->
   n:erased nat -> ctr:u32{U32.v ctr<=8} -> b:s8 ->
   scalar:erased nat(* {reveal n = reveal scalar * (pow2 (w ctr)) + (S8.v b / (pow2 (8-w ctr)))} *) -> Stack unit
     (requires (fun h -> live h two_p /\ live h two_p_plus_q /\ live h p /\ live h q /\ live h p_plus_q))
     (ensures (fun h0 _ h1 -> live h1 two_p /\ live h1 two_p_plus_q /\ live h1 p /\ live h1 p_plus_q
       /\ HS.modifies_one (frame_of p) h0 h1
       /\ HS.modifies_ref (frame_of p) (refs two_p ++ refs two_p_plus_q ++ refs p ++ refs p_plus_q) h0 h1 ))
     (* (requires (fun h -> live h two_p /\ live h two_p_plus_q /\ onCurve h p /\ onCurve h p_plus_q *)
     (*   /\ onCurve h q /\ nTimesQ n (pointOf h q) h p p_plus_q )) *)
     (* (ensures (fun h0 _ h1 -> onCurve h0 p /\ onCurve h0 p_plus_q /\ onCurve h0 q *)
     (*   /\ (live h1 two_p) /\ (live h1 two_p_plus_q) /\ (onCurve h1 p) /\ (onCurve h1 p_plus_q) /\ (onCurve h1 q) *)
     (*   (\* /\ (modifies (refs two_p +++ refs two_p_plus_q +++ refs p +++ refs p_plus_q) h0 h1) *\) *)
     (*   // Formula_0 replaces (scalar * pow2 8 + b) *)
     (*   /\ (nTimesQ  (formula_0 scalar b) (pointOf h0 q) h1 p p_plus_q) *)
     (* )) *)
let rec small_step pp ppq p pq q n ctr b scalar =
  (* admit(); // OK *)
  if U32 (8ul =^ ctr) then begin
    (* lemma_9 ctr; *)
    (* helper_lemma_1 n b;  *)
    ()
  end
  else begin
    (* let h0 = HST.get() in *)
    (* lemma_0 ctr 8; *)
    small_step_core pp ppq p pq q n ctr b scalar;
    (* let h1 = HST.get() in *)
    let bit = nth_bit b ctr in
    (* cut (nTimesQ (formula_1 n bit) (pointOf h0 q) h1 pp ppq); *)
    (* lemma_10 scalar ctr b; *)
    // Replaces a missing definition of the euclidian division
    (* admitP (True /\ 2*reveal n+S8.v bit = reveal scalar * (pow2 (w ctr+1)) + (S8.v b / pow2 (8 - (w ctr+1)))); *)
    (* cut (w ctr+1 <= 8 /\ True); *)
    (* assert (onCurve h1 pp /\ onCurve h1 ppq /\ live h1 p /\ live h1 pq); *)
    swap_both pp ppq p pq;
    (* let h2 = HST.get() in *)
    (* assert (Math.Curve.equal (pointOf h2 p) (pointOf h1 pp) /\ Math.Curve.equal (pointOf h2 pq) (pointOf h1 ppq)); *)
    (* small_step_lemma_1 h0 h1 h2 pp ppq p pq q; *)
    (* formula_lemma n bit;  *)
    (* assert(nTimesQ (eformula_2 n bit) (pointOf h2 q) h2 p pq); *)
    small_step pp ppq p pq q (hide 0(* eformula_2 n bit *)) (U32 (ctr+^1ul)) b scalar
    (* let h3 = HST.get() in *)
    (* small_step_lemma_2 h0 h1 h2 h3 pp ppq p pq q *)
  end

val big_step:
  n:bytes -> pp:point{distinct2 n pp} -> ppq:point{distinct2 n ppq /\ distinct pp ppq} ->
   p:point{distinct2 n p /\ distinct p pp /\ distinct p ppq} ->
   pq:point{distinct2 n pq /\ distinct pq pp /\ distinct pq ppq /\ distinct pq p} ->
   q:point{distinct2 n q /\ distinct q pp /\ distinct q ppq /\ distinct q p /\ distinct q pq} ->
   ctr:u32{U32.v ctr<=bytes_length} -> STL unit
     (requires (fun h -> live h pp /\ live h ppq /\ live h p /\ live h q /\ live h pq))
     (ensures (fun h0 _ h1 -> live h1 pp /\ live h1 ppq /\ live h1 p /\ live h1 pq
       /\ HS.modifies_one (frame_of p) h0 h1
       /\ HS.modifies_ref (frame_of p) (refs pp ++ refs ppq ++ refs p ++ refs pq) h0 h1 ))
    (* (requires (fun h -> live h pp /\ live h ppq /\ onCurve h p /\ onCurve h pq /\ onCurve h q *)
    (*   /\ nTimesQ (formula_4 h n (w ctr)) (pointOf h q) h p pq )) *)
    (* (ensures (fun h0 _ h1 -> live h0 pp /\ live h0 ppq /\ onCurve h0 p /\ onCurve h0 pq /\ onCurve h0 q *)
    (*   /\ onCurve h1 p /\ onCurve h1 pq *)
    (*   (\* /\ (modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h0 h1) *\) *)
    (*   /\ nTimesQ (formula_4 h0 n (w ctr)) (pointOf h0 q) h0 p pq *)
    (*   /\ nTimesQ (hide (valueOfBytes h0 n)) (pointOf h0 q) h1 p pq  )) *)
let rec big_step n pp ppq p pq q ctr =
  (* admit(); // OK modulo *)
  (* let h0 = HST.get() in *)
  if U32 (blength =^ ctr) then () (* assume(reveal (formula_4 h0 n bytes_length) = valueOfBytes h0 n) *)
  else begin
    (* assume(bytes_length-1-w ctr>=0 /\ bytes_length-w ctr-1>=0); *)
    let byte = index n (U32 (blength-^1ul-^ctr)) in
    (* let m = formula_4 h0 n (w ctr) in *)
    // Replaces missing euclidian definitions in F*
    (* admitP(reveal m = reveal m * pow2 0 + (S8.v byte / pow2 (8-0)) /\ True); *)
    small_step pp ppq p pq q (hide 0)(* m *) 0ul byte (hide 0)(* m *);
    (* let h1 = HST.get() in *)
    (* big_step_lemma_1 h0 h1 n pp ppq p pq q ctr byte; *)
    big_step n pp ppq p pq q (U32 (ctr +^ 1ul))
    (* let h2 = HST.get() in *)
    (* big_step_lemma_2 h0 h1 h2 n pp ppq p pq q (w ctr) byte *)
  end

val montgomery_ladder:
  res:point -> n:bytes{distinct2 n res} -> q:point{distinct2 n q /\ distinct res q} ->
  Stack unit
    (requires (fun h -> live h res /\ live h q))
      (* live h res /\ onCurve h q )) *)
    (ensures (fun h0 _ h1 -> live h1 res
      /\ modifies_3 (get_x res) (get_y res) (get_z res) h0 h1))
    (* live h0 res /\ onCurve h0 q /\ onCurve h1 res *)
    (*   (\* /\ (modifies (refs res) h0 h1)  *\) *)
    (*   /\ (pointOf h1 res = (valueOfBytes h0 n +* (pointOf h0 q)))  )) *)
let montgomery_ladder res n q =
  push_frame();
  // Build 'storage' empty but 'live' points
  let nlp1 = U32 (nlength +^ 1ul) in
  let two_p_x = create (Hacl.Cast.uint64_to_sint64 0uL) nlp1 in
  let two_p_y = create (Hacl.Cast.uint64_to_sint64 0uL) nlength in
  let two_p_z = create (Hacl.Cast.uint64_to_sint64 0uL) nlp1 in
  let two_p =  make two_p_x two_p_y two_p_z in
  (* cut(distinct two_p q); *)
  let two_p_plus_q_x = create (Hacl.Cast.uint64_to_sint64 0uL) nlp1 in
  let two_p_plus_q_y = create (Hacl.Cast.uint64_to_sint64 0uL) nlength in
  let two_p_plus_q_z = create (Hacl.Cast.uint64_to_sint64 0uL) nlp1 in
  let two_p_plus_q = make two_p_plus_q_x two_p_plus_q_y two_p_plus_q_z in
  (* cut(distinct two_p_plus_q two_p /\ distinct two_p_plus_q q); *)
  // Copy of the 'q' point
  let p_x = create (Hacl.Cast.uint64_to_sint64 0uL) nlength in
  blit (get_x q) 0ul p_x 0ul nlength;
  let p_y = create (Hacl.Cast.uint64_to_sint64 0uL) nlength in
  blit (get_y q) 0ul p_y 0ul nlength;
  let p_z = create (Hacl.Cast.uint64_to_sint64 0uL) nlength in
  blit (get_z q) 0ul p_z 0ul nlength;
  let p = make p_x p_y p_z in
  // Point at infinity
  let inf_x = create (Hacl.Cast.uint64_to_sint64 0uL) nlp1 in
  upd inf_x 0ul (Hacl.Cast.uint64_to_sint64 1uL);
  let inf_y = create (Hacl.Cast.uint64_to_sint64 0uL) nlength in
  let inf_z = create (Hacl.Cast.uint64_to_sint64 0uL) nlp1 in
  let inf = make inf_x inf_y inf_z in
  // Perform scalar multiplication by the content of 'n'
  big_step n two_p two_p_plus_q inf p q 0ul;
  // Copy result to output
  copy res two_p
