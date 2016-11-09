module Hacl.EC.Curve25519.Ladder

open FStar.Mul
open FStar.ST
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer
open Hacl.UInt64
(* open Hacl.SBuffer *)
open FStar.Buffer
open FStar.Math.Lib
open Hacl.EC.Curve25519.Parameters
open Hacl.EC.Curve25519.Bigint
open Hacl.EC.Curve25519.Bignum
open Hacl.EC.Curve25519.PPoint


#reset-options "--initial_fuel 0 --max_fuel 0"

(* Module abbreviations *)
(* module B  = Hacl.SBuffer *)
module B = FStar.Buffer
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

#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 5"

val small_step_exit:
  two_p:point -> two_p_plus_q:point{distinct two_p two_p_plus_q /\ same_frame_2 two_p two_p_plus_q} ->
  p:point{distinct p two_p /\ distinct p two_p_plus_q /\ same_frame_2 two_p_plus_q p} ->
  p_plus_q:point{distinct p_plus_q two_p /\ distinct p_plus_q two_p_plus_q /\ distinct p_plus_q p /\ same_frame_2 p p_plus_q} ->
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
       /\ HS.modifies_ref (frame_of p) (refs two_p ++ refs two_p_plus_q (* ++ refs p ++ refs p_plus_q *)) h0 h1 ))
       (* (onCurve h0 p) /\ (onCurve h0 p_plus_q) /\ (onCurve h0 q) *)
       (* /\ (onCurve h1 two_p) /\ (onCurve h1 two_p_plus_q) /\ (live h1 p) /\ (live h1 p_plus_q) /\ (onCurve h1 q)  *)
       (* /\ (modifies (refs two_p +++ refs two_p_plus_q +++ refs p +++ refs p_plus_q) h0 h1) *)
       // Formula_0 replaces (scalar * pow2 8 + byte)
       (* /\ (nTimesQ  (formula_0 scalar byte) (pointOf h0 q) h1 two_p two_p_plus_q) *)
let small_step_exit pp ppq p pq q n byte scalar =
  (* let h0 = ST.get() in *)
  Hacl.EC.Curve25519.PPoint.copy2 pp ppq p pq;
  (* let h1 = ST.get() in *)
  (* distinct_lemma q p; distinct_lemma q pq; distinct_lemma q pp; distinct_lemma q ppq; *)
  (* let s = (erefs pp +*+ erefs ppq +*+ erefs p +*+ erefs pq) in *)
  (* cut(modifies (reveal s) h0 h1); *)
  (* ad(True /\ FStar.TSet.intersect (reveal s) (refs q) = !{}); *)
  (* on_curve_lemma h0 h1 q (erefs pp +*+ erefs ppq +*+ erefs p +*+ erefs pq); *)
  (* cut(onCurve h1 q);  *)
  (* cut(nTimesQ (hide (reveal scalar * pow2 8 + (S8.v byte / pow2 (8-8)))) (pointOf h0 q) h0 p pq);  *)
  ()
  (* helper_lemma_1 scalar byte *)

let lemma_helper_0 r s h0 h1 h2 h3 : Lemma
  (requires (HS.modifies_ref r s h0 h1 /\ HS.modifies_ref r s h1 h2 /\ HS.modifies_ref r s h2 h3))
  (ensures  (HS.modifies_ref r s h0 h3))
  = ()

#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 50"

let lemma_helper_00 a b c h0 h1 : Lemma
  (requires (live h0 c /\ distinct c a /\ distinct c b /\ same_frame_2 a c /\ prop_1 h0 h1 a b))
  (ensures  (live h1 c))
  = ()


let lemma_helper_01 a b c h0 h1 : Lemma
  (requires (live h0 c /\ same_frame c /\ frame_of a <> frame_of c /\ HS.modifies_one (frame_of a) h0 h1
    /\ equal_domains h0 h1))
  (ensures  (live h1 c))
  = ()

let lemma_helper_02 r c h0 h1 : Lemma
  (requires (live h0 c /\ same_frame c /\ r <> frame_of c /\ HS.modifies_one r h0 h1 /\ equal_domains h0 h1))
  (ensures  (live h1 c))
  = ()

let lemma_distinct_symm a b : Lemma
  (requires (distinct a b))
  (ensures (distinct b a))
  [SMTPat (distinct a b)]
  = ()


let lemma_helper_001 a b c d e h0 h1 : Lemma
  (requires (live h0 c /\ live h0 d /\ live h0 e
    /\ distinct a b /\ distinct a c /\ distinct a d
    /\ distinct b c /\ distinct b d /\ distinct c d
    /\ same_frame_2 a b /\ same_frame_2 b c /\ same_frame_2 c d /\ same_frame e /\ frame_of e <> frame_of a
    /\ HS.modifies_one (frame_of a) h0 h1
    /\ HS.modifies_ref (frame_of a) (refs a ++ refs b) h0 h1
    /\ prop_1 h0 h1 a b /\ Map.contains h0.h (frame_of e) /\ Map.contains h0.h (frame_of a)
    /\ equal_domains h0 h1))
  (ensures  (live h1 c /\ live h1 d /\live h1 e))
  = lemma_helper_00 a b c h0 h1;
    lemma_helper_00 a b d h0 h1;
    lemma_helper_01 a b e h0 h1

#reset-options "--initial_fuel 0  --max_fuel 0 --z3timeout 20"

val small_step_core:
   two_p:point -> two_p_plus_q:point{distinct two_p two_p_plus_q /\ same_frame_2 two_p two_p_plus_q} ->
   p:point{distinct two_p p /\ distinct two_p_plus_q p /\ same_frame_2 two_p_plus_q p} ->
   p_plus_q:point{distinct two_p p_plus_q /\ distinct two_p_plus_q p_plus_q /\ distinct p_plus_q p /\ same_frame_2 p p_plus_q} ->
   q:point{same_frame q /\ frame_of q <> frame_of p
   (* distinct q two_p /\ distinct q two_p_plus_q /\ distinct q p /\ distinct q p_plus_q *)} ->
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
  (* distinct_commutative p pq; *)
  let bit = nth_bit b ctr in
  let mask = mk_mask bit in
  (* cut (v mask = pow2 platform_size - 1 \/ v mask = 0);  *)
  let h0 = ST.get() in
  swap_conditional p pq mask;
  let h1 = ST.get() in
  lemma_helper_001 p pq pp ppq q h0 h1;
  (* let h = ST.get() in *)
  (* small_step_core_lemma_1 h0 h pp ppq p pq q; *)
  Hacl.EC.Curve25519.AddAndDouble.double_and_add pp ppq p pq q;
  let h2 = ST.get() in
  lemma_helper_02 (frame_of p) q h1 h2;
  (* let h2 = ST.get() in *)
  swap_conditional pp ppq mask;
  let h3 = ST.get() in
  lemma_helper_001 pp ppq p pq q h2 h3;
  Hacl.EC.Curve25519.AddAndDouble.lemma_helper_2 (frame_of p) h0 h1 (refs p ++ refs pq) (refs pp ++ refs ppq ++ refs p ++ refs pq);
  Hacl.EC.Curve25519.AddAndDouble.lemma_helper_2 (frame_of p) h2 h3 (refs pp ++ refs ppq) (refs pp ++ refs ppq ++ refs p ++ refs pq);
  lemma_helper_0 (frame_of p) (refs pp ++ refs ppq ++ refs p ++ refs pq) h0 h1 h2 h3;
  ()

  (* lemma_5 scalar b ctr; *)
  (* let h1 = ST.get() in *)
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

#reset-options "--initial_fuel 0  --max_fuel 0 --z3timeout 100"

val small_step: two_p:point -> two_p_plus_q:point{distinct two_p two_p_plus_q /\ same_frame_2 two_p two_p_plus_q} ->
   p:point{distinct p two_p /\ distinct p two_p_plus_q /\ same_frame_2 two_p_plus_q p} ->
   p_plus_q:point{distinct p_plus_q two_p /\ distinct p_plus_q two_p_plus_q /\ distinct p_plus_q p /\ same_frame_2 p p_plus_q} ->
   q:point{same_frame q /\ frame_of q <> frame_of p} ->
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
  if U32 (8ul =^ ctr) then begin
    (* lemma_9 ctr; *)
    (* helper_lemma_1 n b;  *)
    ()
  end
  else begin
    let h0 = ST.get() in
    (* lemma_0 ctr 8; *)
    small_step_core pp ppq p pq q n ctr b scalar;
    let h1 = ST.get() in
    let bit = nth_bit b ctr in
    (* cut (nTimesQ (formula_1 n bit) (pointOf h0 q) h1 pp ppq); *)
    (* lemma_10 scalar ctr b; *)
    // Replaces a missing definition of the euclidian division
    (* admiP (True /\ 2*reveal n+S8.v bit = reveal scalar * (pow2 (w ctr+1)) + (S8.v b / pow2 (8 - (w ctr+1)))); *)
    (* cut (w ctr+1 <= 8 /\ True); *)
    (* assert (onCurve h1 pp /\ onCurve h1 ppq /\ live h1 p /\ live h1 pq); *)
    swap_both pp ppq p pq;
    let h2 = ST.get() in
    (* assert (Math.Curve.equal (pointOf h2 p) (pointOf h1 pp) /\ Math.Curve.equal (pointOf h2 pq) (pointOf h1 ppq)); *)
    (* small_step_lemma_1 h0 h1 h2 pp ppq p pq q; *)
    (* formula_lemma n bit;  *)
    (* assert(nTimesQ (eformula_2 n bit) (pointOf h2 q) h2 p pq); *)
    small_step pp ppq p pq q (hide 0(* eformula_2 n bit *)) (U32 (ctr+^1ul)) b scalar;
    let h3 = ST.get() in
    (* small_step_lemma_2 h0 h1 h2 h3 pp ppq p pq q *)
    lemma_helper_0 (frame_of p) (refs pp ++ refs ppq ++ refs p ++ refs pq) h0 h1 h2 h3;
    ()
  end

#reset-options "--z3timeout 20 --initial_fuel 0 --max_fuel 0"


let lemma_helper_1 r s h0 h1 h2 : Lemma
  (requires (HS.modifies_ref r s h0 h1 /\ HS.modifies_ref r s h1 h2))
  (ensures  (HS.modifies_ref r s h0 h2))
  = ()

val big_step:
  n:bytes{length n >= 32} -> pp:point{distinct2 n pp} ->
  ppq:point{distinct2 n ppq /\ distinct pp ppq /\ same_frame_2 pp ppq /\ frame_of pp <> frameOf n} ->
  p:point{distinct2 n p /\ distinct p pp /\ distinct p ppq /\ same_frame_2 ppq p} ->
  pq:point{distinct2 n pq /\ distinct pq pp /\ distinct pq ppq /\ distinct pq p /\ same_frame_2 p pq} ->
  q:point{distinct2 n q /\ same_frame q /\ frame_of p <> frame_of q} ->
  ctr:u32{U32.v ctr<=bytes_length} -> STL unit
    (requires (fun h -> B.live h n /\ live h pp /\ live h ppq /\ live h p /\ live h q /\ live h pq))
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
  let h0 = ST.get() in
  if U32 (blength =^ ctr) then () (* assum(reveal (formula_4 h0 n bytes_length) = valueOfBytes h0 n) *)
  else begin
    (* assum(bytes_length-1-w ctr>=0 /\ bytes_length-w ctr-1>=0); *)
    let byte = index n (U32 (blength-^1ul-^ctr)) in
    (* let m = formula_4 h0 n (w ctr) in *)
    // Replaces missing euclidian definitions in F*
    (* admiP(reveal m = reveal m * pow2 0 + (S8.v byte / pow2 (8-0)) /\ True); *)
    small_step pp ppq p pq q (hide 0)(* m *) 0ul byte (hide 0)(* m *);
    let h1 = ST.get() in assert(live h1 q);
    (* big_step_lemma_1 h0 h1 n pp ppq p pq q ctr byte; *)
    big_step n pp ppq p pq q (U32 (ctr +^ 1ul));
    let h2 = ST.get() in
    lemma_helper_1 (frame_of p) (refs pp ++ refs ppq ++ refs p ++ refs pq) h0 h1 h2;
    ()
    (* big_step_lemma_2 h0 h1 h2 n pp ppq p pq q (w ctr) byte *)
  end

#reset-options "--z3timeout 20 --initial_fuel 0 --max_fuel 0"

private val init_points: q:point{same_frame q} -> tmp:bigint{length tmp = 68 /\ frameOf tmp <> frame_of q} -> Stack unit
  (requires (fun h -> B.live h tmp /\ live h q))
  (ensures  (fun h0 _ h1 -> B.live h1 tmp
    /\ HS.modifies_one (frameOf tmp) h0 h1
    /\ HS.modifies_ref (frameOf tmp) (arefs (only tmp)) h0 h1))
let init_points q tmp =
  let p_x = sub tmp 34ul 6ul in
  let p_y = sub tmp 40ul 5ul in
  let p_z = sub tmp 45ul 6ul in

  let inf_x = sub tmp 51ul 6ul in
  let h0 = ST.get() in
  blit (get_x q) 0ul p_x 0ul nlength;
  blit (get_y q) 0ul p_y 0ul nlength;
  blit (get_z q) 0ul p_z 0ul nlength;
  upd inf_x 0ul (Hacl.Cast.uint64_to_sint64 1uL);
  let h1 = ST.get() in
  assert(modifies_1 tmp h0 h1);
  Hacl.EC.Curve25519.AddAndDouble.lemma_helper_0 h0 h1 tmp;
  ()

#reset-options "--z3timeout 20 --initial_fuel 0 --max_fuel 0"

let lemma_helper_2 hinit h0 h1 h2 hfin r : Lemma
  (requires (fresh_frame hinit h0 /\ HS.modifies_one h0.tip h0 h1 /\ HS.modifies_one r h1 h2
    /\ popped h2 hfin /\ r `HS.is_in` hinit.h
    /\ equal_domains hinit hfin))
  (ensures  (HS.modifies_one r hinit hfin))
  = assert(Set.subset (Map.domain hinit.h) (Map.domain hfin.h))


#reset-options "--z3timeout 100 --initial_fuel 0 --max_fuel 0"

val montgomery_ladder:
  res:point{same_frame res} -> n:bytes{distinct2 n res /\ frame_of res <> frameOf n /\ length n >= 32} ->
  q:point{same_frame q /\ frame_of q <> frame_of res /\ frame_of q <> frameOf n} -> Stack unit
    (requires (fun h -> live h res /\ live h q /\ B.live h n))
      (* live h res /\ onCurve h q )) *)
    (ensures (fun h0 _ h1 -> live h1 res
      /\ HS.modifies_one (frame_of res) h0 h1
      /\ HS.modifies_ref (frame_of res) (refs res) h0 h1
      /\ prop_2 h0 h1 res))
    (* /\ modifies_3 (get_x res) (get_y res) (get_z res) h0 h1)) *)
    (* live h0 res /\ onCurve h0 q /\ onCurve h1 res *)
    (*   (\* /\ (modifies (refs res) h0 h1)  *\) *)
    (*   /\ (pointOf h1 res = (valueOfBytes h0 n +* (pointOf h0 q)))  )) *)
let montgomery_ladder res n q =
  let hinit = ST.get() in
  push_frame();

  // Build 'storage' empty but 'live' points
  let nlp1 = U32 (nlength +^ 1ul) in
  let tot_len = 68ul in
  let h0 = ST.get() in
  let tmp = create (Hacl.Cast.uint64_to_sint64 0uL) tot_len in
  let two_p_x = sub tmp 0ul 6ul  in
  let two_p_y = sub tmp 6ul 5ul in
  let two_p_z = sub tmp 11ul 6ul in

  let two_p_plus_q_x = sub tmp 17ul 6ul in
  let two_p_plus_q_y = sub tmp 23ul 5ul in
  let two_p_plus_q_z = sub tmp 28ul 6ul in

  let p_x = sub tmp 34ul 6ul in
  let p_y = sub tmp 40ul 5ul in
  let p_z = sub tmp 45ul 6ul in

  let inf_x = sub tmp 51ul 6ul in
  let inf_y = sub tmp 57ul 5ul in
  let inf_z = sub tmp 62ul 6ul in

  let two_p =  make two_p_x two_p_y two_p_z in
  let two_p_plus_q = make two_p_plus_q_x two_p_plus_q_y two_p_plus_q_z in
  let p = make p_x p_y p_z in
  let inf = make inf_x inf_y inf_z in
  let h = ST.get() in

  let h1 = ST.get() in
  init_points q tmp;
  let h2 = ST.get() in
  cut (HS.modifies_one (frameOf tmp) h1 h2);
  big_step n two_p two_p_plus_q inf p q 0ul;
  let h3 = ST.get() in
  cut (HS.modifies_one (frameOf tmp) h2 h3);
  // Copy result to output
  copy res two_p;
  let h4 = ST.get() in
  cut (HS.modifies_one (frame_of res) h3 h4);

  pop_frame();
  let hfin = ST.get() in
  assert(equal_domains hinit hfin);
  lemma_reveal_modifies_0 h0 h1;
  lemma_helper_2 hinit h0 h3 h4 hfin (frame_of res);
  ()
