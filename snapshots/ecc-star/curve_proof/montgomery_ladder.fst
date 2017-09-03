(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi Parameters --admit_fsi Modulo --admit_fsi Bignum --admit_fsi ConcretePoint --verify_module MontgomeryLadder --z3rlimit 100;
    variables:MATH=../math_interfaces BIGNUM=../bignum_proof;
    other-files:FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst seq.fsi FStar.Seq.Base.fst FStar.Seq.Properties.fst FStar.Seq.fst FStar.Array.fst FStar.Ghost.fst $BIGNUM/axiomatic.fst $BIGNUM/intlib.fst $BIGNUM/lemmas.fst $BIGNUM/parameters.fsti $BIGNUM/uint.fst $BIGNUM/bigint.fst $BIGNUM/eval.fst $MATH/definitions.fst $MATH/field.fst $BIGNUM/modulo.fsti $BIGNUM/bignum.fsti $MATH/curve.fst concrete_point.fst double_and_add.fst montgomery_ladder_lemmas.fst;
  --*)

module MontgomeryLadder

open FStar.Heap
open FStar.Ghost
open IntLib
open UInt
open Bigint
open Parameters
open Bignum
open Curve
open ConcretePoint
open DoubleAndAdd
open MontgomeryLadderLemmas

val op_Plus_Star: nat -> celem -> GTot celem
let op_Plus_Star (n:nat) (x:celem) = smul n x
let op_Plus_Plus_Plus a b = FStar.Set.union a b

assume val op_Plus_Star_Plus: #a:Type -> x:erased (FStar.Set.set a) -> y:erased (FStar.Set.set a) ->
  Tot (z:erased (FStar.Set.set a){reveal z = (reveal x +++ reveal y)})

// q has to be an element of the curve
type NtimesQ (n:erased nat) (q:celem) (h:heap) (p:point) (p':point) =
  OnCurve h p /\ OnCurve h p' /\ pointOf h p == (reveal n +* q) /\ pointOf h p' == ((reveal n+1) +* q)

// Will be specified using the bitwise operators' semantics
val mk_mask: x:byte -> Tot (y:limb{bitsize (v y) platform_size /\ (x == zero_byte ==> v y = 0) /\ (x = one_byte ==> v y = pow2 platform_size - 1)})
let mk_mask x =
  //@@
  let y = byte_to_limb x in
  neg_limb y

val small_step_exit: 
  two_p:point -> two_p_plus_q:point{Distinct two_p two_p_plus_q} -> 
  p:point{Distinct p two_p /\ Distinct p two_p_plus_q} -> 
  p_plus_q:point{Distinct p_plus_q two_p /\ Distinct p_plus_q two_p_plus_q /\ Distinct p_plus_q p} -> 
  q:point{Distinct q two_p /\ Distinct q two_p_plus_q /\ Distinct q p /\ Distinct q p_plus_q} -> 
  n:erased nat -> byte:byte -> 
  scalar:erased nat{reveal n = reveal scalar * (pow2 8) + (v byte / (pow2 (8-8)))} -> 
  ST unit
     (requires (fun h -> 
       (Live h two_p) /\ (Live h two_p_plus_q) /\ (OnCurve h p) /\ (OnCurve h p_plus_q) /\ (OnCurve h q)
       /\ (NtimesQ n (pointOf h q) h p p_plus_q) 
     ))
     (ensures (fun h0 _ h1 ->
       (OnCurve h0 p) /\ (OnCurve h0 p_plus_q) /\ (OnCurve h0 q)
       /\ (OnCurve h1 two_p) /\ (OnCurve h1 two_p_plus_q) /\ (Live h1 p) /\ (Live h1 p_plus_q) /\ (OnCurve h1 q) 
       /\ (modifies (refs two_p +++ refs two_p_plus_q +++ refs p +++ refs p_plus_q) h0 h1)
       // Formula_0 replaces (scalar * pow2 8 + byte)
       /\ (NtimesQ  (formula_0 scalar byte) (pointOf h0 q) h1 two_p two_p_plus_q)
     ))     
let small_step_exit pp ppq p pq q n byte scalar =
  //@@
  let h0 = ST.get() in
  ConcretePoint.copy2 pp ppq p pq;
  let h1 = ST.get() in
  distinct_lemma q p; distinct_lemma q pq; distinct_lemma q pp; distinct_lemma q ppq;
  let s = (erefs pp +*+ erefs ppq +*+ erefs p +*+ erefs pq) in
  cut(modifies (reveal s) h0 h1);
  admitP(True /\ FStar.Set.intersect (reveal s) (refs q) = !{});
  on_curve_lemma h0 h1 q (erefs pp +*+ erefs ppq +*+ erefs p +*+ erefs pq);
  cut(OnCurve h1 q); 
  cut(NtimesQ (hide (reveal scalar * pow2 8 + (v byte / pow2 (8-8)))) (pointOf h0 q) h0 p pq); 
  helper_lemma_1 scalar byte

#reset-options

opaque val nth_bit: byt:byte -> idx:nat{idx < 8} -> Tot (b:byte{log_and_byte (shift_right_byte byt (7-idx)) (one_byte) = b /\ (b == zero_byte \/ b = one_byte) } )
let nth_bit byte idx =
  let bit = log_and_byte (shift_right_byte byte (7-idx)) (one_byte) in
  and_one_lemma (shift_right_byte byte (7-idx));
  bit

opaque val gdouble_and_add_lemma_1: q:Curve.celem -> n:erased nat -> m:erased nat -> 
  GLemma unit (requires (True)) 
	(ensures ((Curve.add (reveal n +* q) (reveal m +* q)) == ((reveal n + reveal m) +* q) )) []
let gdouble_and_add_lemma_1 q n m = 
  Curve.smul_lemma q (reveal n) (reveal m)

val double_and_add_lemma_1: q:Curve.celem -> n:erased nat -> m:erased nat -> 
  Lemma (requires (True)) 
	(ensures ((Curve.add (reveal n +* q) (reveal m +* q)) == ((reveal n + reveal m) +* q) ))
let double_and_add_lemma_1 q n m =
  coerce
    (requires (True))
    (ensures ((Curve.add (reveal n +* q) (reveal m +* q)) == ((reveal n + reveal m) +* q) ))
    (fun _ -> gdouble_and_add_lemma_1 q n m)

opaque val gsmall_step_core_lemma_1: h0:heap -> h1:heap -> pp:point -> ppq:point{Distinct pp ppq} -> p:point{Distinct p pp /\ Distinct p ppq} -> pq:point{Distinct pq pp /\ Distinct pq ppq /\ Distinct pq p} -> q:point{Distinct q pp /\ Distinct q ppq /\ Distinct q p /\ Distinct q pq} -> GLemma unit
  (requires (modifies (refs p +++ refs pq) h0 h1 /\ OnCurve h0 q /\ Live h0 pp /\ Live h0 ppq))
  (ensures (Live h1 pp /\ Live h1 ppq /\ OnCurve h1 q)) []
let gsmall_step_core_lemma_1 h0 h1 pp ppq p pq q =
  //@@
  FStar.Set.lemma_equal_intro (FStar.Set.intersect (refs p +++ refs pq) (refs pp)) !{};  
  FStar.Set.lemma_equal_intro (FStar.Set.intersect (refs p +++ refs pq) (refs ppq)) !{}; 
  FStar.Set.lemma_equal_intro (FStar.Set.intersect (refs p +++ refs pq) (refs q)) !{}; 
  live_lemma h0 h1 pp (hide (refs p +++ refs pq)); 
  live_lemma h0 h1 ppq (hide ((refs p +++ refs pq)));
  on_curve_lemma h0 h1 q (hide (refs p +++ refs pq))

val small_step_core_lemma_1: h0:heap -> h1:heap -> pp:point -> ppq:point{Distinct pp ppq} -> p:point{Distinct p pp /\ Distinct p ppq} -> pq:point{Distinct pq pp /\ Distinct pq ppq /\ Distinct pq p} -> q:point{Distinct q pp /\ Distinct q ppq /\ Distinct q p /\ Distinct q pq} -> Lemma
  (requires (modifies (refs p +++ refs pq) h0 h1 /\ OnCurve h0 q /\ Live h0 pp /\ Live h0 ppq))
  (ensures (Live h1 pp /\ Live h1 ppq /\ OnCurve h1 q))
let small_step_core_lemma_1 h0 h1 pp ppq p pq q =
  coerce 
    (requires (modifies (refs p +++ refs pq) h0 h1 /\ OnCurve h0 q /\ Live h0 pp /\ Live h0 ppq))
    (ensures (Live h1 pp /\ Live h1 ppq /\ OnCurve h1 q))
    (fun _ -> gsmall_step_core_lemma_1 h0 h1 pp ppq p pq q)

#reset-options

val small_step_core_lemma_2: h0:heap -> h:heap -> h2:heap -> h1:heap -> pp:point -> ppq:point{Distinct pp ppq} -> p:point{Distinct p pp /\ Distinct p ppq} -> pq:point{Distinct pq pp /\ Distinct pq ppq /\ Distinct pq p} -> q:point{Distinct q pp /\ Distinct q ppq /\ Distinct q p /\ Distinct q pq} -> Lemma
  (requires (modifies (refs p +++ refs pq) h0 h /\ modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h h2 /\ modifies (refs pp +++ refs ppq) h2 h1))
  (ensures (modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h0 h1))
let small_step_core_lemma_2 h0 h h2 h1 pp ppq p pq q = ()

#reset-options

opaque val gsmall_step_core_lemma_3: h0:heap -> h:heap -> h2:heap -> h1:heap -> pp:point -> ppq:point{Distinct pp ppq} -> p:point{Distinct p pp /\ Distinct p ppq} -> pq:point{Distinct pq pp /\ Distinct pq ppq /\ Distinct pq p} -> q:point{Distinct q pp /\ Distinct q ppq /\ Distinct q p /\ Distinct q pq} ->    n:erased nat -> ctr:nat{ctr<8} -> byt:byte -> scalar:erased nat{reveal n = reveal scalar * (pow2 ctr) + (v byt / (pow2 (8-ctr)))} -> GLemma unit
  (requires (
    let bit = (nth_bit byt ctr) in
    OnCurve h0 p /\ OnCurve h0 pq /\ OnCurve h1 pp /\ OnCurve h1 ppq /\ OnCurve h0 q
    /\ OnCurve h p /\ OnCurve h pq /\ OnCurve h2 pp /\ OnCurve h2 ppq
    /\ (NtimesQ n (pointOf h0 q) h0 p pq)
    /\ ( bit == zero_byte ==> ((pointOf h p) == (pointOf h0 p) /\ (pointOf h pq) == (pointOf h0 pq)) )
    /\ ( bit == one_byte ==> ((pointOf h pq) == (pointOf h0 p) /\ (pointOf h p) == (pointOf h0 pq)) )
    /\ ( (pointOf h2 pp) == (Curve.add (pointOf h p) (pointOf h p)) /\ (pointOf h2 ppq) == (Curve.add (pointOf h p) (pointOf h pq)))
    /\ (bit == zero_byte ==> ((pointOf h1 pp) == (pointOf h2 pp) /\ (pointOf h1 ppq) == (pointOf h2 ppq)))
    /\ (bit == one_byte ==> ((pointOf h1 pp) == (pointOf h2 ppq) /\ (pointOf h1 ppq) == (pointOf h2 pp))) ))
  (ensures (OnCurve h1 pp /\ OnCurve h1 ppq /\ OnCurve h0 q 
    /\ NtimesQ (formula_1 n (nth_bit byt ctr)) (pointOf h0 q) h1 pp ppq))
 []
let gsmall_step_core_lemma_3 h0 h h2 h1 pp ppq p pq q n ctr byt scalar =
  //@@
  let q0 = pointOf h0 q in
  let bit = nth_bit byt ctr in
  if (bit = zero_byte) then (
      Curve.add_equality (pointOf h p) (pointOf h p) (pointOf h0 p) (pointOf h0 p);
      Curve.add_equality (pointOf h p) (pointOf h pq) (pointOf h0 p) (pointOf h0 pq)
      );
  if (bit = one_byte) then (
      Curve.add_equality (pointOf h p) (pointOf h p) (pointOf h0 pq) (pointOf h0 pq);
      Curve.add_equality (pointOf h p) (pointOf h pq) (pointOf h0 pq) (pointOf h0 p)
      );
  cut (bit == zero_byte ==> 
      ((pointOf h1 pp) == (Curve.add (pointOf h0 p) (pointOf h0 p))
      /\ (pointOf h1 ppq) == (Curve.add (pointOf h0 p) (pointOf h0 pq))));
  cut (bit == one_byte ==> 
      ((pointOf h1 pp) == (Curve.add (pointOf h0 pq) (pointOf h0 p))
      /\ (pointOf h1 ppq) == (Curve.add (pointOf h0 pq) (pointOf h0 pq)))); 
  Curve.add_equality (pointOf h0 p) (pointOf h0 p) (smul (reveal n) q0) (smul (reveal n) q0); 
  Curve.add_equality (pointOf h0 p) (pointOf h0 pq) (smul (reveal n) q0) (smul (reveal n+1) q0);
  Curve.add_equality (pointOf h0 pq) (pointOf h0 pq) (smul (reveal n+1) q0) (smul (reveal n+1) q0);
  Curve.add_equality (pointOf h0 pq) (pointOf h0 p) (smul (reveal n+1) q0) (smul (reveal n) q0); 
  cut (bit == zero_byte ==> 
      ((pointOf h1 pp) == (Curve.add (smul (reveal n) q0) (smul (reveal n) q0))
      /\ (pointOf h1 ppq) == (Curve.add (smul (reveal n) q0) (smul (reveal n+1) q0)))); 
  cut (bit = one_byte ==> 
      ((pointOf h1 pp) == (Curve.add (smul (reveal n+1) q0) (smul (reveal n) q0))
      /\ (pointOf h1 ppq) == (Curve.add (smul (reveal n+1) q0) (smul (reveal n+1) q0)))); 
  double_and_add_lemma_1 q0 n n;
  double_and_add_lemma_1 q0 n (hide (reveal n+1));
  double_and_add_lemma_1 q0 (hide (reveal n+1)) n;
  double_and_add_lemma_1 q0 (hide (reveal n+1)) (hide (reveal n+1)); 
  lemma_8 (reveal n);
  cut (bit == zero_byte \/ bit == one_byte); 
  cut (bit == zero_byte ==> NtimesQ (hide (2*(reveal n)+v bit)) q0 h1 pp ppq);
  cut (bit == one_byte ==> NtimesQ (hide (2*(reveal n)+v bit)) q0 h1 pp ppq);
  cut (NtimesQ (hide (2*(reveal n)+v bit)) q0 h1 pp ppq);
  cut (True /\ nth_bit byt ctr = bit);
  cut (True /\ reveal (formula_1 n (nth_bit byt ctr)) = (2*reveal n+v bit));
  cut (NtimesQ (formula_1 n (nth_bit byt ctr)) q0 h1 pp ppq)

val small_step_core_lemma_3: h0:heap -> h:heap -> h2:heap -> h1:heap -> pp:point -> ppq:point{Distinct pp ppq} -> p:point{Distinct p pp /\ Distinct p ppq} -> pq:point{Distinct pq pp /\ Distinct pq ppq /\ Distinct pq p} -> q:point{Distinct q pp /\ Distinct q ppq /\ Distinct q p /\ Distinct q pq} ->    n:erased nat -> ctr:nat{ctr<8} -> byt:byte -> scalar:erased nat{reveal n = reveal scalar * (pow2 ctr) + (v byt / (pow2 (8-ctr)))} -> Lemma
  (requires (
    let bit = (nth_bit byt ctr) in
    OnCurve h0 p /\ OnCurve h0 pq /\ OnCurve h1 pp /\ OnCurve h1 ppq /\ OnCurve h0 q
    /\ OnCurve h p /\ OnCurve h pq /\ OnCurve h2 pp /\ OnCurve h2 ppq
    /\ (NtimesQ n (pointOf h0 q) h0 p pq)
    /\ ( bit == zero_byte ==> ((pointOf h p) == (pointOf h0 p) /\ (pointOf h pq) == (pointOf h0 pq)) )
    /\ ( bit == one_byte ==> ((pointOf h pq) == (pointOf h0 p) /\ (pointOf h p) == (pointOf h0 pq)) )
    /\ ( (pointOf h2 pp) == (Curve.add (pointOf h p) (pointOf h p)) /\ (pointOf h2 ppq) == (Curve.add (pointOf h p) (pointOf h pq)))
    /\ (bit == zero_byte ==> ((pointOf h1 pp) == (pointOf h2 pp) /\ (pointOf h1 ppq) == (pointOf h2 ppq)))
    /\ (bit == one_byte ==> ((pointOf h1 pp) == (pointOf h2 ppq) /\ (pointOf h1 ppq) == (pointOf h2 pp))) ))
  (ensures (OnCurve h1 pp /\ OnCurve h1 ppq /\ OnCurve h0 q 
    /\ NtimesQ (formula_1 n (nth_bit byt ctr)) (pointOf h0 q) h1 pp ppq))
let small_step_core_lemma_3 h0 h h2 h1 pp ppq p pq q n ctr byt scalar =
  coerce 
  (requires (
    let bit = (nth_bit byt ctr) in
    OnCurve h0 p /\ OnCurve h0 pq /\ OnCurve h1 pp /\ OnCurve h1 ppq /\ OnCurve h0 q
    /\ OnCurve h p /\ OnCurve h pq /\ OnCurve h2 pp /\ OnCurve h2 ppq
    /\ (NtimesQ n (pointOf h0 q) h0 p pq)
    /\ ( bit == zero_byte ==> ((pointOf h p) == (pointOf h0 p) /\ (pointOf h pq) == (pointOf h0 pq)) )
    /\ ( bit == one_byte ==> ((pointOf h pq) == (pointOf h0 p) /\ (pointOf h p) == (pointOf h0 pq)) )
    /\ ( (pointOf h2 pp) == (Curve.add (pointOf h p) (pointOf h p)) /\ (pointOf h2 ppq) == (Curve.add (pointOf h p) (pointOf h pq)))
    /\ (bit == zero_byte ==> ((pointOf h1 pp) == (pointOf h2 pp) /\ (pointOf h1 ppq) == (pointOf h2 ppq)))
    /\ (bit == one_byte ==> ((pointOf h1 pp) == (pointOf h2 ppq) /\ (pointOf h1 ppq) == (pointOf h2 pp))) ))
  (ensures (OnCurve h1 pp /\ OnCurve h1 ppq /\ OnCurve h0 q 
    /\ NtimesQ (formula_1 n (nth_bit byt ctr)) (pointOf h0 q) h1 pp ppq))
  (fun _ -> gsmall_step_core_lemma_3 h0 h h2 h1 pp ppq p pq q n ctr byt scalar)

#reset-options

val small_step_core: 
   two_p:point -> two_p_plus_q:point{Distinct two_p two_p_plus_q} -> 
   p:point{Distinct p two_p /\ Distinct p two_p_plus_q} -> 
   p_plus_q:point{Distinct p_plus_q two_p /\ Distinct p_plus_q two_p_plus_q /\ Distinct p_plus_q p} -> 
   q:point{Distinct q two_p /\ Distinct q two_p_plus_q /\ Distinct q p /\ Distinct q p_plus_q} -> 
   n:erased nat -> ctr:nat{ctr<8} -> byt:byte -> 
   scalar:erased nat{reveal n = reveal scalar * (pow2 ctr) + (v byt / (pow2 (8-ctr)))} -> 
   ST unit
     (requires (fun h -> 
       (Live h two_p) /\ (Live h two_p_plus_q) /\ (OnCurve h p) /\ (OnCurve h p_plus_q) /\ (OnCurve h q)
       /\ (NtimesQ n (pointOf h q) h p p_plus_q) 
     ))
     (ensures (fun h0 _ h1 ->
       (OnCurve h0 p) /\ (OnCurve h0 p_plus_q) /\ (OnCurve h0 q)
       /\ (OnCurve h1 two_p) /\ (OnCurve h1 two_p_plus_q) /\ (Live h1 p) /\ (Live h1 p_plus_q) /\ (OnCurve h1 q) 
       /\ (modifies (refs two_p +++ refs two_p_plus_q +++ refs p +++ refs p_plus_q) h0 h1)
       // Formula_0 replaces (scalar * pow2 8 + byte)
       /\ (NtimesQ  (formula_2 (reveal n) (nth_bit byt ctr)) (pointOf h0 q) h1 two_p two_p_plus_q)
     ))
let small_step_core pp ppq p pq q n ctr b scalar =
  //@@
  let h0 = ST.get() in
  distinct_commutative p pq;
  let bit = nth_bit b ctr in
  let mask = mk_mask bit in
  cut (v mask = IntLib.pow2 platform_size - 1 \/ v mask = 0); 
  swap_conditional p pq mask; 
  let h = ST.get() in
  small_step_core_lemma_1 h0 h pp ppq p pq q;
  (* We are garantied that p <> pq provided
     that the initial point is not Inf *)
  admitP(True /\ pointOf h p <> pointOf h pq);
  double_and_add pp ppq p pq q; 
  let h2 = ST.get() in
  swap_conditional pp ppq mask; 
  lemma_5 scalar b ctr;
  let h1 = ST.get() in
  assert ((Live h2 p) /\ (Live h2 pq) /\ (OnCurve h2 q)); 
  assert (OnCurve h1 pp /\ OnCurve h1 ppq); 
  let set2 = (erefs pp +*+ erefs ppq +*+ erefs p +*+ erefs pq) in
  let set21 = (erefs pp +*+ erefs ppq) in
  assert(modifies (reveal set21) h2 h1); 
  small_step_core_lemma_1 h2 h1 p pq pp ppq q; 
  small_step_core_lemma_2 h0 h h2 h1 pp ppq p pq q; 
  cut ( bit == zero_byte ==> ((pointOf h p) == (pointOf h0 p) /\ (pointOf h pq) == (pointOf h0 pq)) );
  cut ( bit == one_byte ==> ((pointOf h pq) == (pointOf h0 p) /\ (pointOf h p) == (pointOf h0 pq)) );
  cut ( ((pointOf h2 pp) == (Curve.add (pointOf h p) (pointOf h p)) /\ (pointOf h2 ppq) == (Curve.add (pointOf h p) (pointOf h pq))) );
  cut (bit == zero_byte ==> ((pointOf h1 pp) == (pointOf h2 pp) /\ (pointOf h1 ppq) == (pointOf h2 ppq)));
  cut (bit == one_byte ==> ((pointOf h1 pp) == (pointOf h2 ppq) /\ (pointOf h1 ppq) == (pointOf h2 pp))); 
  cut (NtimesQ n (pointOf h0 q) h0 p pq); 
  small_step_core_lemma_3 h0 h h2 h1 pp ppq p pq q n ctr b scalar
  
#reset-options

opaque val gsmall_step_lemma_1 : h0:heap -> h1:heap -> h2:heap ->
   pp:point -> ppq:point{Distinct pp ppq} -> p:point{Distinct p pp /\ Distinct p ppq} -> 
   pq:point{Distinct pq pp /\ Distinct pq ppq /\ Distinct pq p} -> 
   q:point{Distinct q pp /\ Distinct q ppq /\ Distinct q p /\ Distinct q pq} -> 
   GLemma unit
     (requires (OnCurve h0 q /\ modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h0 h1
       /\ modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h1 h2))
     (ensures (OnCurve h0 q /\ OnCurve h1 q /\ OnCurve h2 q
	       /\ pointOf h2 q == pointOf h0 q /\ pointOf h1 q == pointOf h0 q)) []
let gsmall_step_lemma_1 h0 h1 h2 pp ppq p pq q =
  //@@
  FStar.Set.lemma_equal_intro (FStar.Set.intersect (refs pp +++ refs ppq +++ refs p +++ refs pq) (refs q)) !{}; 
  on_curve_lemma h0 h2 q (hide (refs pp +++ refs ppq +++ refs p +++ refs pq));
  on_curve_lemma h0 h1 q (hide (refs pp +++ refs ppq +++ refs p +++ refs pq))

val small_step_lemma_1 : h0:heap -> h1:heap -> h2:heap ->
   pp:point -> ppq:point{Distinct pp ppq} -> p:point{Distinct p pp /\ Distinct p ppq} -> 
   pq:point{Distinct pq pp /\ Distinct pq ppq /\ Distinct pq p} -> 
   q:point{Distinct q pp /\ Distinct q ppq /\ Distinct q p /\ Distinct q pq} -> 
   Lemma
     (requires (OnCurve h0 q /\ modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h0 h1
       /\ modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h1 h2))
     (ensures (OnCurve h0 q /\ OnCurve h1 q /\ OnCurve h2 q
	       /\ pointOf h2 q == pointOf h0 q /\ pointOf h1 q == pointOf h0 q))
let small_step_lemma_1 h0 h1 h2 pp ppq p pq q =
  coerce 
     (requires (OnCurve h0 q /\ modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h0 h1
       /\ modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h1 h2))
     (ensures (OnCurve h0 q /\ OnCurve h1 q /\ OnCurve h2 q
	       /\ pointOf h2 q == pointOf h0 q /\ pointOf h1 q == pointOf h0 q))
     (fun _ -> gsmall_step_lemma_1 h0 h1 h2 pp ppq p pq q)

opaque val gsmall_step_lemma_2 : h0:heap -> h1:heap -> h2:heap -> h3:heap ->
   pp:point -> ppq:point{Distinct pp ppq} -> p:point{Distinct p pp /\ Distinct p ppq} -> 
   pq:point{Distinct pq pp /\ Distinct pq ppq /\ Distinct pq p} -> 
   q:point{Distinct q pp /\ Distinct q ppq /\ Distinct q p /\ Distinct q pq} -> 
   GLemma unit
     (requires (OnCurve h0 q /\ modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h0 h1
       /\ modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h1 h2
       /\ modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h2 h3))
     (ensures (OnCurve h3 q /\ modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h0 h3)) []
let gsmall_step_lemma_2 h0 h1 h2 h3 pp ppq p pq q =
  //@@
  FStar.Set.lemma_equal_intro (FStar.Set.intersect (refs pp +++ refs ppq +++ refs p +++ refs pq) (refs q)) !{}; 
  cut (modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h0 h3);
  on_curve_lemma h0 h3 q (hide (refs pp +++ refs ppq +++ refs p +++ refs pq))

val small_step_lemma_2 : h0:heap -> h1:heap -> h2:heap -> h3:heap ->
   pp:point -> ppq:point{Distinct pp ppq} -> p:point{Distinct p pp /\ Distinct p ppq} -> 
   pq:point{Distinct pq pp /\ Distinct pq ppq /\ Distinct pq p} -> 
   q:point{Distinct q pp /\ Distinct q ppq /\ Distinct q p /\ Distinct q pq} -> 
   Lemma
     (requires (OnCurve h0 q /\ modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h0 h1
       /\ modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h1 h2
       /\ modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h2 h3))
     (ensures (OnCurve h3 q /\ modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h0 h3))
let small_step_lemma_2 h0 h1 h2 h3 pp ppq p pq q =
  coerce
     (requires (OnCurve h0 q /\ modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h0 h1
       /\ modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h1 h2
       /\ modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h2 h3))
     (ensures (OnCurve h3 q /\ modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h0 h3))
     (fun _ -> gsmall_step_lemma_2 h0 h1 h2 h3 pp ppq p pq q)

val small_step :
   two_p:point -> two_p_plus_q:point{Distinct two_p two_p_plus_q} -> 
   p:point{Distinct p two_p /\ Distinct p two_p_plus_q} -> 
   p_plus_q:point{Distinct p_plus_q two_p /\ Distinct p_plus_q two_p_plus_q /\ Distinct p_plus_q p} -> 
   q:point{Distinct q two_p /\ Distinct q two_p_plus_q /\ Distinct q p /\ Distinct q p_plus_q} -> 
   n:erased nat -> ctr:nat{ctr<=8} -> b:byte -> 
   scalar:erased nat{reveal n = reveal scalar * (pow2 ctr) + (v b / (pow2 (8-ctr)))} -> 
   ST unit
     (requires (fun h -> 
       (Live h two_p) /\ (Live h two_p_plus_q) /\ (OnCurve h p) /\ (OnCurve h p_plus_q) /\ (OnCurve h q)
       /\ (NtimesQ n (pointOf h q) h p p_plus_q) 
     ))
     (ensures (fun h0 _ h1 ->
       (OnCurve h0 p) /\ (OnCurve h0 p_plus_q) /\ (OnCurve h0 q)
       /\ (Live h1 two_p) /\ (Live h1 two_p_plus_q) /\ (OnCurve h1 p) /\ (OnCurve h1 p_plus_q) /\ (OnCurve h1 q) 
       /\ (modifies (refs two_p +++ refs two_p_plus_q +++ refs p +++ refs p_plus_q) h0 h1)
       // Formula_0 replaces (scalar * pow2 8 + b)
       /\ (NtimesQ  (formula_0 scalar b) (pointOf h0 q) h1 p p_plus_q)
     ))
let rec small_step pp ppq p pq q n ctr b scalar =
  //@@
  match 8 - ctr with
  | 0 -> 
    lemma_9 ctr;
    helper_lemma_1 n b; ()
  | _ -> 
    let h0 = ST.get() in
    lemma_0 ctr 8;
    small_step_core pp ppq p pq q n ctr b scalar; 
    let h1 = ST.get() in
    let bit = nth_bit b ctr in 
    cut (NtimesQ (formula_1 n bit) (pointOf h0 q) h1 pp ppq); 
    lemma_10 scalar ctr b;
    // Replaces a missing definition of the euclidian division 
    admitP (True /\ 2*reveal n+v bit = reveal scalar * (pow2 (ctr+1)) + (v b / pow2 (8 - (ctr+1))));
    cut (ctr+1 <= 8 /\ True); 
    assert (OnCurve h1 pp /\ OnCurve h1 ppq /\ Live h1 p /\ Live h1 pq); 
    swap_both pp ppq p pq; 
    let h2 = ST.get() in 
    assert (Curve.Equal (pointOf h2 p) (pointOf h1 pp) /\ Curve.Equal (pointOf h2 pq) (pointOf h1 ppq)); 
    small_step_lemma_1 h0 h1 h2 pp ppq p pq q;
    formula_lemma n bit; 
    assert(NtimesQ (eformula_2 n bit) (pointOf h2 q) h2 p pq); 
    small_step pp ppq p pq q (eformula_2 n bit) (ctr+1) b scalar; 
    let h3 = ST.get() in
    small_step_lemma_2 h0 h1 h2 h3 pp ppq p pq q

assume  val formula_4: h:heap -> n:serialized{Serialized h n} -> ctr:nat{ctr<=bytes_length} -> Tot (z:erased nat{reveal z = (valueOfBytes h n / pow2 ((bytes_length-ctr)*8))})

#reset-options

type Distinct2 (n:serialized) (p:point) = b2t(not(FStar.Set.mem (Ref (getRef n)) (refs p)))

#reset-options

val serialized_lemma: h0:heap -> h1:heap -> n:serialized{Serialized h0 n} -> mods:FStar.Set.set aref{FStar.Set.intersect mods !{getRef n} = !{}} -> Lemma
  (requires (modifies mods h0 h1))
  (ensures (Serialized h1 n /\ valueOfBytes h1 n = valueOfBytes h0 n))
let serialized_lemma h0 h1 n mods =
  //@@
  FStar.Set.lemma_equal_intro !{getRef n} (FStar.Set.singleton (Ref (getRef n))); 
  cut (True /\ FStar.Set.mem (Ref (getRef n)) !{getRef n}); 
  cut( not(FStar.Set.mem (Ref (getRef n)) mods) /\ True); 
  no_upd_lemma h0 h1 n mods; 
  assert(forall (i:nat). {:pattern (getValue h1 n i)} i < bytes_length ==> v (getValue h1 n i) = v (getValue h1 n i));  
  Eval.eval_eq_lemma h0 h1 n n bytes_length
  
#reset-options

opaque val gbig_step_lemma_1: h0:heap -> h1:heap ->
  n:serialized -> pp:point{Distinct2 n pp} -> ppq:point{Distinct2 n ppq /\ Distinct pp ppq} -> 
   p:point{Distinct2 n p /\ Distinct p pp /\ Distinct p ppq} -> 
   pq:point{Distinct2 n pq /\ Distinct pq pp /\ Distinct pq ppq /\ Distinct pq p} -> 
   q:point{Distinct2 n q /\ Distinct q pp /\ Distinct q ppq /\ Distinct q p /\ Distinct q pq} -> ctr:nat{ctr<=bytes_length-1} -> b:byte ->
  GLemma unit
    (requires (
      (Live h0 pp) /\ (Live h0 ppq) /\ (OnCurve h0 p) /\ (OnCurve h0 pq) /\ (OnCurve h0 q) /\ Serialized h0 n
      /\ (NtimesQ (formula_4 h0 n ctr) (pointOf h0 q) h0 p pq)
      /\ modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h0 h1
      /\ OnCurve h1 p /\ OnCurve h1 pq /\ OnCurve h1 q /\ Live h1 pp /\ Live h1 ppq
      /\ b = getValue h0 n (bytes_length-1-ctr)
      /\ NtimesQ (formula_0 (formula_4 h0 n ctr) b) (pointOf h0 q) h1 p pq
    ))
    (ensures (
      (Live h1 pp) /\ (Live h1 ppq) /\ (OnCurve h1 p) /\ (OnCurve h1 pq) /\ (OnCurve h1 q) /\ Serialized h1 n
      /\ (NtimesQ (formula_4 h1 n (ctr+1)) (pointOf h1 q) h1 p pq)
    )) []
let gbig_step_lemma_1 h0 h1 n pp ppq p pq q ctr b =
  //@@
  let mods = (refs pp +++ refs ppq +++ refs p +++ refs pq) in
  FStar.Set.lemma_equal_intro (FStar.Set.intersect mods !{getRef n}) !{}; 
  FStar.Set.lemma_equal_intro (FStar.Set.intersect mods (refs q)) !{}; 
  serialized_lemma h0 h1 n mods; 
  on_curve_lemma h0 h1 q (hide mods);
  admitP(reveal (formula_4 h0 n (ctr+1)) = reveal (formula_0 (formula_4 h0 n ctr) b) /\ True)

val big_step_lemma_1: h0:heap -> h1:heap ->
  n:serialized -> pp:point{Distinct2 n pp} -> ppq:point{Distinct2 n ppq /\ Distinct pp ppq} -> 
   p:point{Distinct2 n p /\ Distinct p pp /\ Distinct p ppq} -> 
   pq:point{Distinct2 n pq /\ Distinct pq pp /\ Distinct pq ppq /\ Distinct pq p} -> 
   q:point{Distinct2 n q /\ Distinct q pp /\ Distinct q ppq /\ Distinct q p /\ Distinct q pq} -> ctr:nat{ctr<=bytes_length-1} -> b:byte ->
  Lemma
    (requires (
      (Live h0 pp) /\ (Live h0 ppq) /\ (OnCurve h0 p) /\ (OnCurve h0 pq) /\ (OnCurve h0 q) /\ Serialized h0 n
      /\ (NtimesQ (formula_4 h0 n ctr) (pointOf h0 q) h0 p pq)
      /\ modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h0 h1
      /\ OnCurve h1 p /\ OnCurve h1 pq /\ OnCurve h1 q /\ Live h1 pp /\ Live h1 ppq
      /\ b = getValue h0 n (bytes_length-1-ctr)
      /\ NtimesQ (formula_0 (formula_4 h0 n ctr) b) (pointOf h0 q) h1 p pq
    ))
    (ensures (
      (Live h1 pp) /\ (Live h1 ppq) /\ (OnCurve h1 p) /\ (OnCurve h1 pq) /\ (OnCurve h1 q) /\ Serialized h1 n
      /\ (NtimesQ (formula_4 h1 n (ctr+1)) (pointOf h1 q) h1 p pq)
    ))

let big_step_lemma_1 h0 h1 n pp ppq p pq q ctr b =
  coerce 
      (requires (
      (Live h0 pp) /\ (Live h0 ppq) /\ (OnCurve h0 p) /\ (OnCurve h0 pq) /\ (OnCurve h0 q) /\ Serialized h0 n
      /\ (NtimesQ (formula_4 h0 n ctr) (pointOf h0 q) h0 p pq)
      /\ modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h0 h1
      /\ OnCurve h1 p /\ OnCurve h1 pq /\ OnCurve h1 q /\ Live h1 pp /\ Live h1 ppq
      /\ b = getValue h0 n (bytes_length-1-ctr)
      /\ NtimesQ (formula_0 (formula_4 h0 n ctr) b) (pointOf h0 q) h1 p pq
    ))
    (ensures (
      (Live h1 pp) /\ (Live h1 ppq) /\ (OnCurve h1 p) /\ (OnCurve h1 pq) /\ (OnCurve h1 q) /\ Serialized h1 n
      /\ (NtimesQ (formula_4 h1 n (ctr+1)) (pointOf h1 q) h1 p pq)
    ))
    (fun _ -> gbig_step_lemma_1 h0 h1 n pp ppq p pq q ctr b)
    
#reset-options

opaque val gbig_step_lemma_2: h0:heap -> h1:heap -> h2:heap ->
  n:serialized -> pp:point{Distinct2 n pp} -> ppq:point{Distinct2 n ppq /\ Distinct pp ppq} -> 
   p:point{Distinct2 n p /\ Distinct p pp /\ Distinct p ppq} -> 
   pq:point{Distinct2 n pq /\ Distinct pq pp /\ Distinct pq ppq /\ Distinct pq p} -> 
   q:point{Distinct2 n q /\ Distinct q pp /\ Distinct q ppq /\ Distinct q p /\ Distinct q pq} ->  ctr:nat{ctr<=bytes_length-1} -> b:byte -> GLemma unit
    (requires (
      (Live h0 pp) /\ (Live h0 ppq) /\ (OnCurve h0 p) /\ (OnCurve h0 pq) /\ (OnCurve h0 q) /\ Serialized h0 n
      /\ (NtimesQ (formula_4 h0 n ctr) (pointOf h0 q) h0 p pq)
      /\ modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h0 h1
      /\ OnCurve h1 p /\ OnCurve h1 pq /\ OnCurve h1 q /\ Live h1 pp /\ Live h1 ppq
      /\ b = getValue h0 n (bytes_length-1-ctr)
      /\ NtimesQ (formula_0 (formula_4 h0 n ctr) b) (pointOf h0 q) h1 p pq
      /\ (Live h1 pp) /\ (Live h1 ppq) /\ (OnCurve h1 p) /\ (OnCurve h1 pq) /\ (OnCurve h1 q)
      /\ (OnCurve h2 p) /\ (OnCurve h2 pq) /\ Serialized h1 n
      /\ (modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h1 h2)
      /\ (NtimesQ (formula_4 h1 n (ctr+1)) (pointOf h1 q) h1 p pq)
      /\ (NtimesQ (hide (valueOfBytes h1 n)) (pointOf h1 q) h2 p pq)
    ))
    (ensures (
      (Live h0 pp) /\ (Live h0 ppq) /\ (OnCurve h0 p) /\ (OnCurve h0 pq) /\ (OnCurve h0 q)
      /\ (OnCurve h2 p) /\ (OnCurve h2 pq) /\ Serialized h0 n
      /\ (modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h0 h2)
      /\ (NtimesQ (formula_4 h0 n ctr) (pointOf h0 q) h0 p pq)
      /\ (NtimesQ (hide (valueOfBytes h0 n)) (pointOf h0 q) h2 p pq)
    )) []
let gbig_step_lemma_2 h0 h1 h2 n pp ppq p pq q ctr byte = 
  //@@
  let mods = (refs pp +++ refs ppq +++ refs p +++ refs pq) in
  FStar.Set.lemma_equal_intro (FStar.Set.intersect mods !{getRef n}) !{}; 
  FStar.Set.lemma_equal_intro (FStar.Set.intersect mods (refs q)) !{}; 
  serialized_lemma h0 h1 n mods; 
  on_curve_lemma h0 h1 q (hide mods)

#reset-options

val big_step_lemma_2: h0:heap -> h1:heap -> h2:heap ->
  n:serialized -> pp:point{Distinct2 n pp} -> ppq:point{Distinct2 n ppq /\ Distinct pp ppq} -> 
   p:point{Distinct2 n p /\ Distinct p pp /\ Distinct p ppq} -> 
   pq:point{Distinct2 n pq /\ Distinct pq pp /\ Distinct pq ppq /\ Distinct pq p} -> 
   q:point{Distinct2 n q /\ Distinct q pp /\ Distinct q ppq /\ Distinct q p /\ Distinct q pq} ->  ctr:nat{ctr<=bytes_length-1} -> b:byte -> Lemma
    (requires (
      (Live h0 pp) /\ (Live h0 ppq) /\ (OnCurve h0 p) /\ (OnCurve h0 pq) /\ (OnCurve h0 q) /\ Serialized h0 n
      /\ (NtimesQ (formula_4 h0 n ctr) (pointOf h0 q) h0 p pq)
      /\ modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h0 h1
      /\ OnCurve h1 p /\ OnCurve h1 pq /\ OnCurve h1 q /\ Live h1 pp /\ Live h1 ppq
      /\ b = getValue h0 n (bytes_length-1-ctr)
      /\ NtimesQ (formula_0 (formula_4 h0 n ctr) b) (pointOf h0 q) h1 p pq
      /\ (Live h1 pp) /\ (Live h1 ppq) /\ (OnCurve h1 p) /\ (OnCurve h1 pq) /\ (OnCurve h1 q)
      /\ (OnCurve h2 p) /\ (OnCurve h2 pq) /\ Serialized h1 n
      /\ (modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h1 h2)
      /\ (NtimesQ (formula_4 h1 n (ctr+1)) (pointOf h1 q) h1 p pq)
      /\ (NtimesQ (hide (valueOfBytes h1 n)) (pointOf h1 q) h2 p pq)
    ))
    (ensures (
      (Live h0 pp) /\ (Live h0 ppq) /\ (OnCurve h0 p) /\ (OnCurve h0 pq) /\ (OnCurve h0 q)
      /\ (OnCurve h2 p) /\ (OnCurve h2 pq) /\ Serialized h0 n
      /\ (modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h0 h2)
      /\ (NtimesQ (formula_4 h0 n ctr) (pointOf h0 q) h0 p pq)
      /\ (NtimesQ (hide (valueOfBytes h0 n)) (pointOf h0 q) h2 p pq)
    ))
let big_step_lemma_2 h0 h1 h2 n pp ppq p pq q ctr b = 
  coerce
    (requires (
      (Live h0 pp) /\ (Live h0 ppq) /\ (OnCurve h0 p) /\ (OnCurve h0 pq) /\ (OnCurve h0 q) /\ Serialized h0 n
      /\ (NtimesQ (formula_4 h0 n ctr) (pointOf h0 q) h0 p pq)
      /\ modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h0 h1
      /\ OnCurve h1 p /\ OnCurve h1 pq /\ OnCurve h1 q /\ Live h1 pp /\ Live h1 ppq
      /\ b = getValue h0 n (bytes_length-1-ctr)
      /\ NtimesQ (formula_0 (formula_4 h0 n ctr) b) (pointOf h0 q) h1 p pq
      /\ (Live h1 pp) /\ (Live h1 ppq) /\ (OnCurve h1 p) /\ (OnCurve h1 pq) /\ (OnCurve h1 q)
      /\ (OnCurve h2 p) /\ (OnCurve h2 pq) /\ Serialized h1 n
      /\ (modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h1 h2)
      /\ (NtimesQ (formula_4 h1 n (ctr+1)) (pointOf h1 q) h1 p pq)
      /\ (NtimesQ (hide (valueOfBytes h1 n)) (pointOf h1 q) h2 p pq)
    ))
    (ensures (
      (Live h0 pp) /\ (Live h0 ppq) /\ (OnCurve h0 p) /\ (OnCurve h0 pq) /\ (OnCurve h0 q)
      /\ (OnCurve h2 p) /\ (OnCurve h2 pq) /\ Serialized h0 n
      /\ (modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h0 h2)
      /\ (NtimesQ (formula_4 h0 n ctr) (pointOf h0 q) h0 p pq)
      /\ (NtimesQ (hide (valueOfBytes h0 n)) (pointOf h0 q) h2 p pq)
    ))
    (fun _ -> gbig_step_lemma_2 h0 h1 h2 n pp ppq p pq q ctr b)
    
#reset-options

val big_step:
  n:serialized -> pp:point{Distinct2 n pp} -> ppq:point{Distinct2 n ppq /\ Distinct pp ppq} -> 
   p:point{Distinct2 n p /\ Distinct p pp /\ Distinct p ppq} -> 
   pq:point{Distinct2 n pq /\ Distinct pq pp /\ Distinct pq ppq /\ Distinct pq p} -> 
   q:point{Distinct2 n q /\ Distinct q pp /\ Distinct q ppq /\ Distinct q p /\ Distinct q pq} ->  ctr:nat{ctr<=bytes_length} ->
  ST unit
    (requires (fun h -> 
      (Live h pp) /\ (Live h ppq) /\ (OnCurve h p) /\ (OnCurve h pq) /\ (OnCurve h q) /\ Serialized h n
      /\ (NtimesQ (formula_4 h n ctr) (pointOf h q) h p pq)
    ))
    (ensures (fun h0 _ h1 ->
      (Live h0 pp) /\ (Live h0 ppq) /\ (OnCurve h0 p) /\ (OnCurve h0 pq) /\ (OnCurve h0 q)
      /\ (OnCurve h1 p) /\ (OnCurve h1 pq) /\ Serialized h0 n
      /\ (modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h0 h1)
      /\ (NtimesQ (formula_4 h0 n ctr) (pointOf h0 q) h0 p pq)
      /\ (NtimesQ (hide (valueOfBytes h0 n)) (pointOf h0 q) h1 p pq)
    ))
    
let rec big_step n pp ppq p pq q ctr = 
  //@@
  let h0 = ST.get() in
  match bytes_length - ctr with
  | 0 -> 
    // Trivial, but increases timeout
    admitP(True /\ reveal (formula_4 h0 n bytes_length) = valueOfBytes h0 n);
    ()
  | _ -> 
    cut(bytes_length-1-ctr>=0 /\ bytes_length-ctr-1>=0);
    let byte = index_byte n (bytes_length-1-ctr) in 
    let m = formula_4 h0 n ctr in
    // Replaces missing euclidian definitions in F*
    admitP(reveal m = reveal m * pow2 0 + (v byte / pow2 (8-0)) /\ True); 
    small_step pp ppq p pq q m 0 byte m; 
    let h1 = ST.get() in 
    big_step_lemma_1 h0 h1 n pp ppq p pq q ctr byte;
    big_step n pp ppq p pq q (ctr+1); 
    let h2 = ST.get() in 
    big_step_lemma_2 h0 h1 h2 n pp ppq p pq q ctr byte

val untouched_point_lemma: h0:heap -> h1:heap -> p:point -> q:point{Distinct p q} -> Lemma
  (requires (Live h0 p /\ modifies (refs q) h0 h1))
  (ensures  (Live h0 p /\ Live h1 p))
let untouched_point_lemma h0 h1 p q = ()

val guntouched_point_lemma_2: h0:heap -> h1:heap -> p:point -> q:point{Distinct p q} -> GLemma unit
  (requires (OnCurve h0 p /\ modifies (refs q) h0 h1))
  (ensures  (OnCurve h0 p /\ OnCurve h1 p /\ pointOf h1 p = pointOf h0 p)) []
let guntouched_point_lemma_2 h0 h1 p q =
  no_upd_lemma h0 h1 (get_x p) (refs q); 
  no_upd_lemma h0 h1 (get_y p) (refs q);
  no_upd_lemma h0 h1 (get_z p) (refs q); 
  Eval.eval_eq_lemma h0 h1 (get_x p) (get_x p) norm_length; 
  Eval.eval_eq_lemma h0 h1 (get_y p) (get_y p) norm_length; 
  Eval.eval_eq_lemma h0 h1 (get_z p) (get_z p) norm_length

val untouched_point_lemma_2: h0:heap -> h1:heap -> p:point -> q:point{Distinct p q} -> Lemma
  (requires (OnCurve h0 p /\ modifies (refs q) h0 h1))
  (ensures  (OnCurve h0 p /\ OnCurve h1 p /\ pointOf h1 p = pointOf h0 p))
let untouched_point_lemma_2 h0 h1 p q =
  coerce
    (requires (OnCurve h0 p /\ modifies (refs q) h0 h1))
    (ensures  (OnCurve h0 p /\ OnCurve h1 p /\ pointOf h1 p = pointOf h0 p))
    (fun _ -> guntouched_point_lemma_2 h0 h1 p q)

val untouched_point_lemma_3: h0:heap -> h1:heap -> p:point -> q:point{Distinct p q} -> Lemma
  (requires (Live h0 p /\ modifies !{(getRef (get_x q))} h0 h1))
  (ensures  (Live h0 p /\ Live h1 p))
let untouched_point_lemma_3 h0 h1 p q = ()

val untouched_point_lemma_4: h0:heap -> h1:heap -> p:point -> q:point{Distinct p q} -> Lemma
  (requires (OnCurve h0 p /\ modifies !{(getRef (get_x q))} h0 h1))
  (ensures  (OnCurve h0 p /\ OnCurve h1 p /\ pointOf h1 p = pointOf h0 p))
let untouched_point_lemma_4 h0 h1 p q = 
  no_upd_lemma h0 h1 (get_x p) !{(getRef (get_x q))}; 
  no_upd_lemma h0 h1 (get_y p) !{(getRef (get_x q))};
  no_upd_lemma h0 h1 (get_z p) !{(getRef (get_x q))}; 
  Eval.eval_eq_lemma h0 h1 (get_x p) (get_x p) norm_length; 
  Eval.eval_eq_lemma h0 h1 (get_y p) (get_y p) norm_length; 
  Eval.eval_eq_lemma h0 h1 (get_z p) (get_z p) norm_length

val init_points: two_p:point -> two_p_plus_q:point -> p:point -> inf:point -> q:point -> ST unit
  (requires (fun h -> Distinct two_p two_p_plus_q /\ Distinct two_p p /\ Distinct two_p inf /\ Distinct two_p q 
    /\ Distinct two_p_plus_q p /\ Distinct two_p_plus_q inf /\ Distinct two_p_plus_q q
    /\ Distinct p inf /\ Distinct p q /\ Distinct inf q /\ OnCurve h q
    /\ Live h two_p /\ Live h two_p_plus_q /\ Live h p /\ Live h inf /\ Live h q
    /\ (forall (i:nat). i < norm_length ==> (v (getValue h (get_y inf) i) = 0 /\ v (getValue h (get_y inf) i) = 0)) ))
  (ensures  (fun h0 _ h1 -> Live h1 two_p /\ Live h1 two_p_plus_q /\ Live h1 inf /\ Live h1 q
    /\ OnCurve h1 p /\ OnCurve h0 q /\ OnCurve h1 q /\ pointOf h1 p = pointOf h0 q
    /\ OnCurve h1 inf 
    /\ modifies (Set.union (refs p) !{getRef (get_x inf)}) h0 h1 ))
let init_points pp ppq p inf q =
  let h0 = ST.get() in
  copy p q;
  let h1 = ST.get() in
  untouched_point_lemma h0 h1 pp p;
  untouched_point_lemma h0 h1 ppq p;
  untouched_point_lemma h0 h1 inf p;
  untouched_point_lemma_2 h0 h1 q p;
  Bigint.upd_limb (get_x inf) 0 one_limb;
  let h2 = ST.get() in  
  untouched_point_lemma_3 h1 h2 pp inf;
  untouched_point_lemma_3 h1 h2 ppq inf;
  untouched_point_lemma_4 h1 h2 q inf;
  untouched_point_lemma_4 h1 h2 p inf;
  admitP(OnCurve h2 inf /\ pointOf h2 inf = Inf) // Point at infinity  

val oncurve_lemma_0: h0:heap -> h1:heap -> p:point -> Lemma
  (requires (OnCurve h0 p /\ modifies !{} h0 h1))
  (ensures  (OnCurve h0 p /\ OnCurve h1 p /\ pointOf h1 p = pointOf h0 p))
let oncurve_lemma_0 h0 h1 p = 
  Eval.eval_eq_lemma h0 h1 (get_x p) (get_x p) norm_length; 
  Eval.eval_eq_lemma h0 h1 (get_y p) (get_y p) norm_length; 
  Eval.eval_eq_lemma h0 h1 (get_z p) (get_z p) norm_length

val live_lemma_0: h0:heap -> h1:heap -> p:point -> Lemma
  (requires (Live h0 p /\ modifies !{} h0 h1))
  (ensures  (Live h0 p /\ Live h1 p))
let live_lemma_0 h0 h1 p = ()

(* 
   As for Montgomery curves for which only the "x" coordinate is used, one cannot check that a 
   point is actually on the curve, we rely on the fact that is the input secret has been properly 
   trimmed as indicated in the RFC for both Curve25519 and Curve448, is does not influence the 
   computation.
*)
val montgomery_ladder:
  res:point -> n:serialized{Distinct2 n res} -> q:point{Distinct2 n q /\ Distinct res q} ->
  ST unit
    (requires (fun h -> 
      (Live h res) /\ (Serialized h n) /\ (OnCurve h q) /\ is_Finite (pointOf h q)
    ))
    (ensures (fun h0 _ h1 -> 
      Live h0 res /\ Serialized h0 n /\ OnCurve h0 q /\ OnCurve h1 res
      /\ (modifies (refs res) h0 h1) 
      /\ (pointOf h1 res = (valueOfBytes h0 n +* (pointOf h0 q))) ))
let montgomery_ladder res n q =
  let h0 = ST.get() in
  // Build 'storage' empty but 'Live' points
  let two_p_x = create_limb norm_length in 
  let two_p_y = create_limb norm_length in
  let two_p_z = create_limb norm_length in
  let two_p =  make two_p_x two_p_y two_p_z in
  let h = ST.get() in
  cut (Distinct two_p q /\ Live h two_p);
  let two_p_plus_q_x = create_limb norm_length in
  let two_p_plus_q_y = create_limb norm_length in
  let two_p_plus_q_z = create_limb norm_length in
  let two_p_plus_q = make two_p_plus_q_x two_p_plus_q_y two_p_plus_q_z in
  let h' = ST.get() in
  cut (Distinct two_p_plus_q two_p /\ Distinct two_p_plus_q q /\ Live h' two_p_plus_q);
  // Copy of the 'q' point
  let p_x = create_limb norm_length in
  let p_y = create_limb norm_length in
  let p_z = create_limb norm_length in
  let p = make p_x p_y p_z in
  let h'' = ST.get() in
  cut (Distinct p two_p_plus_q /\ Distinct p two_p /\ Distinct p q /\ Live h'' p);
  let inf_x = create_limb norm_length in
  let inf_y = create_limb norm_length in
  let inf_z = create_limb norm_length in
  let inf = make inf_x inf_y inf_z in
  let h1 = ST.get() in
  cut (modifies !{} h'' h1); 
  cut (modifies !{} h' h1); 
  cut (modifies !{} h h1); 
  cut (modifies !{} h0 h1);
  cut (Distinct inf two_p /\ Distinct inf two_p_plus_q /\ Distinct inf p /\ Distinct inf q /\ Live h1 inf);
  oncurve_lemma_0 h0 h1 q; 
  live_lemma_0 h h1 two_p; 
  live_lemma_0 h' h1 two_p_plus_q;
  live_lemma_0 h'' h1 p; 
  init_points two_p two_p_plus_q p inf q;
  let h2 = ST.get() in
  admitP(NtimesQ (formula_4 h2 n 0) (pointOf h2 q) h2 inf p);
  admitP(Serialized h2 n);
  admit(); // Must reduce the timeout
  big_step n two_p two_p_plus_q inf p q 0;
  let h3 = ST.get() in
  admitP (Live h3 res);
  // Copy result to output
  copy res two_p
