(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi Parameters --admit_fsi Modulo --admit_fsi Bignum --admit_fsi ConcretePoint --verify_module DoubleAndAdd --lax;
    variables:MATH=../math_interfaces BIGNUM=../bignum_proof;
    other-files:FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst seq.fsi FStar.Seq.Base.fst FStar.Seq.Properties.fst FStar.Seq.fst FStar.Array.fst FStar.Ghost.fst $BIGNUM/axiomatic.fst $BIGNUM/intlib.fst $BIGNUM/lemmas.fst $BIGNUM/parameters.fsti $BIGNUM/uint.fst $BIGNUM/bigint.fst $BIGNUM/eval.fst $MATH/definitions.fst $MATH/field.fst $BIGNUM/modulo.fsti $BIGNUM/bignum.fsti $MATH/curve.fst concrete_point.fst
  --*)

module DoubleAndAdd

open FStar.Heap
open FStar.Ghost
open Parameters
open Bigint
open Bignum
open Field
open ConcretePoint

let op_Plus_Plus_Plus a b = FStar.Set.union a b

val equation_1: felem -> felem -> GTot felem
let equation_1 x2 z2 = (((x2 ^+ z2) ^^ 2) ^* ((x2 ^- z2) ^^ 2))
val equation_2: felem -> felem -> GTot felem
let equation_2 x2 z2 = ((4 +* x2 ^* z2) ^* (((x2 ^- z2) ^^ 2) ^+ (a24' +* (4 +* x2 ^* z2))))
val equation_3: felem -> felem -> felem -> felem -> GTot felem
let equation_3 x2 z2 x3 z3 = ((((x3 ^- z3) ^* (x2^+z2)) ^+ ((x3 ^+ z3) ^* (x2 ^- z2))) ^^ 2)
val equation_4: felem -> felem -> felem -> felem -> felem -> GTot felem
let equation_4 x2 z2 x3 z3 x1 = (x1 ^* (((x3 ^- z3) ^* (x2^+z2)) ^- ((x3 ^+ z3) ^* (x2 ^- z2))) ^^ 2)

val double_and_add': two_p:point -> two_p_plus_q:point -> p:point -> p_plus_q:point -> q:point ->
  ST unit
    (requires (fun h ->
      (Live h two_p) /\ (Live h two_p_plus_q) /\ (pointOf h p <> pointOf h p_plus_q)
      /\ (OnCurve h p) /\ (OnCurve h p_plus_q) /\ (OnCurve h q)
    ))
    (ensures (fun h0 _ h1 ->
      (Live h0 two_p) /\ (Live h0 two_p_plus_q)
      /\ (OnCurve h0 p) /\ (OnCurve h0 p_plus_q) /\ (OnCurve h0 q)
      /\ (OnCurve h1 two_p) /\ (OnCurve h1 two_p_plus_q)
      /\ (Live h1 p) /\ (Live h1 p_plus_q) /\ (OnCurve h1 q)
       /\ (modifies (refs two_p +++ refs two_p_plus_q +++ refs p +++ refs p_plus_q) h0 h1)
       /\ (Bignum.Live h1 (get_x q) /\ Bignum.Live h1 (get_x p) /\ Bignum.Live h1 (get_z p) 
	 /\ Bignum.Live h1 (get_x p_plus_q) 
	 /\ Bignum.Live h1 (get_z p_plus_q) /\ Bignum.Live h1 (get_x two_p) 
	 /\ Bignum.Live h1 (get_z two_p) /\ Bignum.Live h1 (get_x two_p_plus_q) 
	 /\ Bignum.Live h1 (get_z two_p_plus_q))
      /\ (
	  let x1 = valueOf h1 (get_x q) in 
	  let x2 = valueOf h1 (get_x p) in let z2 = valueOf h1 (get_z p) in
	  let x3 = valueOf h1 (get_x p_plus_q) in let z3 = valueOf h1 (get_z p_plus_q) in
	  (valueOf h1 (get_x two_p) = equation_1 x2 z2	 
//	       (((x2 ^+ z2) ^^ 2) ^* ((x2 ^- z2) ^^ 2))
	   /\ valueOf h1 (get_z two_p) = equation_2 x2 z2
//	       ((4 +* x2 ^* z2) ^* (((x2 ^- z2) ^^ 2) ^+ (a24' +* (4 +* x2 ^* z2))))
	   /\ valueOf h1 (get_x two_p_plus_q) = equation_3 x2 z2 x3 z3
//	       ((((x3 ^- z3) ^* (x2^+z2)) ^+ ((x3 ^+ z3) ^* (x2 ^- z2))) ^^ 2)
	   /\ valueOf h1 (get_z two_p_plus_q) = equation_4 x2 z2 x3 z3 x1 
//	       (x1 ^* (((x3 ^- z3) ^* (x2^+z2)) ^- ((x3 ^+ z3) ^* (x2 ^- z2))) ^^ 2)
	))
    ))    
      
let double_and_add' two_p two_p_plus_q p p_plus_q q =
  let h0 = ST.get() in
  let qmqp = get_x q in
  let x = get_x p in let z = get_z p in 
  let xprime = get_x p_plus_q in let zprime = get_z p_plus_q in
  let x2 = get_x two_p in let z2 = get_z two_p in
  let origx = create_limb norm_length in
  let origxprime = create_limb norm_length in
  let zzz = create_limb (2*norm_length-1) in
  let xx = create_limb (2*norm_length-1) in
  let zz = create_limb (2*norm_length-1) in
  let xxprime = create_limb (2*norm_length-1) in
  let zzprime = create_limb (2*norm_length-1) in
  let xxxprime = create_limb (2*norm_length-1) in
  let zzzprime = create_limb (2*norm_length-1) in  
  Bigint.blit #platform_size x origx norm_length;
  fsum x z;
  fdifference z origx; 
  Bigint.blit #platform_size xprime origxprime norm_length;
  fsum xprime zprime;
  fdifference zprime origxprime;
  fmul xxprime xprime z;
  fmul zzprime x zprime;  
  Bigint.blit #platform_size xxprime origxprime norm_length;
  fsum xxprime zzprime;
  fdifference zzprime origxprime;
  fsquare xxxprime xxprime;
  fsquare zzzprime zzprime;
  fmul zzprime zzzprime qmqp;
  Bigint.blit #platform_size xxxprime (get_x two_p_plus_q) norm_length;
  Bigint.blit #platform_size zzprime (get_z two_p_plus_q) norm_length;
  fsquare xx x;
  fsquare zz z;
  fmul x2 xx zz;
  fdifference zz xx; 
  Bignum.erase zzz norm_length (norm_length-1) 0;
  fscalar zzz zz #12 (UInt.to_limb a24);
  fsum zzz xx;
  fmul z2 zz zzz

(* Stateful double and add function on concrete points *)
val double_and_add:
  two_p:point -> two_p_plus_q:point -> p:point -> p_plus_q:point -> q:point -> 
  ST unit
    (requires (fun h -> 
      (Live h two_p) /\ (Live h two_p_plus_q) /\ (pointOf h p <> pointOf h p_plus_q)
      /\ (OnCurve h p) /\ (OnCurve h p_plus_q) /\ (OnCurve h q)
      ))
    (ensures (fun h0 _ h1 -> 
      (Live h0 two_p) /\ (Live h0 two_p_plus_q)
      /\ (OnCurve h0 p) /\ (OnCurve h0 p_plus_q) /\ (OnCurve h0 q)
      /\ (OnCurve h1 two_p) /\ (OnCurve h1 two_p_plus_q)
      /\ (Live h1 p) /\ (Live h1 p_plus_q) /\ (OnCurve h1 q)
       /\ (modifies (refs two_p +++ refs two_p_plus_q +++ refs p +++ refs p_plus_q) h0 h1)
      /\ ((pointOf h1 two_p) == (Curve.add (pointOf h0 p) (pointOf h0 p)))
      /\ ((pointOf h1 two_p_plus_q) == (Curve.add (pointOf h0 p) (pointOf h0 p_plus_q)))
    ))
let double_and_add two_p two_p_plus_q p p_plus_q q =
  double_and_add' two_p two_p_plus_q p p_plus_q q

