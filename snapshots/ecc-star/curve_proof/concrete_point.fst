(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi Set --admit_fsi Parameters --admit_fsi Modulo --admit_fsi Bignum --verify_module ConcretePoint --z3rlimit 20;
    variables:MATH=../math_interfaces BIGNUM=../bignum_proof;
    other-files:FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst seq.fsi FStar.Seq.Base.fst FStar.Seq.Properties.fst FStar.Seq.fst FStar.Array.fst FStar.Ghost.fst $BIGNUM/axiomatic.fst $BIGNUM/intlib.fst $BIGNUM/lemmas.fst $BIGNUM/parameters.fsti $BIGNUM/uint.fst $BIGNUM/bigint.fst $BIGNUM/eval.fst $MATH/definitions.fst $MATH/field.fst $BIGNUM/modulo.fsti $BIGNUM/bignum.fsti $MATH/curve.fst
  --*)

module ConcretePoint

open FStar.Heap
open UInt
open Parameters
open Bigint
open Bignum
open Curve

type point = | Point: x:bigint -> y:bigint -> z:bigint -> point

val get_x: point -> Tot bigint
let get_x p = Point.x p
val get_y: point -> Tot bigint
let get_y p = Point.y p
val get_z: point -> Tot bigint
let get_z p = Point.z p

// Separation between the references of all three coordinates
opaque type SeparateCoordinates (p:point) = 
  getRef (get_x p) <> getRef (get_y p) 
  /\ getRef (get_x p) <> getRef (get_z p)
  /\ getRef (get_y p) <> getRef (get_z p)

// Point "live" in memory 'h'
opaque type Live (h:heap) (p:point) =
  Live h (get_x p) /\ Live h (get_y p) /\ Live h (get_z p)
  /\ SeparateCoordinates p

// Wellformedness of points : all its coordinates are properly normalized big integers
opaque type WellFormed (h:heap) (p:point) =
  Norm h (get_x p) /\ Norm h (get_y p) /\ Norm h (get_z p) /\ SeparateCoordinates p

val to_apoint: h:heap -> p:point{Live h p} -> GTot Curve.affine_point
let to_apoint h p = 
  Affine.p (to_affine (Projective (Proj (valueOf h (get_x p)) (valueOf h (get_y p)) (valueOf h (get_z p)))))

// Proper point located on the curve
type OnCurve (h:heap) (p:point) =
  WellFormed h p /\ CurvePoint (to_apoint h p)

val refs: p:point -> GTot (FStar.Set.set FStar.Heap.aref)
let refs p = !{getRef (get_x p), getRef (get_y p), getRef (get_z p)}

val erefs: p:point -> Tot (FStar.Ghost.erased (FStar.Set.set FStar.Heap.aref))
let erefs p = FStar.Ghost.hide !{getRef (get_x p), getRef (get_y p), getRef (get_z p)}

let op_Plus_Plus_Plus a b = FStar.Set.union a b

// Two distincts points from a memory point of view
type Distinct (a:point) (b:point) =
  Ref (getRef (get_x a)) <> Ref (getRef (get_x b)) /\ Ref (getRef (get_x a)) <> Ref (getRef (get_y b)) /\ Ref (getRef (get_x a)) <> Ref (getRef (get_z b))
  /\ Ref (getRef (get_y a)) <> Ref (getRef (get_x b)) /\ Ref (getRef (get_y a)) <> Ref (getRef (get_y b)) /\ Ref (getRef (get_y a)) <> Ref (getRef (get_z b))
  /\ Ref (getRef (get_z a)) <> Ref (getRef (get_x b)) /\ Ref (getRef (get_z a)) <> Ref (getRef (get_y b)) /\ Ref (getRef (get_z a)) <> Ref (getRef (get_z b))

assume val set_intersect_lemma: #a:Type -> x:FStar.Set.set a -> y:FStar.Set.set a -> Lemma
  (FStar.Set.intersect x y = FStar.Set.intersect y x)

val make: bigint -> bigint -> bigint -> Tot point
let make x y z = Point x y z

// Map curve points to curve points, any other to the point at infinity
val pointOf: h:heap -> p:point{OnCurve h p} -> GTot Curve.celem
let pointOf h p = 
  to_apoint h p

opaque type PartialSwap (h0:heap) (h1:heap) (is_swap:limb) (ctr:nat{ctr<=norm_length})
  (a:bigint) (b:bigint{Similar a b}) =
  Norm h0 a /\ Norm h0 b /\ Norm h1 a /\ Norm h1 b 
  /\ (forall (i:nat). {:pattern (getValue h1 a i) \/ (getValue h1 b i)} (i >= ctr /\ i < norm_length) ==>
      ((v is_swap = 0 ==> (v (getValue h1 a i) = v (getValue h0 a i) 
		         /\ v (getValue h1 b i) = v (getValue h0 b i)))
       /\ (v is_swap = IntLib.pow2 platform_size - 1 ==> (v (getValue h1 a i) = v (getValue h0 b i) 
						       /\ v (getValue h1 b i) = v (getValue h0 a i)))))

val swap_conditional_aux': a:bigint -> b:bigint{Similar a b} ->
  is_swap:UInt.limb{v is_swap = IntLib.pow2 platform_size -1 \/ v is_swap = 0} -> 
  ctr:nat{ctr<=norm_length} -> ST unit
    (requires (fun h -> Norm h a /\ Norm h b))
    (ensures (fun h0 _ h1 -> modifies !{getRef a, getRef b} h0 h1
      /\ Norm h0 a /\ Norm h0 b /\ Norm h1 a /\ Norm h1 b
      /\ EqSub h0 a 0 h1 a 0 ctr /\ EqSub h0 b 0 h1 b 0 ctr
      /\ PartialSwap h0 h1 is_swap ctr a b))
let rec swap_conditional_aux' a b swap ctr =
  //@@
  let h0 = ST.get() in
  match norm_length - ctr with
  | 0 -> ()
  | _ ->
    cut (True /\ ctr < norm_length); 
    let ai = Bigint.index_limb a ctr in 
    let bi = Bigint.index_limb b ctr in 
    let y = log_xor_limb ai bi in 
    let x = log_and_limb swap y in
    let ai' = log_xor_limb x ai in
    let bi' = log_xor_limb x bi in
    // Definition of the bitwise operations
    admitP (v swap = 0 ==> (v ai' = v ai /\ v bi' = v bi));
    admitP (v swap = IntLib.pow2 platform_size - 1 ==> (v ai' = v bi /\ v bi' = v ai)); 
    // ---
    Bigint.upd_limb a ctr ai'; 
    let h2 = ST.get() in
    Bigint.upd_limb b ctr bi'; 
    let h3 = ST.get() in 
    upd_lemma h0 h2 a ctr ai'; 
    no_upd_lemma h0 h2 b !{getRef a}; 
    upd_lemma h2 h3 b ctr bi';  
    no_upd_lemma h2 h3 a !{getRef b}; 
    swap_conditional_aux' a b swap (ctr+1); 
    let h1 = ST.get() in
    cut (forall (i:nat). (i >= ctr + 1 /\ i < norm_length) ==> 
      ((v swap = 0 ==> (v (getValue h1 a i) = v (getValue h0 a i) 
	         /\ v (getValue h1 b i) = v (getValue h0 b i)))
       /\ (v swap = IntLib.pow2 platform_size - 1 ==> (v (getValue h1 a i) = v (getValue h0 b i) 
					       /\ v (getValue h1 b i) = v (getValue h0 a i)))));
    cut (forall (i:nat). {:pattern (getValue h1 a i) \/ (getValue h1 b i)} 0+i = i); 
    cut (forall (i:nat). {:pattern (getValue h1 a i)} i < ctr ==> v (getValue h1 a i) = v (getValue h3 a i)); 
    cut (forall (i:nat). {:pattern (getValue h1 b i)} i < ctr ==> v (getValue h1 b i) = v (getValue h3 b i));
    ()

#reset-options

opaque val gswap_conditional_aux_lemma: h0:heap -> h1:heap -> a:bigint -> b:bigint{Similar a b} ->
  is_swap:UInt.limb{v is_swap = IntLib.pow2 platform_size -1 \/ v is_swap = 0} -> 
  GLemma unit
    (requires (PartialSwap h0 h1 is_swap 0 a b))
    (ensures (Norm h0 a /\ Norm h1 a /\ Norm h0 b /\ Norm h1 b 
      /\ (v is_swap = 0 ==> ((valueOf h1 a = valueOf h0 a) /\ (valueOf h1 b = valueOf h0 b)))
      /\ (v is_swap = IntLib.pow2 platform_size - 1 ==> 
  	  ((valueOf h1 a = valueOf h0 b) /\ (valueOf h1 b = valueOf h0 a))) )) []
let rec gswap_conditional_aux_lemma h0 h1 a b swap =
  //@@
  if (v swap = 0) then (Eval.eval_eq_lemma h0 h1 a a norm_length; Eval.eval_eq_lemma h0 h1 b b norm_length)
  else (Eval.eval_eq_lemma h0 h1 a b norm_length; Eval.eval_eq_lemma h0 h1 b a norm_length)

val swap_conditional_aux_lemma: h0:heap -> h1:heap -> a:bigint -> b:bigint{Similar a b} ->
  is_swap:UInt.limb{v is_swap = IntLib.pow2 platform_size -1 \/ v is_swap = 0} -> 
  Lemma
    (requires (PartialSwap h0 h1 is_swap 0 a b))
    (ensures (Norm h0 a /\ Norm h1 a /\ Norm h0 b /\ Norm h1 b 
      /\ (v is_swap = 0 ==> ((valueOf h1 a = valueOf h0 a) /\ (valueOf h1 b = valueOf h0 b)))
      /\ (v is_swap = IntLib.pow2 platform_size - 1 ==> 
  	  ((valueOf h1 a = valueOf h0 b) /\ (valueOf h1 b = valueOf h0 a))) ))
let swap_conditional_aux_lemma h0 h1 a b is_swap =
  coerce
    (requires (PartialSwap h0 h1 is_swap 0 a b))
    (ensures (Norm h0 a /\ Norm h1 a /\ Norm h0 b /\ Norm h1 b 
      /\ (v is_swap = 0 ==> ((valueOf h1 a = valueOf h0 a) /\ (valueOf h1 b = valueOf h0 b)))
      /\ (v is_swap = IntLib.pow2 platform_size - 1 ==> 
   	  ((valueOf h1 a = valueOf h0 b) /\ (valueOf h1 b = valueOf h0 a))) ))
    (fun _ -> gswap_conditional_aux_lemma h0 h1 a b is_swap)

#reset-options

val swap_conditional_aux: a:bigint -> b:bigint{Similar a b} ->
  is_swap:UInt.limb{v is_swap = IntLib.pow2 platform_size -1 \/ v is_swap = 0} -> 
  ctr:nat{ctr<=norm_length} -> ST unit
    (requires (fun h -> Norm h a /\ Norm h b))
    (ensures (fun h0 _ h1 -> modifies !{getRef a, getRef b} h0 h1
      /\ Norm h0 a /\ Norm h0 b /\ Norm h1 a /\ Norm h1 b
      /\ (v is_swap = 0 ==> ((valueOf h1 a = valueOf h0 a) /\ (valueOf h1 b = valueOf h0 b)))
      /\ (v is_swap = IntLib.pow2 platform_size - 1 ==> 
  	  ((valueOf h1 a = valueOf h0 b) /\ (valueOf h1 b = valueOf h0 a))) ))
let rec swap_conditional_aux a b swap ctr =
  let h0 = ST.get() in
  swap_conditional_aux' a b swap 0; 
  let h1 = ST.get() in 
  swap_conditional_aux_lemma h0 h1 a b swap  

#reset-options

val norm_lemma: h0:heap -> h1:heap -> b:bigint{Norm h0 b} -> mods:FStar.Set.set aref ->
  Lemma (requires (modifies mods h0 h1 /\ not(FStar.Set.mem (Ref (getRef b)) mods)))
	(ensures (Norm h1 b /\ valueOf h1 b = valueOf h0 b))
let norm_lemma h0 h1 b mods =
  //@@
  Eval.eval_eq_lemma h0 h1 b b norm_length

open FStar.Ghost

val enorm_lemma: h0:heap -> h1:heap -> b:bigint{Norm h0 b} -> mods:erased (FStar.Set.set aref) ->
  Lemma (requires (modifies (reveal mods) h0 h1 /\ not(FStar.Set.mem (Ref (getRef b)) (reveal mods))))
	(ensures (Norm h1 b /\ valueOf h1 b = valueOf h0 b))
let enorm_lemma h0 h1 b mods =
  //@@
  Eval.eval_eq_lemma h0 h1 b b norm_length

#reset-options

val swap_is_on_curve: h0:heap -> h3:heap -> a:point -> b:point{Distinct a b} -> 
  is_swap:UInt.limb{v is_swap = IntLib.pow2 platform_size - 1 \/ v is_swap = 0} -> Lemma
    (requires (WellFormed h0 a /\ WellFormed h0 b /\ WellFormed h3 a /\ WellFormed h3 b
	      /\ (v is_swap = 0 ==> 
	   (valueOf h3 (get_x a) = valueOf h0 (get_x a) 
	   /\ valueOf h3 (get_y a) = valueOf h0 (get_y a)
	   /\ valueOf h3 (get_z a) = valueOf h0 (get_z a)
	   /\ valueOf h3 (get_x b) = valueOf h0 (get_x b)
	   /\ valueOf h3 (get_y b) = valueOf h0 (get_y b)
	   /\ valueOf h3 (get_z b) = valueOf h0 (get_z b)))
	 /\ (v is_swap = IntLib.pow2 platform_size - 1 ==> 
	   (valueOf h3 (get_x a) = valueOf h0 (get_x b) 
	   /\ valueOf h3 (get_y a) = valueOf h0 (get_y b)
	   /\ valueOf h3 (get_z a) = valueOf h0 (get_z b)
	   /\ valueOf h3 (get_x b) = valueOf h0 (get_x a)
	   /\ valueOf h3 (get_y b) = valueOf h0 (get_y a)
	   /\ valueOf h3 (get_z b) = valueOf h0 (get_z a))) ))
  (ensures ((OnCurve h0 a /\ OnCurve h0 b) ==> (OnCurve h3 a /\ OnCurve h3 b)))
let swap_is_on_curve h0 h3 a b is_swap = 
  //@@
  ()

#reset-options
opaque val gswap_conditional_lemma: h0:heap -> h1:heap -> h2:heap -> h3:heap -> a:point -> b:point{Distinct a b} -> is_swap:UInt.limb{v is_swap = IntLib.pow2 platform_size -1 \/ v is_swap = 0} ->
  GLemma unit (requires (OnCurve h0 a /\ OnCurve h0 b /\ modifies !{getRef (get_x a), getRef (get_x b)} h0 h1
           /\ modifies !{getRef (get_y a), getRef (get_y b)} h1 h2
	   /\ modifies !{getRef (get_z a), getRef (get_z b)} h2 h3
	   /\ Norm h1 (get_x a) /\ Norm h1 (get_x b) /\ Norm h1 (get_y a) /\ Norm h1 (get_y b)
	   /\ Norm h2 (get_y a) /\ Norm h2 (get_y b) /\ Norm h2 (get_z a) /\ Norm h2 (get_z b)
	   /\ Norm h3 (get_z a) /\ Norm h3 (get_z b) 
	   /\ (v is_swap = 0 ==> 
	   	   (valueOf h1 (get_x a) = valueOf h0 (get_x a) 
		   /\ valueOf h2 (get_y a) = valueOf h1 (get_y a) 
		   /\ valueOf h3 (get_z a) = valueOf h2 (get_z a) 
		   /\ valueOf h1 (get_x b) = valueOf h0 (get_x b)
		   /\ valueOf h2 (get_y b) = valueOf h1 (get_y b)
		   /\ valueOf h3 (get_z b) = valueOf h2 (get_z b)))
	   /\ (v is_swap = IntLib.pow2 platform_size - 1 ==>
	           (valueOf h1 (get_x a) = valueOf h0 (get_x b) 
		   /\ valueOf h2 (get_y a) = valueOf h1 (get_y b)
		   /\ valueOf h3 (get_z a) = valueOf h2 (get_z b)
		   /\ valueOf h1 (get_x b) = valueOf h0 (get_x a)
		   /\ valueOf h2 (get_y b) = valueOf h1 (get_y a)
		   /\ valueOf h3 (get_z b) = valueOf h2 (get_z a)))
	))
	(ensures (OnCurve h0 a /\ OnCurve h0 b /\ OnCurve h3 a /\ OnCurve h3 b
	  /\ modifies (refs a +++ refs b) h0 h1 
	  /\ (v is_swap = 0 ==> 
	    ((pointOf h3 a) == (pointOf h0 a) /\ (pointOf h3 b) == (pointOf h0 b)))
	  /\ (v is_swap = IntLib.pow2 platform_size - 1 ==> 
  	    ((pointOf h3 a) == (pointOf h0 b) /\ (pointOf h3 b) == (pointOf h0 a))) 
	)) []
let gswap_conditional_lemma h0 h1 h2 h3 a b is_swap = 
  //@@
  let set01 = !{getRef (get_x a), getRef (get_x b)} in
  let set02 = !{getRef (get_x a), getRef (get_x b), getRef (get_y a), getRef (get_y b)} in
  let set12 = !{getRef (get_y a), getRef (get_y b)} in
  let set13 = !{getRef (get_y a), getRef (get_y b), getRef (get_z a), getRef (get_z b)} in
  let set23 = !{getRef (get_z a), getRef (get_z b)} in
  let set03 = !{getRef (get_x a), getRef (get_x b), getRef (get_y a), getRef (get_y b), getRef (get_z a), getRef (get_z b)} in
  cut (modifies set03 h0 h3); 
  FStar.Set.lemma_equal_intro set03 (refs a +++ refs b);
  cut (modifies set02 h0 h2);
  cut (modifies set13 h1 h3);
  cut (not(FStar.Set.mem (Ref (getRef (get_x a))) set13)
       /\ not(FStar.Set.mem (Ref (getRef (get_x b))) set13)); 
  cut (not(FStar.Set.mem (Ref (getRef (get_z a))) set02)
       /\ not(FStar.Set.mem (Ref (getRef (get_z b))) set02)); 
  norm_lemma h1 h3 (get_x a) set13;
  norm_lemma h1 h3 (get_x b) set13; 
  norm_lemma h0 h1 (get_y a) set01;
  norm_lemma h0 h1 (get_y b) set01; 
  norm_lemma h2 h3 (get_y a) set23;
  norm_lemma h2 h3 (get_y b) set23; 
  norm_lemma h0 h2 (get_z a) set02;
  norm_lemma h0 h2 (get_z b) set02; 
  cut(v is_swap = 0 ==> 
	   (valueOf h3 (get_x a) = valueOf h0 (get_x a) 
	   /\ valueOf h3 (get_y a) = valueOf h0 (get_y a)
	   /\ valueOf h3 (get_z a) = valueOf h0 (get_z a)
	   /\ valueOf h3 (get_x b) = valueOf h0 (get_x b)
	   /\ valueOf h3 (get_y b) = valueOf h0 (get_y b)
	   /\ valueOf h3 (get_z b) = valueOf h0 (get_z b)));
  cut(v is_swap = IntLib.pow2 platform_size - 1 ==> 
	   (valueOf h3 (get_x a) = valueOf h0 (get_x b) 
	   /\ valueOf h3 (get_y a) = valueOf h0 (get_y b)
	   /\ valueOf h3 (get_z a) = valueOf h0 (get_z b)
	   /\ valueOf h3 (get_x b) = valueOf h0 (get_x a)
	   /\ valueOf h3 (get_y b) = valueOf h0 (get_y a)
	   /\ valueOf h3 (get_z b) = valueOf h0 (get_z a)));	 
  swap_is_on_curve h0 h3 a b is_swap;
  ()

#reset-options

val swap_conditional_lemma: h0:heap -> h1:heap -> h2:heap -> h3:heap -> a:point -> b:point{Distinct a b} -> is_swap:UInt.limb{v is_swap = IntLib.pow2 platform_size -1 \/ v is_swap = 0} ->
  Lemma (requires (OnCurve h0 a /\ OnCurve h0 b /\ modifies !{getRef (get_x a), getRef (get_x b)} h0 h1
           /\ modifies !{getRef (get_y a), getRef (get_y b)} h1 h2
	   /\ modifies !{getRef (get_z a), getRef (get_z b)} h2 h3
	   /\ Norm h1 (get_x a) /\ Norm h1 (get_x b) /\ Norm h1 (get_y a) /\ Norm h1 (get_y b)
	   /\ Norm h2 (get_y a) /\ Norm h2 (get_y b) /\ Norm h2 (get_z a) /\ Norm h2 (get_z b)
	   /\ Norm h3 (get_z a) /\ Norm h3 (get_z b) 
	   /\ (v is_swap = 0 ==> 
	   	   (valueOf h1 (get_x a) = valueOf h0 (get_x a) 
		   /\ valueOf h2 (get_y a) = valueOf h1 (get_y a) 
		   /\ valueOf h3 (get_z a) = valueOf h2 (get_z a) 
		   /\ valueOf h1 (get_x b) = valueOf h0 (get_x b)
		   /\ valueOf h2 (get_y b) = valueOf h1 (get_y b)
		   /\ valueOf h3 (get_z b) = valueOf h2 (get_z b)))
	   /\ (v is_swap = IntLib.pow2 platform_size - 1 ==>
	           (valueOf h1 (get_x a) = valueOf h0 (get_x b) 
		   /\ valueOf h2 (get_y a) = valueOf h1 (get_y b)
		   /\ valueOf h3 (get_z a) = valueOf h2 (get_z b)
		   /\ valueOf h1 (get_x b) = valueOf h0 (get_x a)
		   /\ valueOf h2 (get_y b) = valueOf h1 (get_y a)
		   /\ valueOf h3 (get_z b) = valueOf h2 (get_z a)))
	))
	(ensures (OnCurve h0 a /\ OnCurve h0 b /\ OnCurve h3 a /\ OnCurve h3 b
	  /\ modifies (refs a +++ refs b) h0 h1 
	  /\ (v is_swap = 0 ==> 
	    ((pointOf h3 a) == (pointOf h0 a) /\ (pointOf h3 b) == (pointOf h0 b)))
	  /\ (v is_swap = IntLib.pow2 platform_size - 1 ==> 
  	    ((pointOf h3 a) == (pointOf h0 b) /\ (pointOf h3 b) == (pointOf h0 a))) 
	))
let swap_conditional_lemma h0 h1 h2 h3 a b is_swap = 
  coerce 
    (requires (OnCurve h0 a /\ OnCurve h0 b /\ modifies !{getRef (get_x a), getRef (get_x b)} h0 h1
           /\ modifies !{getRef (get_y a), getRef (get_y b)} h1 h2
	   /\ modifies !{getRef (get_z a), getRef (get_z b)} h2 h3
	   /\ Norm h1 (get_x a) /\ Norm h1 (get_x b) /\ Norm h1 (get_y a) /\ Norm h1 (get_y b)
	   /\ Norm h2 (get_y a) /\ Norm h2 (get_y b) /\ Norm h2 (get_z a) /\ Norm h2 (get_z b)
	   /\ Norm h3 (get_z a) /\ Norm h3 (get_z b) 
	   /\ (v is_swap = 0 ==> 
	   	   (valueOf h1 (get_x a) = valueOf h0 (get_x a) 
		   /\ valueOf h2 (get_y a) = valueOf h1 (get_y a) 
		   /\ valueOf h3 (get_z a) = valueOf h2 (get_z a) 
		   /\ valueOf h1 (get_x b) = valueOf h0 (get_x b)
		   /\ valueOf h2 (get_y b) = valueOf h1 (get_y b)
		   /\ valueOf h3 (get_z b) = valueOf h2 (get_z b)))
	   /\ (v is_swap = IntLib.pow2 platform_size - 1 ==>
	           (valueOf h1 (get_x a) = valueOf h0 (get_x b) 
		   /\ valueOf h2 (get_y a) = valueOf h1 (get_y b)
		   /\ valueOf h3 (get_z a) = valueOf h2 (get_z b)
		   /\ valueOf h1 (get_x b) = valueOf h0 (get_x a)
		   /\ valueOf h2 (get_y b) = valueOf h1 (get_y a)
		   /\ valueOf h3 (get_z b) = valueOf h2 (get_z a)))
	))
	(ensures (OnCurve h0 a /\ OnCurve h0 b /\ OnCurve h3 a /\ OnCurve h3 b
	  /\ modifies (refs a +++ refs b) h0 h1 
	  /\ (v is_swap = 0 ==> 
	    ((pointOf h3 a) == (pointOf h0 a) /\ (pointOf h3 b) == (pointOf h0 b)))
	  /\ (v is_swap = IntLib.pow2 platform_size - 1 ==> 
  	    ((pointOf h3 a) == (pointOf h0 b) /\ (pointOf h3 b) == (pointOf h0 a))) 
	))
  (fun _ -> gswap_conditional_lemma h0 h1 h2 h3 a b is_swap)

#reset-options

val swap_conditional: 
  a:point -> b:point{Distinct a b} -> 
  is_swap:UInt.limb{v is_swap = IntLib.pow2 platform_size -1 \/ v is_swap = 0} ->
  ST unit
    (requires (fun h -> OnCurve h a /\ OnCurve h b))
    (ensures (fun h0 _ h1 -> (OnCurve h0 a /\ OnCurve h0 b) /\ (OnCurve h1 a /\ OnCurve h1 b)
      /\ modifies (refs a +++ refs b) h0 h1 
      /\ (v is_swap = 0 ==> 
	  ((pointOf h1 a) == (pointOf h0 a) /\ (pointOf h1 b) == (pointOf h0 b)))
      /\ (v is_swap = IntLib.pow2 platform_size - 1 ==> 
  	  ((pointOf h1 a) == (pointOf h0 b) /\ (pointOf h1 b) == (pointOf h0 a))) ))
let swap_conditional a b is_swap =
  //@@
  let h0 = ST.get() in
  swap_conditional_aux (get_x a) (get_x b) is_swap 0;
  let h1 = ST.get() in
  norm_lemma h0 h1 (get_y a) !{getRef (get_x a), getRef (get_x b)};
  norm_lemma h0 h1 (get_y b) !{getRef (get_x a), getRef (get_x b)};
  swap_conditional_aux (get_y a) (get_y b) is_swap 0;
  let h2 = ST.get() in
  let mods = (hide !{getRef (get_x a), getRef (get_x b), getRef (get_y a), getRef (get_y b)}) in
  cut(modifies (reveal mods) h0 h2); 
  cut(not(FStar.Set.mem (Ref (getRef (get_z b))) (reveal mods)) /\ not(FStar.Set.mem (Ref (getRef (get_z a))) (reveal mods))); 
  enorm_lemma h0 h2 (get_z a) mods;
  enorm_lemma h0 h2 (get_z b) mods;
  swap_conditional_aux (get_z a) (get_z b) is_swap 0;
  let h3 = ST.get() in
  swap_conditional_lemma h0 h1 h2 h3 a b is_swap

#reset-options

val bignum_live_lemma: h0:heap -> h1:heap -> b:bigint{Bignum.Live h0 b} -> mods:FStar.Set.set aref ->
  Lemma (requires (modifies mods h0 h1 /\ not(FStar.Set.mem (Ref (getRef b)) mods)))
	(ensures (Bignum.Live h1 b))
let bignum_live_lemma h0 h1 b mods = ()

#reset-options

val norm_lemma_2: h0:heap -> h1:heap -> a:bigint -> b:bigint{getTemplate a = getTemplate b} ->
  Lemma (requires (EqSub h0 a 0 h1 b 0 norm_length /\ Norm h0 a))
        (ensures (Norm h1 b))
let norm_lemma_2 h0 h1 a b = 
  //@@
  cut(forall (i:nat). {:pattern (getValue h1 b i)} 0+i = i); 
  cut (forall (i:nat). i < norm_length ==> v (getValue h1 b i) = v (getValue h0 a i))

val glemma_copy_0: h0:heap -> h1:heap -> a:point -> b:point{Distinct a b} -> GLemma unit
  (requires (OnCurve h0 b /\ modifies (refs a) h0 h1))
  (ensures  (OnCurve h0 b /\ OnCurve h1 b /\ pointOf h1 b = pointOf h0 b)) []
let glemma_copy_0 h0 h1 a b =
  //@@
  no_upd_lemma h0 h1 (get_x b) (refs a);
  no_upd_lemma h0 h1 (get_y b) (refs a);
  no_upd_lemma h0 h1 (get_z b) (refs a);
  Eval.eval_eq_lemma h0 h1 (get_x b) (get_x b) norm_length;
  Eval.eval_eq_lemma h0 h1 (get_y b) (get_y b) norm_length;
  Eval.eval_eq_lemma h0 h1 (get_z b) (get_z b) norm_length

val lemma_copy_0: h0:heap -> h1:heap -> a:point -> b:point{Distinct a b} -> Lemma
  (requires (OnCurve h0 b /\ modifies (refs a) h0 h1))
  (ensures  (OnCurve h0 b /\ OnCurve h1 b /\ pointOf h1 b = pointOf h0 b))
let lemma_copy_0 h0 h1 a b = 
  coerce 
    (requires (OnCurve h0 b /\ modifies (refs a) h0 h1))
  (ensures  (OnCurve h0 b /\ OnCurve h1 b /\ pointOf h1 b = pointOf h0 b))
    (fun _ -> glemma_copy_0 h0 h1 a b)

#reset-options

val lemma_copy_2: h0:heap -> h1:heap -> a:point -> b:point{Distinct a b} -> Lemma
  (requires (OnCurve h0 b
    /\ modifies !{getRef (get_x a)} h0 h1 /\ EqSub h1 (get_x a) 0 h0 (get_x b) 0 norm_length))
  (ensures  (OnCurve h1 b /\ OnCurve h0 b
    /\ valueOf h1 (get_x b) = valueOf h0 (get_x b)
    /\ valueOf h1 (get_y b) = valueOf h0 (get_y b)
    /\ valueOf h1 (get_z b) = valueOf h0 (get_z b) ))
let lemma_copy_2 h0 h1 a b =
  no_upd_lemma h0 h1 (get_x b) !{getRef (get_x a)};
  no_upd_lemma h0 h1 (get_y b) !{getRef (get_x a)};
  no_upd_lemma h0 h1 (get_z b) !{getRef (get_x a)};
  Eval.eval_eq_lemma h0 h1 (get_x b) (get_x b) norm_length;
  Eval.eval_eq_lemma h0 h1 (get_y b) (get_y b) norm_length;
  Eval.eval_eq_lemma h0 h1 (get_z b) (get_z b) norm_length

val lemma_copy_3: h0:heap -> h1:heap -> a:point -> b:point{Distinct a b} -> Lemma
  (requires (OnCurve h0 b
    /\ modifies !{getRef (get_y a)} h0 h1 /\ EqSub h1 (get_y a) 0 h0 (get_y b) 0 norm_length))
  (ensures  (OnCurve h1 b /\ OnCurve h0 b
    /\ valueOf h1 (get_x b) = valueOf h0 (get_x b)
    /\ valueOf h1 (get_y b) = valueOf h0 (get_y b)
    /\ valueOf h1 (get_z b) = valueOf h0 (get_z b) ))
let lemma_copy_3 h0 h1 a b =
  no_upd_lemma h0 h1 (get_x b) !{getRef (get_y a)};
  no_upd_lemma h0 h1 (get_y b) !{getRef (get_y a)};
  no_upd_lemma h0 h1 (get_z b) !{getRef (get_y a)};
  Eval.eval_eq_lemma h0 h1 (get_x b) (get_x b) norm_length;
  Eval.eval_eq_lemma h0 h1 (get_y b) (get_y b) norm_length;
  Eval.eval_eq_lemma h0 h1 (get_z b) (get_z b) norm_length

val lemma_copy_4: h0:heap -> h1:heap -> a:point -> b:point{Distinct a b} -> Lemma
  (requires (OnCurve h0 b
    /\ modifies !{getRef (get_z a)} h0 h1 /\ EqSub h1 (get_z a) 0 h0 (get_z b) 0 norm_length))
  (ensures  (OnCurve h1 b /\ OnCurve h0 b
    /\ valueOf h1 (get_x b) = valueOf h0 (get_x b)
    /\ valueOf h1 (get_y b) = valueOf h0 (get_y b)
    /\ valueOf h1 (get_z b) = valueOf h0 (get_z b) ))
let lemma_copy_4 h0 h1 a b =
  no_upd_lemma h0 h1 (get_x b) !{getRef (get_z a)};
  no_upd_lemma h0 h1 (get_y b) !{getRef (get_z a)};
  no_upd_lemma h0 h1 (get_z b) !{getRef (get_z a)};
  Eval.eval_eq_lemma h0 h1 (get_x b) (get_x b) norm_length;
  Eval.eval_eq_lemma h0 h1 (get_y b) (get_y b) norm_length;
  Eval.eval_eq_lemma h0 h1 (get_z b) (get_z b) norm_length

val lemma_copy_5: h0:heap -> h1:heap -> h2:heap -> h3:heap -> a:point -> b:point{Distinct a b} -> Lemma
  (requires (OnCurve h0 b /\ OnCurve h1 b /\ OnCurve h2 b /\ Live h1 a /\ Live h2 a /\ Live h3 a
    /\ EqSub h0 (get_x b) 0 h1 (get_x a) 0 norm_length
    /\ EqSub h2 (get_y a) 0 h1 (get_y b) 0 norm_length
    /\ EqSub h3 (get_z a) 0 h2 (get_z b) 0 norm_length ))
  (ensures (Live h1 a /\ OnCurve h0 b /\ Live h2 a /\ OnCurve h1 b /\ Live h3 a /\ OnCurve h2 b 
    /\ valueOf h1 (get_x a) = valueOf h0 (get_x b)
    /\ valueOf h2 (get_y a) = valueOf h1 (get_y b)
    /\ valueOf h3 (get_z a) = valueOf h2 (get_z b) ))
let lemma_copy_5 h0 h1 h2 h3 bb aa =
  let b = get_x bb in let a = get_x aa in
  cut(forall (i:nat). {:pattern (0+i)} 0+i = i);
  cut(forall (i:nat). {:pattern (v (getValue h1 b i))} i < norm_length ==> v (getValue h1 b (0+i)) = v (getValue h0 a (0+i)));
  cut(forall (i:nat). {:pattern (v (getValue h1 b i))} i < norm_length ==> v (getValue h1 b (i)) = v (getValue h0 a (i)));
  let b = get_y bb in let a = get_y aa in
  cut(forall (i:nat). {:pattern (v (getValue h2 b i))} i < norm_length ==> v (getValue h2 b (0+i)) = v (getValue h1 a (0+i))); 
  cut(forall (i:nat). {:pattern (v (getValue h2 b i))} i < norm_length ==> v (getValue h2 b (i)) = v (getValue h1 a (i))); 
  let b = get_z bb in let a = get_z aa in
  cut(forall (i:nat). {:pattern (v (getValue h3 b i))} i < norm_length ==> v (getValue h3 b (0+i)) = v (getValue h2 a (0+i))); 
  cut(forall (i:nat). {:pattern (v (getValue h3 b i))} i < norm_length ==> v (getValue h3 b (i)) = v (getValue h2 a (i)));
  Eval.eval_eq_lemma h0 h1 (get_x aa) (get_x bb) norm_length;
  Eval.eval_eq_lemma h1 h2 (get_y aa) (get_y bb) norm_length;
  Eval.eval_eq_lemma h2 h3 (get_z aa) (get_z bb) norm_length

val lemma_copy_6: h0:heap -> h1:heap -> h2:heap -> h3:heap -> a:point -> b:point{Distinct a b} -> Lemma
  (requires (Live h1 a /\ Live h2 a /\ Live h3 a /\ modifies !{getRef (get_x a)} h0 h1
    /\ modifies !{getRef (get_y a)} h1 h2
    /\ modifies !{getRef (get_z a)} h2 h3 ))
  (ensures  (Live h1 a /\ Live h2 a /\ Live h3 a
    /\ valueOf h3 (get_x a) = valueOf h1 (get_x a)
    /\ valueOf h3 (get_y a) = valueOf h2 (get_y a) ))
let lemma_copy_6 h0 h1 h2 h3 a b =
  no_upd_lemma h1 h3 (get_x a) !{getRef (get_y a), getRef (get_z a)};
  no_upd_lemma h2 h3 (get_y a) !{getRef (get_z a)};
  Eval.eval_eq_lemma h1 h3 (get_x a) (get_x a) norm_length;
  Eval.eval_eq_lemma h2 h3 (get_y a) (get_y a) norm_length

val lemma_copy_1: h0:heap -> h1:heap -> h2:heap -> h3:heap -> a:point -> b:point{Distinct a b} -> Lemma
  (requires (Live h0 a /\ OnCurve h0 b /\ Live h1 a /\ Live h2 a /\ Live h3 a
    /\ EqSub h1 (get_x a) 0 h0 (get_x b) 0 norm_length
    /\ EqSub h2 (get_y a) 0 h1 (get_y b) 0 norm_length
    /\ EqSub h3 (get_z a) 0 h2 (get_z b) 0 norm_length 
    /\ modifies !{getRef (get_x a)} h0 h1
    /\ modifies !{getRef (get_y a)} h1 h2 /\ modifies !{getRef (get_z a)} h2 h3 ))
  (ensures (OnCurve h3 a /\ OnCurve h0 b /\ pointOf h3 a = pointOf h0 b))
let lemma_copy_1 h0 h1 h2 h3 a b =
  //@@
  lemma_copy_2 h0 h1 a b;
  lemma_copy_3 h1 h2 a b;
  lemma_copy_4 h2 h3 a b;
  lemma_copy_5 h0 h1 h2 h3 a b;
  lemma_copy_6 h0 h1 h2 h3 a b;
  admitP (OnCurve h3 a)

#reset-options

val copy:
  a:point -> b:point{Distinct a b} -> 
  ST unit
    (requires (fun h -> Live h a /\ OnCurve h b))
    (ensures (fun h0 _ h1 -> 
      (Live h0 a) /\ (OnCurve h1 a) /\ (OnCurve h0 b) /\ (OnCurve h1 b)
      /\ (pointOf h1 a = pointOf h0 b) /\ (pointOf h1 b = pointOf h0 b)
      /\ (modifies (refs a) h0 h1) ))
let copy a b =
  //@@
  let h0 = ST.get() in
  Bigint.blit_limb (get_x b) (get_x a) norm_length;
  let h1 = ST.get() in 
  norm_lemma h0 h1 (get_x b) (!{getRef (get_x a)}); 
  norm_lemma h0 h1 (get_y b) (!{getRef (get_x a)}); 
  norm_lemma h0 h1 (get_z b) (!{getRef (get_x a)}); 
  bignum_live_lemma h0 h1 (get_y a) (!{getRef (get_x a)});
  bignum_live_lemma h0 h1 (get_z a) (!{getRef (get_x a)});
  Bigint.blit_limb (get_y b) (get_y a) norm_length;
  let h2 = ST.get() in
  norm_lemma h1 h2 (get_x b) (!{getRef (get_y a)}); 
  norm_lemma h1 h2 (get_y b) (!{getRef (get_y a)});
  norm_lemma h1 h2 (get_z b) (!{getRef (get_y a)}); 
  norm_lemma_2 h0 h1 (get_x b) (get_x a); 
  norm_lemma h1 h2 (get_x a) (!{getRef (get_y a)}); 
  bignum_live_lemma h1 h2 (get_z a) (!{getRef (get_y a)});
  Bigint.blit_limb (get_z b) (get_z a) norm_length;
  let h3 = ST.get() in
  norm_lemma h2 h3 (get_x b) (!{getRef (get_z a)});
  norm_lemma h2 h3 (get_y b) (!{getRef (get_z a)});
  norm_lemma h2 h3 (get_z b) (!{getRef (get_z a)});
  norm_lemma h2 h3 (get_x a) (!{getRef (get_z a)});
  norm_lemma_2 h1 h2 (get_y b) (get_y a); 
  norm_lemma h2 h3 (get_y a) (!{getRef (get_z a)}); 
  norm_lemma_2 h2 h3 (get_z b) (get_z a);
  cut (modifies (refs a) h0 h3 );
  lemma_copy_0 h0 h3 a b; 
  lemma_copy_1 h0 h1 h2 h3 a b
  
val swap:
  a:point -> b:point{Distinct a b} ->
  ST unit
    (requires (fun h -> OnCurve h a /\ Live h b))
    (ensures (fun h0 _ h1 -> OnCurve h0 a /\ Live h0 b /\ OnCurve h1 b /\ Live h1 a 
      /\ (pointOf h0 a) == (pointOf h1 b)
      /\ modifies (FStar.Set.union (refs a) (refs b)) h0 h1))
let swap a b = 
  copy b a

opaque val gon_curve_lemma: h0:heap -> h1:heap -> a:point -> mods:FStar.Ghost.erased (FStar.Set.set aref) -> GLemma unit
  (requires (OnCurve h0 a /\ modifies (reveal mods) h0 h1 /\ FStar.Set.intersect (reveal mods) (refs a) = !{}))
  (ensures (OnCurve h0 a /\ OnCurve h1 a /\ pointOf h1 a = pointOf h0 a)) []
let gon_curve_lemma h0 h1 a mods = 
  //@@
  cut(True /\ FStar.Set.mem (Ref (getRef (get_x a))) (refs a));
  cut(True /\ FStar.Set.mem (Ref (getRef (get_y a))) (refs a));
  cut(True /\ FStar.Set.mem (Ref (getRef (get_z a))) (refs a));
  norm_lemma h0 h1 (get_x a) (reveal mods);
  norm_lemma h0 h1 (get_y a) (reveal mods);
  norm_lemma h0 h1 (get_z a) (reveal mods); 
  Eval.eval_eq_lemma h0 h1 (get_x a) (get_x a) norm_length;
  Eval.eval_eq_lemma h0 h1 (get_y a) (get_y a) norm_length;
  Eval.eval_eq_lemma h0 h1 (get_z a) (get_z a) norm_length

#reset-options

val on_curve_lemma: h0:heap -> h1:heap -> a:point -> mods:FStar.Ghost.erased (FStar.Set.set aref) -> Lemma
  (requires (OnCurve h0 a /\ modifies (reveal mods) h0 h1 /\ FStar.Set.intersect (reveal mods) (refs a) = !{}))
  (ensures (OnCurve h0 a /\ OnCurve h1 a /\ pointOf h1 a = pointOf h0 a))
let on_curve_lemma h0 h1 a mods =
  coerce 
     (requires (OnCurve h0 a /\ modifies (reveal mods) h0 h1 /\ FStar.Set.intersect (reveal mods) (refs a) = !{}))
     (ensures (OnCurve h0 a /\ OnCurve h1 a /\ pointOf h1 a = pointOf h0 a))
     (fun _ -> gon_curve_lemma h0 h1 a mods)

opaque val glive_lemma: h0:heap -> h1:heap -> a:point -> mods:erased (FStar.Set.set aref) -> GLemma unit
  (requires (Live h0 a /\ modifies (reveal mods) h0 h1 /\ FStar.Set.intersect (reveal mods) (refs a) = !{}))
  (ensures (Live h1 a)) []
let glive_lemma h0 h1 a mods = 
  //@@
  cut(True /\ FStar.Set.mem (Ref (getRef (get_x a))) (refs a));
  cut(True /\ FStar.Set.mem (Ref (getRef (get_y a))) (refs a));
  cut(True /\ FStar.Set.mem (Ref (getRef (get_z a))) (refs a))

#reset-options

val live_lemma: h0:heap -> h1:heap -> a:point -> mods:erased (FStar.Set.set aref) -> Lemma
  (requires (Live h0 a /\ modifies (reveal mods) h0 h1 /\ FStar.Set.intersect (reveal mods) (refs a) = !{}))
  (ensures (Live h1 a))
let live_lemma h0 h1 a mods = 
  coerce
    (requires (Live h0 a /\ modifies (reveal mods) h0 h1 /\ FStar.Set.intersect (reveal mods) (refs a) = !{}))
    (ensures (Live h1 a))
    (fun _ -> glive_lemma h0 h1 a mods)

#reset-options

opaque val gdistinct_lemma: a:point -> b:point{Distinct a b} -> GLemma unit (requires (True)) (ensures (FStar.Set.intersect (refs a) (refs b) = !{})) []
let gdistinct_lemma a b = 
  FStar.Set.lemma_equal_intro (FStar.Set.intersect (refs a) (refs b)) !{}

#reset-options

val distinct_lemma: a:point -> b:point{Distinct a b} -> Lemma (FStar.Set.intersect (refs a) (refs b) = !{})
let distinct_lemma a b = 
  coerce 
    (requires (True)) 
    (ensures (FStar.Set.intersect (refs a) (refs b) = !{}))
    (fun _ -> gdistinct_lemma a b)

#reset-options

val distinct_commutative: a:point -> b:point -> Lemma 
  (requires (True)) (ensures (Distinct a b <==> Distinct b a)) [SMTPat (Distinct a b)]
let distinct_commutative a b = 
  //@@
  ()

val swap_both:
  a:point -> b:point{Distinct a b} -> c:point{Distinct c a /\ Distinct c b} ->
  d:point{Distinct d a /\ Distinct d b /\ Distinct d c} ->
  ST unit
    (requires (fun h -> OnCurve h a /\ OnCurve h b /\ Live h c /\ Live h d))
    (ensures (fun h0 _ h1 -> OnCurve h0 a /\ OnCurve h0 b /\ Live h0 c /\ Live h0 d 
      /\ OnCurve h1 c /\ OnCurve h1 d /\ Live h1 a /\ Live h1 b 
      /\ (pointOf h0 a) == (pointOf h1 c) /\ (pointOf h0 b) == (pointOf h1 d)
      /\ modifies ((refs a) +++ (refs b) +++ (refs c) +++ (refs d)) h0 h1))
let swap_both a b c d =
  //@@
  let h0 = ST.get() in
  copy c a; 
  let h1 = ST.get() in
  let set01 = erefs c in 
  distinct_lemma c b; 
  distinct_lemma c d; 
  on_curve_lemma h0 h1 b set01; 
  live_lemma h0 h1 d set01; 
  copy d b;
  let h2 = ST.get() in
  distinct_lemma d c; 
  distinct_lemma d a;
  distinct_lemma d b;
  on_curve_lemma h1 h2 c (erefs d);
  live_lemma h1 h2 a (erefs d);
  live_lemma h1 h2 b (erefs d)
  
val copy2:
  p':point -> q':point{Distinct p' q'} -> 
  p:point{Distinct p p' /\ Distinct p q'} -> 
  q:point{Distinct q p' /\ Distinct q q'} -> 
  ST unit 
    (requires (fun h -> 
      (Live h p') /\ (Live h q') /\ (OnCurve h p) /\ (OnCurve h q)
    ))
    (ensures (fun h0 _ h1 ->
      (OnCurve h1 p') /\ (OnCurve h1 q') /\ (OnCurve h1 p) /\ (OnCurve h1 q) 
      /\ (OnCurve h0 p) /\ (OnCurve h0 q) 
      /\ (modifies (FStar.Set.union (refs p') (refs q')) h0 h1)
      /\ ((pointOf h1 p') == (pointOf h0 p))
      /\ ((pointOf h1 q') == (pointOf h0 q))
    ))
let copy2 p' q' p q =
  //@@
  let h0 = ST.get() in
  copy p' p; 
  let h1 = ST.get() in
  let set01 = (erefs p') in 
  distinct_lemma p' q; 
  distinct_lemma p' q'; 
  on_curve_lemma h0 h1 q set01; 
  live_lemma h0 h1 q' set01;  
  copy q' q; 
  let h2 = ST.get() in
  distinct_lemma q' p'; 
  distinct_lemma q' p;
  distinct_lemma q' q; 
  on_curve_lemma h1 h2 p' (erefs q'); 
  on_curve_lemma h1 h2 p (erefs q'); 
  on_curve_lemma h1 h2 q (erefs q')
