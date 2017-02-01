(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi Parameters --verify_module Modulo;
    other-files:FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst seq.fsi FStar.Seq.Base.fst FStar.Seq.Properties.fst FStar.Seq.fst FStar.Array.fst FStar.Ghost.fst  axiomatic.fst intlib.fst lemmas.fst parameters.fsti uint.fst bigint.fst eval.fst
  --*)

(* Placeholder *)

module Modulo

(* 64/128 bits *)

open FStar.Ghost
open FStar.Heap
open IntLib
open Parameters
open UInt
open Bigint
open Eval

let op_Bar_Amp x y = log_and_limb x y
let op_Bar_Greater_Greater x y = shift_left_wide x y
let op_Bar_Plus x y = add_wide x y
let op_Bar_Star x y = mul_wide x y

(* Set of constraints to satisfy, necessary to call the 'freduce_degree' and 'carry' functions
   consecutively *)
val satisfies_modulo_constraints: h:FStar.Heap.heap -> b:bigint_wide{live h b} -> GTot bool

val freduce_degree: b:bigint_wide -> ST unit 
  (requires (fun h -> live h b /\ satisfies_modulo_constraints h b)) 
  (ensures (fun h0 _ h1 -> live h0 b /\ live h1 b /\ satisfies_modulo_constraints h0 b
    /\ getLength h0 b >= 2*norm_length - 1
    /\ getLength h1 b = getLength h0 b /\ modifies !{getRef b} h0 h1 /\ getLength h1 b >= norm_length+1
    /\ (forall (i:nat). {:pattern (v (getValue h1 b i))} i <= norm_length ==> 
	v (getValue h1 b i) < pow2 (platform_wide - 1))
    /\ eval h1 b norm_length % reveal prime = eval h0 b (2*norm_length-1) % reveal prime))

val freduce_coefficients: b:bigint_wide{getTemplate b = templ} -> ST unit
  (requires (fun h -> live h b /\ getLength h b >= 2*norm_length-1  /\ getLength h b >= norm_length + 1
     /\ (forall (i:nat). {:pattern (v (getValue h b i))} i <= norm_length ==> 
	 v (getValue h b i) < pow2 (platform_wide -1))))
  (ensures (fun h0 _ h1 -> live h0 b /\ getLength h0 b >= 2*norm_length-1 
    /\ Standardized h1 b /\ modifies !{getRef b} h0 h1
    /\ eval h1 b norm_length % reveal prime = eval h0 b norm_length % reveal prime))

val carry: 
    b:bigint_wide{getTemplate b = templ} -> ctr:nat -> ST unit
    (requires (fun h -> live h b /\ getLength h b >= norm_length+1
      /\ (forall (i:nat). {:pattern (v (getValue h b i))} i <= norm_length ==> 
	  v (getValue h b i) < pow2 (platform_wide - 1)) ))
    (ensures (fun h0 _ h1 -> live h0 b /\ getLength h0 b >= norm_length +1
      /\ Standardized h1 b /\ modifies !{getRef b} h0 h1 /\ getLength h1 b = getLength h0 b
      /\ eval h1 b (norm_length+1) % reveal prime = eval h0 b (norm_length+1) % reveal prime))

val carry_top_to_0:
  b:bigint_wide -> ST unit (requires (fun h -> True)) (ensures (fun h0 _ h1 -> True))

val normalize:
  output:bigint -> ST unit
  (requires (fun h -> Standardized h output)) 
  (ensures (fun h0 _ h1 -> Standardized h0 output /\ Standardized h1 output
    /\ eval h0 output norm_length % reveal prime = eval h1 output norm_length % reveal prime
    /\ eval h1 output norm_length < reveal prime
    /\ modifies !{getRef output} h0 h1))

opaque type Larger (h:FStar.Heap.heap) (b:bigint) (n:pos) =
  live h b /\ getLength h b >= norm_length /\ getTemplate b = templ
  /\ (forall (i:nat). {:pattern (v (getValue h b i))} i < norm_length ==> 
      (v (getValue h b i) < pow2 n) /\ v (getValue h b i) >= pow2 (getTemplate b i))

(* Same as in parameters.fsti *)
assume val n1: n:pos{n = Parameters.ndiff /\ n <= platform_size}
assume val n0: n:pos{n = Parameters.ndiff'}

val add_big_zero:
  output:bigint -> ST unit 
    (requires (fun h -> Standardized h output)) 
    (ensures (fun h0 _ h1 -> Standardized h0 output
      /\ Filled h1 output n0 n1
      /\ eval h0 output norm_length % reveal prime = eval h1 output norm_length % reveal prime
      /\ modifies !{getRef output} h0 h1))

val sum_satisfies_constraints: h0:heap -> h1:heap -> cpy:bigint_wide{getTemplate cpy = templ} -> a:bigint -> b:bigint ->
  Lemma 
    (requires (Standardized h0 a /\ Standardized h0 b /\ live h1 cpy /\ getLength h1 cpy >= 2*norm_length-1
		/\ (forall (i:nat). i < norm_length ==> v (getValue h1 cpy i) = v (getValue h0 a i) 
							  + v (getValue h0 b i))
		/\ (forall (i:nat). (i >= norm_length /\ i < getLength h1 cpy) ==> 
		    v (getValue h1 cpy i) = 0)))
    (ensures (live h1 cpy /\ satisfies_modulo_constraints h1 cpy))

val difference_satisfies_constraints: h0:heap -> h1:heap -> cpy:bigint_wide{getTemplate cpy = templ} -> a:bigint -> b:bigint ->
  Lemma 
    (requires (Filled h0 a n0 n1 /\ Standardized h0 b /\ live h1 cpy 
      /\ getLength h1 cpy >= 2*norm_length-1
      /\ (forall (i:nat). i < norm_length ==> v (getValue h1 cpy i) = v (getValue h0 a i) - v (getValue h0 b i))
      /\ (forall (i:nat). (i >= norm_length /\ i < getLength h1 cpy) ==> v (getValue h1 cpy i) = 0) ))
    (ensures (live h1 cpy /\ satisfies_modulo_constraints h1 cpy))

val mul_satisfies_constraints: h0:heap -> h1:heap -> cpy:bigint_wide{getTemplate cpy = templ} -> a:bigint -> b:bigint ->
  Lemma 
    (requires (Standardized h0 a /\ Standardized h0 b /\ live h1 cpy /\ getLength h1 cpy >= 2*norm_length-1
      /\ maxValue h1 cpy <= norm_length * maxValueNorm h0 a * maxValueNorm h0 b))
    (ensures (live h1 cpy /\ satisfies_modulo_constraints h1 cpy))
