(*--build-config
  options:--admit_fsi FStar.Set --admit_fsi IntLib --admit_fsi Parameters --verify_module Fscalar --z3timeout 15;
  other-files:FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Seq.Base.fst FStar.Seq.Properties.fst FStar.Seq.fst FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Array.fst FStar.Ghost.fst axiomatic.fst intlib.fsti lemmas.fst parameters.fsti uint.fst bigint.fst eval.fst;
  --*)

module Fscalar

open FStar.Heap
open FStar.ST
open FStar.Seq
open Axiomatic
open IntLib
open Parameters
open UInt
open Eval
open Bigint

opaque type WillNotOverflow (h:heap) 
		     (a:bigint{live h a /\ getLength h a >= norm_length}) 
		     (s:limb) (ctr:nat) =
  (forall (i:nat). {:pattern (v (getValue h a i))}
    (i >= ctr /\ i < norm_length) ==> v (getValue h a i) * v s < pow2 platform_wide)

opaque type IsScalarProduct (h0:heap) (h1:heap) (ctr:nat) (len:nat)
		  (a:bigint{live h0 a /\ getLength h0 a >= len}) 
		  (s:limb)
		  (res:bigint_wide{live h1 res /\ getLength h1 res >= len}) =
  (forall (i:nat). {:pattern (v (getValue h1 res i))}
    (i>= ctr /\ i < len) ==> v (getValue h1 res i) = v (getValue h0 a i) * v s)

opaque type IsNotModified (h0:heap) (h1:heap) 
		   (res:bigint_wide{live h0 res /\ live h1 res /\ getLength h0 res >= norm_length
		     /\ getLength h1 res = getLength h0 res})
		   (ctr:nat) =
  (forall (i:nat). {:pattern (getValue h1 res i)}
    (i < getLength h1 res /\ (i < ctr \/ i >= norm_length)) ==>
      (getValue h1 res i == getValue h0 res i))

(* Tail recursive version of the scalar multiplication *)
val scalar_multiplication_tr:
  res:bigint_wide -> a:bigint{Similar res a} -> s:limb -> ctr:nat{ctr<=norm_length} -> 
  ST unit
     (requires (fun h -> 
       (live h res) /\ (live h a) /\ (getLength h a >= norm_length) /\ (getLength h res >= norm_length)
       /\ (WillNotOverflow h a s ctr)
     ))
     (ensures (fun h0 u h1 -> 
       (live h0 res) /\ (live h1 res) /\ (live h0 a) /\ (live h1 a)
       /\ (modifies !{getRef res} h0 h1) /\ (getLength h0 a >= norm_length)
       /\ (getLength h0 res >= norm_length) /\ (getLength h1 res = getLength h0 res)
       /\ (IsScalarProduct h0 h1 ctr norm_length a s res)
       /\ (IsNotModified h0 h1 res ctr)
       /\ (Seq.Eq (sel h0 (getRef a)) (sel h1 (getRef a)))
     ))

#reset-options

val theorem_scalar_multiplication: 
  h0:heap -> h1:heap -> a:bigint{live h0 a} -> s:limb -> len:nat{len <= getLength h0 a} ->
  b:bigint_wide{live h1 b /\ len <= getLength h1 b /\ getTemplate a = getTemplate b} ->
  Lemma 
    (requires (IsScalarProduct h0 h1 0 len a s b))
    (ensures ((eval h1 b len) = (eval h0 a len) * v s))

#reset-options

val scalar':
  res:bigint_wide{getTemplate res = templ} -> 
  a:bigint{Similar res a} -> s:limb ->  
  ST unit
     (requires (fun h -> 
       (Standardized h a) /\ (live h res) /\ (getLength h res >= getLength h a)))
     (ensures (fun h0 u h1 -> 
       (live h0 res) /\ (live h1 res) /\ (Standardized h0 a) /\ (Standardized h1 a) 
       /\ (modifies !{getRef res} h0 h1)
       /\ (getLength h0 res >= getLength h0 a)
       /\ (getLength h1 res = getLength h0 res)
       /\ (IsScalarProduct h0 h1 0 norm_length a s res)
       /\ (eval h1 res norm_length = eval h0 a norm_length * v s)
     ))
