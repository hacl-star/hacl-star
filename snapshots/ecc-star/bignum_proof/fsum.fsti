(*--build-config
  options:--admit_fsi FStar.Seq --admit_fsi FStar.Set --admit_fsi IntLib --admit_fsi Parameters --verify_module Fsum --z3timeout 15;
  other-files:FStar.Classical.fst FStar.PredicateExtensionality.fst FStar.Set.fsi FStar.Seq.Base.fst FStar.Seq.Properties.fst FStar.Seq.fst FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Array.fst FStar.Ghost.fst axiomatic.fst intlib.fsti lemmas.fst parameters.fsti uint.fst bigint.fst eval.fst;
  --*)

module Fsum

open IntLib
open Parameters
open UInt
open FStar.Seq
open Eval
open FStar.ST
open FStar.Heap
open FStar.Ghost
open Bigint

opaque type WillNotOverflow (h:heap) 
		     (a:bigint{live h a /\ getLength h a >= norm_length}) 
		     (b:bigint{live h b /\ getLength h b >= norm_length}) 
		     (ctr:nat) =
  (forall (i:nat). {:pattern (v (getValue h a i) + v (getValue h b i))} (i >= ctr /\ i < norm_length) ==> v (getValue h a i) + v (getValue h b i) < pow2 platform_size)

opaque type NotModified (h0:heap) (h1:heap) 
			(a:bigint{live h0 a /\ live h1 a /\ getLength h0 a = getLength h1 a
			  /\ getLength h0 a >= norm_length})
			(ctr:nat) =
  (forall (i:nat). {:pattern (getValue h1 a i)}
    ((i <> ctr /\ i < getLength h0 a) ==>  getValue h1 a i == getValue h0 a i))

opaque type IsSum (h0:heap) (h1:heap) 
		  (a:bigint{live h0 a /\ live h1 a /\ getLength h0 a >= norm_length 
		    /\ getLength h0 a = getLength h1 a}) 
		  (b:bigint{live h0 b /\ getLength h0 b >= norm_length})
		  (ctr:nat) =
  (forall (i:nat). {:pattern (v (getValue h1 a i))}
	  (i>=ctr /\ i<norm_length) ==> (v (getValue h1 a i) = v (getValue h0 a i) + v (getValue h0 b i)))

opaque type NotModified2 (h0:heap) (h1:heap)
			 (a:bigint{live h0 a /\ live h1 a /\ getLength h0 a = getLength h1 a
			   /\ getLength h0 a >= norm_length})
			 (ctr:nat) =
  (forall (i:nat). {:pattern (getValue h1 a i)}
    ((i < ctr \/ i >= norm_length) /\ i < getLength h0 a) ==>  getValue h1 a i == getValue h0 a i)

val fsum_index:
  a:bigint -> b:bigint{Similar a b} -> ctr:nat{ ctr <= norm_length } ->
  ST unit
    (requires (fun h ->
      (live h a) /\ (live h b)
      /\ (norm_length <= getLength h a /\ norm_length <= getLength h b)
      /\ (forall (i:nat). (i >= ctr /\ i < norm_length) ==>
	  (v (getValue h a i) + v (getValue h b i) < pow2 platform_size))
    ))
    (ensures (fun h0 _ h1 -> 
      (live h0 a) /\ (live h0 b) /\ (live h1 a) /\ (live h1 b)
      /\ (norm_length <= getLength h0 a /\ norm_length <= getLength h0 b)
      /\ (modifies !{getRef a} h0 h1)
      /\ (getLength h0 a = getLength h1 a)
      /\ (IsSum h0 h1 a b ctr)
      /\ (NotModified2 h0 h1 a ctr)
     ))
     
val fsum':
  a:bigint -> b:bigint{Similar a b} -> ST unit
    (requires (fun h -> Standardized h a /\ Standardized h b))
    (ensures (fun h0 u h1 -> 
      Standardized h0 a /\ Standardized h0 b /\ Standardized h1 b
      /\ (live h1 a) /\ (modifies !{getRef a} h0 h1) 
      /\ (getLength h1 a = getLength h0 a) /\ (getLength h0 b = getLength h1 b)
      /\ (eval h1 a norm_length = eval h0 a norm_length + eval h0 b norm_length)
      /\ (IsSum h0 h1 a b 0)
    ))
