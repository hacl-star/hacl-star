(*--build-config
  options:--admit_fsi FStar.Seq --admit_fsi FStar.Set --admit_fsi IntLib --admit_fsi Parameters --verify_module FsumWide --z3timeout 15;
  other-files:FStar.Classical.fst FStar.PredicateExtensionality.fst FStar.Set.fsi FStar.Seq.Base.fst FStar.Seq.Properties.fst FStar.Seq.fst FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Array.fst FStar.Ghost.fst axiomatic.fst intlib.fsti lemmas.fst parameters.fsti uint.fst bigint.fst eval.fst;
  --*)

module FsumWide

open IntLib
open Parameters
open UInt
open FStar.Seq
open Eval
open FStar.ST
open FStar.Heap
open FStar.Ghost
open Bigint

opaque type WillNotOverflow 
  (h:heap) (a_idx:nat) (b_idx:nat) (len:nat) (ctr:nat)
  (a:bigint_wide{live h a /\ getLength h a >= a_idx+len})
  (b:bigint_wide{live h b /\ getLength h b >= b_idx+len}) = 
    (forall (i:nat). {:pattern (v (getValue h a (i+a_idx)))}
      (i >= ctr /\ i < len) ==>
	(v (getValue h a (i+a_idx)) + v (getValue h b (i+b_idx)) < pow2 platform_wide))

opaque type IsNotModified
  (h0:heap) (h1:heap) (a_idx:nat) (len:nat) (ctr:nat) 
  (a:bigint_wide{live h0 a /\ live h1 a /\ a_idx+len <= getLength h0 a /\ getLength h0 a = getLength h1 a}) = 
    (forall (i:nat). {:pattern (getValue h1 a i)}
      ((i<ctr+a_idx \/ i >= len+a_idx) /\ i<getLength h0 a) ==>
	(getValue h1 a i == getValue h0 a i))

opaque type IsSum
  (h0:heap) (h1:heap) (a_idx:nat) (b_idx:nat) (len:nat) (ctr:nat)
  (a:bigint_wide{live h0 a /\ live h1 a /\ a_idx+len <= getLength h0 a /\ getLength h0 a = getLength h1 a})
  (b:bigint_wide{live h0 b /\ b_idx+len <= getLength h0 b}) =
    (forall (i:nat). {:pattern (v (getValue h1 a (i+a_idx))) \/ (v (getValue h1 a i))}
      (i>= ctr /\ i<len) ==> 
	(v (getValue h1 a (i+a_idx)) = v (getValue h0 a (i+a_idx)) + v (getValue h0 b (i+b_idx))) )
     
val fsum_index:
  a:bigint_wide -> a_idx:nat -> b:bigint_wide{Similar a b} -> 
  b_idx:nat -> len:nat -> ctr:nat{ ctr <= len } ->
  ST unit
    (requires (fun h ->
      (live h a) /\ (live h b)
      /\ (a_idx+len <= getLength h a /\ b_idx+len <= getLength h b)
      /\ (WillNotOverflow h a_idx b_idx len ctr a b)
    ))
    (ensures (fun h0 _ h1 -> 
      (live h0 a) /\ (live h0 b) /\ (live h1 a) /\ (live h1 b)
      /\ (a_idx+len <= getLength h0 a /\ b_idx+len <= getLength h0 b)
      /\ (modifies !{getRef a} h0 h1)
      /\ (getLength h0 a = getLength h1 a)
      /\ (IsSum h0 h1 a_idx b_idx len ctr a b)
      /\ (IsNotModified h0 h1 a_idx len ctr a)
    ))

val fsum':
  a:bigint_wide -> b:bigint_wide{Similar a b} -> ST unit
    (requires (fun h -> Standardized h a /\ Standardized h b))
    (ensures (fun h0 u h1 -> 
      Standardized h0 a /\ Standardized h0 b /\ Standardized h1 b
      /\ (live h1 a) /\ (modifies !{getRef a} h0 h1) 
      /\ (getLength h1 a = getLength h0 a) /\ (getLength h0 b = getLength h1 b)
      /\ (eval h1 a norm_length = eval h0 a norm_length + eval h0 b norm_length)
      /\ (IsSum h0 h1 0 0 norm_length 0 a b)
    ))
