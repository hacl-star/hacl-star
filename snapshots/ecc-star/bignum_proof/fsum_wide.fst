(*--build-config
  options:--admit_fsi FStar.Seq --admit_fsi FStar.Set --admit_fsi IntLib --admit_fsi Parameters --verify_module FsumWide --z3rlimit 30;
  other-files:FStar.Classical.fst FStar.PredicateExtensionality.fst FStar.Set.fsi FStar.Seq.Base.fst FStar.Seq.Properties.fst FStar.Seq.fst FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Array.fst FStar.Ghost.fst axiomatic.fst intlib.fsti lemmas.fst parameters.fsti uint.fst bigint.fst eval.fst fsum_lemmas.fst;
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

#reset-options

opaque val gfsum_index_lemma:
  h0:heap -> h1:heap -> h2:heap ->
  a:bigint_wide -> a_idx:nat -> b:bigint_wide{Similar a b} -> 
  b_idx:nat -> len:nat -> ctr:nat{ ctr < len } ->
  GLemma unit
    (requires (
      (live h0 a) /\ (live h0 b) /\ (live h1 b) /\ (live h1 a) /\ (live h2 a) /\ (live h2 b)
      /\ (a_idx+len <= getLength h0 a /\ b_idx+len <= getLength h0 b)
      /\ (getLength h1 a = getLength h0 a) /\ (getLength h2 a = getLength h0 a) 
      /\ (getLength h1 b = getLength h0 b) /\ (getLength h2 b = getLength h0 b) 
      /\ (modifies !{getRef a} h0 h1) /\ (modifies !{getRef a} h1 h2)
      // Before fsum_index (ctr+1)
      /\ (forall (i:nat). 
	  (i >= ctr+1 /\ i < len) ==>
	    (v (getValue h1 a (i+a_idx)) + v (getValue h1 b (i+b_idx)) < pow2 platform_wide))
      /\ (forall (i:nat).
	  (i<>ctr /\ i < getLength h0 a - a_idx) ==> getValue h0 a (i+a_idx) == getValue h1 a (i+a_idx))
      /\ (v (getValue h1 a (ctr+a_idx)) = v (getValue h0 a (ctr+a_idx)) + v (getValue h0 b (ctr+b_idx)))
       // After fsum
      /\ (forall (i:nat). (i>= ctr+1 /\ i<len) ==> 
	  (v (getValue h2 a (i+a_idx)) = v (getValue h1 a (i+a_idx)) + v (getValue h1 b (i+b_idx))) )
      /\ (forall (i:nat). ((i<ctr+1 \/ i >= len) /\ i<getLength h1 a-a_idx) ==>
	  (getValue h2 a (i+a_idx) == getValue h1 a (i+a_idx))) ))
    (ensures (
      (live h0 a) /\ (live h0 b) /\ (live h2 a) /\ (live h2 b)
      /\ (a_idx+len <= getLength h0 a /\ b_idx+len <= getLength h0 b)
      /\ (modifies !{getRef a} h0 h2)
      /\ (getLength h0 a = getLength h2 a)
      /\ (forall (i:nat). (i>= ctr /\ i<len) ==> 
	  (v (getValue h2 a (i+a_idx)) = v (getValue h0 a (i+a_idx)) + v (getValue h0 b (i+b_idx))) )
      /\ (forall (i:nat). ((i<ctr \/ i >= len) /\ i<getLength h0 a-a_idx) ==>
	  (getValue h2 a (i+a_idx) == getValue h0 a (i+a_idx)))
     ))
     []
     
let gfsum_index_lemma h0 h1 h2 a a_idx b b_idx len ctr =
  //@@
      no_upd_lemma h1 h2 b (!{getRef a});
      cut(forall (i:nat). (i>=ctr+1 /\ i < len) ==> (v (getValue h2 a (i+a_idx)) = v (getValue h1 a (i+a_idx)) + v (getValue h1 b (i+b_idx)))); 
      let (f:(i:nat{i<>ctr/\i<getLength h0 a-a_idx} -> GTot bool)) =  (fun i -> v (getValue h1 a (i+a_idx)) = v (getValue h0 a (i+a_idx))) in 
      FsumLemmas.auxiliary_lemma_3 a_idx ctr len (getLength h0 a) f; 
      cut(forall (i:nat). (i>=ctr+1 /\ i < len) ==> v (getValue h1 a (i+a_idx)) = v (getValue h0 a (i+a_idx))); 
      no_upd_lemma h0 h1 b (!{getRef a});
      cut(forall (i:nat). (i>=ctr+1 /\ i < len) ==> v (getValue h1 b (i+b_idx)) = v (getValue h0 b (i+b_idx))); 
      cut(forall (i:nat). (i>=ctr+1 /\ i < len) ==> (v (getValue h2 a (i+a_idx)) = v (getValue h0 a (i+a_idx)) + v (getValue h0 b (i+b_idx)))); 
      cut(forall (i:nat). ((i<ctr+1 \/ i >= len) /\ i<getLength h0 a-a_idx) ==>  
	  (getValue h2 a (i+a_idx) == getValue h1 a (i+a_idx)) ); 
      cut(getValue h2 a (ctr+a_idx) == getValue h1 a (ctr+a_idx)); 
      cut(True /\ v (getValue h2 a (ctr+a_idx)) = v (getValue h1 a (ctr+a_idx))); 
      assert(v (getValue h2 a (ctr+a_idx)) = v (getValue h0 a (ctr+a_idx)) + v (getValue h0 b (ctr+b_idx)));
      let (g:(i:nat{(i>=ctr+1 /\ i < len)\/i=ctr} -> GTot bool)) = fun i -> 
	(v (getValue h2 a (i+a_idx)) = v (getValue h0 a (i+a_idx)) + v (getValue h0 b (i+b_idx))) in
      FsumLemmas.auxiliary_lemma_4 len ctr g; 
      cut(forall (i:nat). (i>=ctr /\ i < len) ==> (v (getValue h2 a (i+a_idx)) = v (getValue h0 a (i+a_idx)) + v (getValue h0 b (i+b_idx))) ); 
      cut(forall (i:nat).((i<ctr \/ i >= len) /\ i<getLength h0 a-a_idx) ==> (getValue h2 a (i+a_idx) == getValue h0 a (i+a_idx))); 
      no_upd_lemma h0 h2 b (!{getRef a})

#reset-options

val fsum_index_lemma:
  h0:heap -> h1:heap -> h2:heap ->
  a:bigint_wide -> a_idx:nat -> b:bigint_wide{Similar a b} -> 
  b_idx:nat -> len:nat -> ctr:nat{ ctr < len } ->
  Lemma
    (requires (
      (live h0 a) /\ (live h0 b) /\ (live h1 b) /\ (live h1 a) /\ (live h2 a) /\ (live h2 b)
      /\ (a_idx+len <= getLength h0 a /\ b_idx+len <= getLength h0 b)
      /\ (getLength h1 a = getLength h0 a) /\ (getLength h2 a = getLength h0 a) 
      /\ (getLength h1 b = getLength h0 b) /\ (getLength h2 b = getLength h0 b) 
      /\ (modifies !{getRef a} h0 h1) /\ (modifies !{getRef a} h1 h2)
      // Before fsum_index (ctr+1)
      /\ (forall (i:nat). 
	  (i >= ctr+1 /\ i < len) ==>
	    (v (getValue h1 a (i+a_idx)) + v (getValue h1 b (i+b_idx)) < pow2 platform_wide))
      /\ (forall (i:nat).
	  (i<>ctr /\ i < getLength h0 a - a_idx) ==> getValue h0 a (i+a_idx) == getValue h1 a (i+a_idx))
      /\ (v (getValue h1 a (ctr+a_idx)) = v (getValue h0 a (ctr+a_idx)) + v (getValue h0 b (ctr+b_idx)))
       // After fsum
      /\ (forall (i:nat). (i>= ctr+1 /\ i<len) ==> 
	  (v (getValue h2 a (i+a_idx)) = v (getValue h1 a (i+a_idx)) + v (getValue h1 b (i+b_idx))) )
      /\ (forall (i:nat). ((i<ctr+1 \/ i >= len) /\ i<getLength h1 a-a_idx) ==>
	  (getValue h2 a (i+a_idx) == getValue h1 a (i+a_idx))) ))
    (ensures (
      (live h0 a) /\ (live h0 b) /\ (live h2 a) /\ (live h2 b)
      /\ (a_idx+len <= getLength h0 a /\ b_idx+len <= getLength h0 b)
      /\ (modifies !{getRef a} h0 h2)
      /\ (getLength h0 a = getLength h2 a)
      /\ (forall (i:nat). (i>= ctr /\ i<len) ==> 
	  (v (getValue h2 a (i+a_idx)) = v (getValue h0 a (i+a_idx)) + v (getValue h0 b (i+b_idx))) )
      /\ (forall (i:nat). ((i<ctr \/ i >= len) /\ i<getLength h0 a-a_idx) ==>
	  (getValue h2 a (i+a_idx) == getValue h0 a (i+a_idx)))
     ))
let fsum_index_lemma h0 h1 h2 a a_idx b b_idx len ctr =
  coerce
    (requires (
      (live h0 a) /\ (live h0 b) /\ (live h1 b) /\ (live h1 a) /\ (live h2 a) /\ (live h2 b)
      /\ (a_idx+len <= getLength h0 a /\ b_idx+len <= getLength h0 b)
      /\ (getLength h1 a = getLength h0 a) /\ (getLength h2 a = getLength h0 a) 
      /\ (getLength h1 b = getLength h0 b) /\ (getLength h2 b = getLength h0 b) 
      /\ (modifies !{getRef a} h0 h1) /\ (modifies !{getRef a} h1 h2)
      // Before fsum_index (ctr+1)
      /\ (forall (i:nat). 
	  (i >= ctr+1 /\ i < len) ==>
	    (v (getValue h1 a (i+a_idx)) + v (getValue h1 b (i+b_idx)) < pow2 platform_wide))
      /\ (forall (i:nat).
	  (i<>ctr /\ i < getLength h0 a - a_idx) ==> getValue h0 a (i+a_idx) == getValue h1 a (i+a_idx))
      /\ (v (getValue h1 a (ctr+a_idx)) = v (getValue h0 a (ctr+a_idx)) + v (getValue h0 b (ctr+b_idx)))
       // After fsum
      /\ (forall (i:nat). (i>= ctr+1 /\ i<len) ==> 
	  (v (getValue h2 a (i+a_idx)) = v (getValue h1 a (i+a_idx)) + v (getValue h1 b (i+b_idx))) )
      /\ (forall (i:nat). ((i<ctr+1 \/ i >= len) /\ i<getLength h1 a-a_idx) ==>
	  (getValue h2 a (i+a_idx) == getValue h1 a (i+a_idx))) ))
    (ensures (
      (live h0 a) /\ (live h0 b) /\ (live h2 a) /\ (live h2 b)
      /\ (a_idx+len <= getLength h0 a /\ b_idx+len <= getLength h0 b)
      /\ (modifies !{getRef a} h0 h2)
      /\ (getLength h0 a = getLength h2 a)
      /\ (forall (i:nat). (i>= ctr /\ i<len) ==> 
	  (v (getValue h2 a (i+a_idx)) = v (getValue h0 a (i+a_idx)) + v (getValue h0 b (i+b_idx))) )
      /\ (forall (i:nat). ((i<ctr \/ i >= len) /\ i<getLength h0 a-a_idx) ==>
	  (getValue h2 a (i+a_idx) == getValue h0 a (i+a_idx)))
     ))
     (fun _ -> gfsum_index_lemma h0 h1 h2 a a_idx b b_idx len ctr)

#reset-options

// Verified, try with big timeout
val fsum_index:
  a:bigint_wide -> a_idx:nat -> b:bigint_wide{Similar a b} -> 
  b_idx:nat -> len:nat -> ctr:nat{ ctr <= len } ->
  ST unit
    (requires (fun h ->
      (live h a) /\ (live h b)
      /\ (a_idx+len <= getLength h a /\ b_idx+len <= getLength h b)
      /\ (forall (i:nat). {:pattern (i+a_idx); (i+b_idx)}
	  (i >= ctr /\ i < len) ==>
	    (v (getValue h a (i+a_idx)) + v (getValue h b (i+b_idx)) < pow2 platform_wide))
    ))
    (ensures (fun h0 _ h1 -> 
      (live h0 a) /\ (live h0 b) /\ (live h1 a) /\ (live h1 b)
      /\ (a_idx+len <= getLength h0 a /\ b_idx+len <= getLength h0 b)
      /\ (modifies !{getRef a} h0 h1)
      /\ (getLength h0 a = getLength h1 a)
      /\ (forall (i:nat). (i>= ctr /\ i<len) ==> 
	  (v (getValue h1 a (i+a_idx)) = v (getValue h0 a (i+a_idx)) + v (getValue h0 b (i+b_idx))) )
      /\ (forall (i:nat). ((i<ctr \/ i >= len) /\ i<getLength h0 a-a_idx) ==>
	  (getValue h1 a (i+a_idx) == getValue h0 a (i+a_idx)))
    ))
let rec fsum_index a a_idx b b_idx len ctr =
  //@@
  let h0 = ST.get() in
  match len - ctr with
  | 0 -> ()    
  | _ -> 
      let i = ctr in
      FsumLemmas.helper_lemma_1 a_idx i len (egetLength h0 a);
      FsumLemmas.helper_lemma_1 b_idx i len (egetLength h0 b);
      let ai = index_wide a (i+a_idx) in 
      let bi = index_wide b (i+b_idx) in 
      assert(i >= ctr /\ i < len); 
      cut(b2t(v (getValue h0 a (i+a_idx)) + v (getValue h0 b (i+b_idx)) < pow2 platform_wide));
      let z = add_wide ai bi in
      upd_wide a (a_idx+i) z; 
      let h1 = ST.get() in
      upd_lemma h0 h1 a (i+a_idx) z; 
      no_upd_lemma h0 h1 b (!{getRef a}); 
      cut(True /\ live h1 a); 
      cut(True /\ live h1 b); 
      cut(a_idx+len <= getLength h1 a /\ b_idx+len <= getLength h1 b); 
      cut(forall (i:nat). (i >= ctr+1 /\ i < len) ==> 
	  (v (getValue h1 a (i+a_idx)) + v (getValue h1 b (i+b_idx)) < pow2 platform_wide));
      FsumLemmas.auxiliary_lemma_0 len ctr;
      fsum_index a a_idx b b_idx len (ctr+1); 
      let h2 = ST.get() in
      no_upd_lemma h1 h2 b (!{getRef a});      
      cut (forall (i:nat).
	  (i<>ctr+a_idx /\ i < getLength h0 a) ==> getValue h0 a (i) == getValue h1 a (i)); 
      FsumLemmas.auxiliary_lemma_5 ctr (egetLength h0 a) a_idx;
      cut (forall (i:nat).
	  (i<>ctr /\ i < getLength h0 a - a_idx) ==> getValue h0 a (i+a_idx) == getValue h1 a (i+a_idx));
      fsum_index_lemma h0 h1 h2 a a_idx b b_idx len ctr

#reset-options

opaque val gaddition_lemma_aux:
  h0:heap ->  h1:heap ->
  a:bigint_wide{(live h0 a) /\ (live h1 a)} -> 
  b:bigint_wide{(live h0 b) /\ (getTemplate b = getTemplate a) } ->
  len:pos{ (len <= getLength h0 a) /\ (len <= getLength h0 b) /\ (len <= getLength h1 a)
	   /\ (forall (i:nat{ i < len }). v (getValue h1 a i) = v (getValue h0 a i) + v (getValue h0 b i)) } ->
  GLemma unit
    (requires ( (eval h0 a (len-1) + eval h0 b (len-1) = eval h1 a (len-1))
		/\ (v (getValue h1 a (len-1)) = v (getValue h0 a (len-1)) + v (getValue h0 b (len-1))) ) )
    (ensures (eval h0 a len + eval h0 b len = eval h1 a len)) []
let gaddition_lemma_aux h0 h1 a b len =
  //@@
  eval_definition h1 a len;
  assert(eval h1 a len = pow2 (bitweight (getTemplate a) (len-1)) * v (getValue h1 a (len-1)) + eval h1 a (len-1));
  assert(v (getValue h1 a (len-1)) = v (getValue h0 a (len-1)) + v (getValue h0 b (len-1)));
  Axiomatic.distributivity_add_right (pow2 (bitweight (getTemplate a) (len-1))) (v (getValue h0 a (len-1)))  (v (getValue h0 b (len-1))); 
  assert(eval h1 a len = (pow2 (bitweight (getTemplate a) (len-1)) * v (getValue h0 a (len-1)) + pow2 (bitweight (getTemplate a) (len-1)) * v (getValue h0 b (len-1))) + eval h1 a (len-1));
  FsumLemmas.helper_lemma_2 (pow2 (bitweight (getTemplate a) (len-1)) * v (getValue h0 a (len-1)))
		(pow2 (bitweight (getTemplate a) (len-1)) * v (getValue h0 b (len-1)))
		(eval h0 a (len-1))
		(eval h0 b (len-1));
  eval_definition h0 a len;
  eval_definition h0 b len

#reset-options

val addition_lemma_aux:
  h0:heap ->  h1:heap ->
  a:bigint_wide{(live h0 a) /\ (live h1 a)} -> 
  b:bigint_wide{(live h0 b) /\ (getTemplate b = getTemplate a) } ->
  len:pos{ (len <= getLength h0 a) /\ (len <= getLength h0 b) /\ (len <= getLength h1 a)
	   /\ (forall (i:nat{ i < len }). v (getValue h1 a i) = v (getValue h0 a i) + v (getValue h0 b i)) } ->
  Lemma
    (requires ( (eval h0 a (len-1) + eval h0 b (len-1) = eval h1 a (len-1))
		/\ (v (getValue h1 a (len-1)) = v (getValue h0 a (len-1)) + v (getValue h0 b (len-1))) ) )
    (ensures (eval h0 a len + eval h0 b len = eval h1 a len))
let addition_lemma_aux h0 h1 a b len =
  coerce
	(requires ( (eval h0 a (len-1) + eval h0 b (len-1) = eval h1 a (len-1))
	/\ (v (getValue h1 a (len-1)) = v (getValue h0 a (len-1)) + v (getValue h0 b (len-1)))))
	(ensures (eval h0 a len + eval h0 b len = eval h1 a len))
	(fun _ -> gaddition_lemma_aux h0 h1 a b len)

#reset-options

val addition_lemma:
  h0:heap ->
  h1:heap ->
  a:bigint_wide{(live h0 a) /\ (live h1 a)} -> 
  b:bigint_wide{(live h0 b) /\ (getTemplate b = getTemplate a) } ->
  len:nat{ (len <= getLength h0 a) /\ (len <= getLength h0 b) /\ (len <= getLength h1 a)
	  /\ (forall (i:nat). i < len ==> v (getValue h1 a i) = v (getValue h0 a i) + v (getValue h0 b i)) } ->
  Lemma
    (requires (True))
    (ensures ( eval h0 a len + eval h0 b len = eval h1 a len ))
let rec addition_lemma h0 h1 a b len =
  //@@
  match len with
  | 0 -> ()
  | _ -> addition_lemma h0 h1 a b (len-1);
    addition_lemma_aux h0 h1 a b len

#reset-options

val addition_max_value_lemma:
  h0:heap -> 
  h1:heap -> 
  a:bigint_wide{ (live h0 a) } -> 
  b:bigint_wide{ (live h0 b) /\ (getLength h0 a = getLength h0 b) } ->
  c:bigint_wide{ (live h1 c) /\ (getLength h1 c = getLength h0 a)
	    /\ (forall (i:nat{i<getLength h1 c}). 
		v (getValue h1 c i) = v (getValue h0 a i) + v (getValue h0 b i)) } ->
  Lemma
    (requires (True))
    (ensures (maxValue h1 c <= maxValue h0 a + maxValue h0 b))
let addition_max_value_lemma h0 h1 a b c = ()

#reset-options

val max_value_lemma: 
  h:heap -> a:bigint_wide{ live h a } -> m:nat ->
  Lemma 
    (requires (forall (n:nat). n < getLength h a ==> v (getValue h a n) <= m))
    (ensures (maxValue h a <= m))
let max_value_lemma h a m = ()

#reset-options

val addition_max_value_lemma_extended:
  h0:heap -> h1:heap -> a:bigint_wide{ (live h0 a) } -> b:bigint_wide{ (live h0 b) } ->
  c:bigint_wide{ (live h1 c) /\ (getLength h0 a = getLength h1 c) } ->
  idx:nat -> len:nat{ len + idx <= getLength h0 a /\ len <= getLength h0 b } ->
  Lemma
    (requires ((forall (i:nat{i<len}). 
		  v (getValue h1 c (i+idx)) = v (getValue h0 a (i+idx)) + v (getValue h0 b i))
	       /\ (forall (i:nat{i < getLength h1 c /\ (i < idx \/ i >= idx + len)}).
		   v (getValue h1 c i) = v (getValue h0 a i))))
    (ensures (maxValue h1 c <= maxValue h0 a + maxValue h0 b))
let addition_max_value_lemma_extended h0 h1 a b c idx len = 
  //@@
  cut ( forall (i:nat). (i < getLength h1 c /\ (i < idx \/ i >= idx + len))
	==> (v (getValue h1 c i) = v (getValue h0 a i) /\ v (getValue h1 c i) <= maxValue h0 a + maxValue h0 b));
  cut ( forall (i:nat). (i < getLength h1 c /\ (i < idx \/ i >= idx + len)) 
  	==> v (getValue h1 c i) <= maxValue h0 a + maxValue h0 b);
  cut ( forall (i:nat). (i < idx + len /\ i >= idx)
	==> ((v (getValue h1 c i) = v (getValue h0 a i) + v (getValue h0 b (i-idx))) 
	     /\ (v (getValue h1 c i) <= v (getValue h0 a i) + v (getValue h0 b (i-idx)))) );
  cut ( forall (i:nat). (i < idx + len /\ i >= idx)
	==> (v (getValue h0 a i) <= maxValue h0 a /\ v (getValue h0 b (i-idx)) <= maxValue h0 b));
  cut ( forall (i:nat). (i >= idx /\ i < idx + len)
	==> v (getValue h1 c i) <= maxValue h0 a + maxValue h0 b);
  cut ( forall (i:nat). i < getLength h1 c 
	==> v (getValue h1 c i) <= maxValue h0 a + maxValue h0 b);
  max_value_lemma h1 c (maxValue h0 a + maxValue h0 b);
  ()

#reset-options

opaque val gauxiliary_lemma_2: 
  ha:heap -> a:bigint_wide{Standardized ha a} ->
  hb:heap -> b:bigint_wide{Standardized hb b} -> i:nat{ i < norm_length} ->
  GLemma unit 
    (requires (True))
    (ensures (bitsize (v (getValue ha a i) + v (getValue hb b i)) platform_size))
    []
let gauxiliary_lemma_2 ha a hb b i =
  UInt.add_lemma #(templ i) (v (getValue ha a i)) #(templ i) (v (getValue hb b i));
  parameters_lemma_0 ();
  Lemmas.pow2_increases_2 platform_size (templ i + 1)

#reset-options

val auxiliary_lemma_2: 
  ha:heap -> a:bigint_wide{Standardized ha a} ->
  hb:heap -> b:bigint_wide{Standardized hb b} -> i:nat{ i < norm_length} ->
  Lemma (requires (True))
	(ensures (bitsize (v (getValue ha a i) + v (getValue hb b i)) platform_size))
	[SMTPat (v (getValue ha a i) + v (getValue hb b i))]
let auxiliary_lemma_2 ha a hb b i =
  coerce
    (requires (True))
    (ensures (bitsize (v (getValue ha a i) + v (getValue hb b i)) platform_size))
    (fun _ -> gauxiliary_lemma_2 ha a hb b i)

#reset-options

val auxiliary_lemma_0: 
  ha:heap -> a:bigint_wide{Standardized ha a} ->
  hb:heap -> b:bigint_wide{Standardized hb b} ->
  Lemma (requires (True))
	(ensures (forall (i:nat). 
	  i < norm_length ==> bitsize (v (getValue ha a i) + v (getValue hb b i)) platform_size))
let auxiliary_lemma_0 ha a hb b = ()

#reset-options

val auxiliary_lemma_1:
  h0:heap -> h1:heap -> b:bigint_wide{Standardized h0 b} ->
  Lemma (requires (live h1 b /\ Seq.Eq (sel h1 (getRef b)) (sel h0 (getRef b))))
	(ensures (Standardized h1 b))
let auxiliary_lemma_1 h0 h1 b = 
  //@@
  ()

#reset-options

val auxiliary_lemma_3:
  h0:heap -> h1:heap -> 
  a:bigint_wide{Standardized h0 a /\ live h1 a /\ getLength h1 a >= norm_length} ->
  b:bigint_wide{Standardized h0 b /\ Standardized h1 b} ->
  Lemma (requires (forall (i:nat{i>= 0 /\ i<norm_length}). 
	  (v (getValue h1 a (i+0)) = v (getValue h0 a (i+0)) + v (getValue h0 b (i+0))) ))
	(ensures (forall (i:nat). i < norm_length ==> v (getValue h1 a i) = v (getValue h0 a i) + v (getValue h0 b i)))
let auxiliary_lemma_3 h0 h1 a b =	
  cut (forall (i:nat{ i >= 0 /\ i < norm_length }). True ==> (i < norm_length /\ i+0 = i));
  cut (forall (i:nat). i < norm_length ==> v (getValue h1 a i) = v (getValue h0 a i) + v (getValue h0 b i))

#reset-options

val fsum':
  a:bigint_wide -> b:bigint_wide{Similar a b} -> ST unit
    (requires (fun h -> Standardized h a /\ Standardized h b))
    (ensures (fun h0 u h1 -> 
      Standardized h0 a /\ Standardized h0 b /\ Standardized h1 b
      /\ (live h1 a) /\ (modifies !{getRef a} h0 h1) 
      /\ (getLength h1 a = getLength h0 a) /\ (getLength h0 b = getLength h1 b)
      /\ (eval h1 a norm_length = eval h0 a norm_length + eval h0 b norm_length)
      /\ (forall (i:nat). i < norm_length ==> v (getValue h1 a i) = v (getValue h0 a i) + v (getValue h0 b i))
    ))
let fsum' a b =
  //@@
  Lemmas.pow2_increases_1 platform_wide platform_size;
  (* admitP(True /\ pow2 platform_size < pow2 platform_wide); *)
  let h0 = ST.get() in
  auxiliary_lemma_0 h0 a h0 b;
  fsum_index a 0 b 0 norm_length 0;
  let h1 = ST.get() in
  no_upd_lemma h0 h1 b (!{getRef a});
  auxiliary_lemma_1 h0 h1 b;
  auxiliary_lemma_3 h0 h1 a b;
  addition_lemma h0 h1 a b norm_length;
  ()

