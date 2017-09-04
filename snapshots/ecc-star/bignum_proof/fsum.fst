(*--build-config
  options:--admit_fsi FStar.Set --admit_fsi Parameters --verify_module Fsum --z3rlimit 500;
  other-files:FStar.Classical.fst FStar.PredicateExtensionality.fst FStar.Set.fsi seq.fsi FStar.Seq.Base.fst FStar.Seq.Properties.fst FStar.Seq.fst FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Array.fst FStar.Ghost.fst axiomatic.fst intlib.fst lemmas.fst parameters.fsti uint.fst bigint.fst eval.fst fsum_lemmas.fst;
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
  			  
val fsum_index_aux:
  a:bigint -> b:bigint{Similar a b} -> ctr:nat{ctr < norm_length} ->
  ST unit
    (requires (fun h -> 
      live h a /\ live h b /\ norm_length <= getLength h a /\ norm_length <= getLength h b
      /\ WillNotOverflow h a b ctr
    ))
    (ensures (fun h0 _ h1 ->
      live h0 a /\ live h1 a /\ live h0 b /\ live h1 b
      /\ getLength h1 a = getLength h0 a /\ getLength h0 b = getLength h1 b
      /\ norm_length <= getLength h0 a /\ norm_length <= getLength h0 b /\ modifies !{getRef a} h0 h1
      /\ (WillNotOverflow h1 a b (ctr+1))
      /\ (NotModified h0 h1 a ctr)
      /\ v (getValue h1 a ctr) = v (getValue h0 a ctr) + v (getValue h0 b ctr)))
      
let fsum_index_aux a b ctr =
  //@@
  let h0 = ST.get() in
  let ai = index_limb a ctr in 
  let bi = index_limb b ctr in 
  assert(ctr >= ctr /\ ctr < norm_length); 
  assert(b2t(v (getValue h0 a ctr) + v (getValue h0 b ctr) < pow2 platform_size)); 
  let z = add_limb ai bi in 
  upd_limb a ctr z; 
  let h1 = ST.get() in
  upd_lemma h0 h1 a ctr z; 
  assert(v (getValue h1 a ctr) = v (getValue h0 a ctr) + v (getValue h0 b ctr)); 
  assert(NotModified h0 h1 a ctr); 
  assert(WillNotOverflow h1 a b (ctr+1));
  no_upd_lemma h0 h1 b (!{getRef a})

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
    
val fsum_index_lemma: 
  h0:heap -> h1:heap -> h2:heap -> a:bigint -> b:bigint{Similar a b} -> ctr:nat{ctr < norm_length} ->
  Lemma (requires (
      live h0 a /\ live h1 a /\ live h2 a /\ live h0 b /\ live h1 b /\ live h2 b
      /\ modifies !{getRef a} h0 h1 /\ modifies !{getRef a} h1 h2
      /\ getLength h0 a = getLength h1 a /\ getLength h1 a = getLength h2 a
      /\ getLength h0 b = getLength h1 b /\ getLength h1 b = getLength h2 b
      /\ (norm_length <= getLength h0 a /\ norm_length <= getLength h0 b)
      /\ (modifies !{getRef a} h1 h2)
      /\ (NotModified2 h1 h2 a (ctr+1))
      /\ (IsSum h1 h2 a b (ctr+1))
      /\ (WillNotOverflow h0 a b (ctr+1))
      /\ (NotModified h0 h1 a ctr)
      /\ v (getValue h1 a ctr) = v (getValue h0 a ctr) + v (getValue h0 b ctr)
      ))
    (ensures (
      (live h0 a) /\ (live h0 b) /\ (live h2 a) /\ (live h2 b)
      /\ (norm_length <= getLength h0 a /\ norm_length <= getLength h0 b)
      /\ (modifies !{getRef a} h0 h2)
      /\ (getLength h0 a = getLength h2 a)
      /\ (IsSum h0 h2 a b ctr)
      ))
      
let fsum_index_lemma h0 h1 h2 a b ctr =
  //@@
  no_upd_lemma h0 h1 b (!{getRef a});
  no_upd_lemma h1 h2 b (!{getRef a});
  assert(IsSum h1 h2 a b (ctr+1)); 
  assert(NotModified2 h1 h2 a (ctr+1)); 
  assert(NotModified h0 h1 a ctr); 
  cut(IsSum h0 h2 a b (ctr+1)); 
  cut(True /\ v (getValue h2 a ctr) = v (getValue h0 a ctr) + v (getValue h0 b ctr)); 
  FsumLemmas.auxiliary_lemma_7 ctr norm_length; 
  assert(IsSum h0 h2 a b ctr)

// Verified, try with big timeout
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
let rec fsum_index a b ctr =
  //@@
  let h0 = ST.get() in
  match norm_length - ctr with
  | 0 -> ()    
  | _ -> 
    fsum_index_aux a b ctr; 
    let h1 = ST.get() in
    no_upd_lemma h0 h1 b (!{getRef a}); 
    FsumLemmas.auxiliary_lemma_6 norm_length ctr; 
    fsum_index a b (ctr+1); 
    let h2 = ST.get() in
    fsum_index_lemma h0 h1 h2 a b ctr
      
#reset-options

opaque val gaddition_lemma_aux:
  h0:heap ->  h1:heap ->
  a:bigint{(live h0 a) /\ (live h1 a)} -> 
  b:bigint{(live h0 b) /\ (getTemplate b = getTemplate a) } ->
  len:pos{ (len <= getLength h0 a) /\ (len <= getLength h0 b) /\ (len <= getLength h1 a)
	   /\ (forall (i:nat{ i < len }). v (getValue h1 a i) = v (getValue h0 a i) + v (getValue h0 b i)) } ->
  GLemma unit
    (requires ( (eval h0 a (len-1) + eval h0 b (len-1) = eval h1 a (len-1))
		/\ (v (getValue h1 a (len-1)) = v (getValue h0 a (len-1)) + v (getValue h0 b (len-1))) ) )
    (ensures (eval h0 a len + eval h0 b len = eval h1 a len)) []
let gaddition_lemma_aux h0 h1 a b len =
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

val addition_lemma_aux:
  h0:heap ->  h1:heap ->
  a:bigint{(live h0 a) /\ (live h1 a)} -> 
  b:bigint{(live h0 b) /\ (getTemplate b = getTemplate a) } ->
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

val addition_lemma:
  h0:heap ->
  h1:heap ->
  a:bigint{(live h0 a) /\ (live h1 a)} -> 
  b:bigint{(live h0 b) /\ (getTemplate b = getTemplate a) } ->
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
  a:bigint{ (live h0 a) } -> 
  b:bigint{ (live h0 b) /\ (getLength h0 a = getLength h0 b) } ->
  c:bigint{ (live h1 c) /\ (getLength h1 c = getLength h0 a)
	    /\ (forall (i:nat{i<getLength h1 c}). 
		v (getValue h1 c i) = v (getValue h0 a i) + v (getValue h0 b i)) } ->
  Lemma
    (requires (True))
    (ensures (maxValue h1 c <= maxValue h0 a + maxValue h0 b))
let addition_max_value_lemma h0 h1 a b c = ()
  
val max_value_lemma: 
  h:heap -> a:bigint{ live h a } -> m:nat ->
  Lemma 
    (requires (forall (n:nat). n < getLength h a ==> v (getValue h a n) <= m))
    (ensures (maxValue h a <= m))
let max_value_lemma h a m = ()

#reset-options

val addition_max_value_lemma_extended:
  h0:heap -> h1:heap -> a:bigint{ (live h0 a) } -> b:bigint{ (live h0 b) } ->
  c:bigint{ (live h1 c) /\ (getLength h0 a = getLength h1 c) } ->
  idx:nat -> len:nat{ len + idx <= getLength h0 a /\ len <= getLength h0 b } ->
  Lemma
    (requires ((forall (i:nat). {:pattern (v (getValue h1 c (i+idx)))} 
		  (i<len) ==> v (getValue h1 c (i+idx)) = v (getValue h0 a (i+idx)) + v (getValue h0 b i))
	       /\ (forall (i:nat). {:pattern (v (getValue h1 c i))}
		   (i < getLength h1 c /\ (i < idx \/ i >= idx + len)) ==> v (getValue h1 c i) = v (getValue h0 a i))))
    (ensures (maxValue h1 c <= maxValue h0 a + maxValue h0 b))
let addition_max_value_lemma_extended h0 h1 a b c idx len = 
  cut ( forall (i:nat). (i < getLength h1 c /\ (i < idx \/ i >= idx + len))
	==> (v (getValue h1 c i) = v (getValue h0 a i) /\ v (getValue h1 c i) <= maxValue h0 a + maxValue h0 b)); 
  cut ( forall (i:nat). (i < getLength h1 c /\ (i < idx \/ i >= idx + len)) 
  	==> v (getValue h1 c i) <= maxValue h0 a + maxValue h0 b); 
  cut(forall (i:nat). {:pattern (v (getValue h1 c i))} (i+idx < idx + len /\ i+idx >= idx) ==> (i >= 0 /\ i < len)); 
  cut((forall (i:nat). {:pattern (v (getValue h1 c i))} (i-idx)+idx=i)); 
  assert(forall (i:nat). {:pattern (v (getValue h1 c (i)))} (i<len) ==> v (getValue h1 c (i+idx)) = v (getValue h0 a (i+idx)) + v (getValue h0 b i)); 
  assert(forall (i:nat). {:pattern (v (getValue h1 c i))} (i >= idx /\ i < idx + len) ==> (v (getValue h1 c i) = v (getValue h1 c ((i-idx)+idx)))); 
  cut ( forall (i:nat). (i < idx + len /\ i >= idx)
	==> ((v (getValue h1 c i) = v (getValue h0 a i) + v (getValue h0 b (i-idx))) )); 
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
  ha:heap -> a:bigint{Standardized ha a} ->
  hb:heap -> b:bigint{Standardized hb b} -> i:nat{ i < norm_length} ->
  GLemma unit 
    (requires (True))
    (ensures (bitsize (v (getValue ha a i) + v (getValue hb b i)) platform_size))
    []
let gauxiliary_lemma_2 ha a hb b i =
  UInt.add_lemma (templ i) (v (getValue ha a i)) (templ i) (v (getValue hb b i));
  parameters_lemma_0 ();
  Lemmas.pow2_increases_2 platform_size (templ i + 1)

val auxiliary_lemma_2: 
  ha:heap -> a:bigint{Standardized ha a} ->
  hb:heap -> b:bigint{Standardized hb b} -> i:nat{ i < norm_length} ->
  Lemma (requires (True))
	(ensures (bitsize (v (getValue ha a i) + v (getValue hb b i)) platform_size))
	[SMTPat (v (getValue ha a i) + v (getValue hb b i))]
let auxiliary_lemma_2 ha a hb b i =
  coerce
    (requires (True))
    (ensures (bitsize (v (getValue ha a i) + v (getValue hb b i)) platform_size))
    (fun _ -> gauxiliary_lemma_2 ha a hb b i)

val auxiliary_lemma_0: 
  ha:heap -> a:bigint{Standardized ha a} ->
  hb:heap -> b:bigint{Standardized hb b} ->
  Lemma (requires (True))
	(ensures (forall (i:nat). 
	  i < norm_length ==> bitsize (v (getValue ha a i) + v (getValue hb b i)) platform_size))
let auxiliary_lemma_0 ha a hb b = ()

#reset-options

val auxiliary_lemma_1:
  h0:heap -> h1:heap -> b:bigint{Standardized h0 b} ->
  Lemma (requires (live h1 b /\ Seq.Eq (sel h1 (getRef b)) (sel h0 (getRef b))))
	(ensures (Standardized h1 b))
let auxiliary_lemma_1 h0 h1 b = 
  //@@
  ()

val auxiliary_lemma_3:
  h0:heap -> h1:heap -> 
  a:bigint{Standardized h0 a /\ live h1 a /\ getLength h1 a >= norm_length} ->
  b:bigint{Standardized h0 b /\ Standardized h1 b} ->
  Lemma (requires (forall (i:nat{i>= 0 /\ i<norm_length}). 
	  (v (getValue h1 a (i+0)) = v (getValue h0 a (i+0)) + v (getValue h0 b (i+0))) ))
	(ensures (forall (i:nat). i < norm_length ==> v (getValue h1 a i) = v (getValue h0 a i) + v (getValue h0 b i)))
let auxiliary_lemma_3 h0 h1 a b =	
  cut (forall (i:nat{ i >= 0 /\ i < norm_length }). True ==> (i < norm_length /\ i+0 = i));
  cut (forall (i:nat). i < norm_length ==> v (getValue h1 a i) = v (getValue h0 a i) + v (getValue h0 b i))

#reset-options

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
let fsum' a b =
  let h0 = ST.get() in
  auxiliary_lemma_0 h0 a h0 b;
  fsum_index a b 0;
  let h1 = ST.get() in
  no_upd_lemma h0 h1 b (!{getRef a});
  auxiliary_lemma_1 h0 h1 b;
  auxiliary_lemma_3 h0 h1 a b;
  addition_lemma h0 h1 a b norm_length;
  cut(forall (i:nat). (i >= 0 /\ i < norm_length) ==> i < norm_length);
  ()

