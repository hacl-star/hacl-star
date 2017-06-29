module Fdifference

open IntLib
open Parameters
open UInt
open FStar.Seq
open Eval
open FStar.ST
open FStar.Heap
open FStar.Ghost
open Bigint

val helper_lemma_1:
  i:nat -> len:nat -> x:erased nat -> 
  Lemma (requires (i < len /\ len <= reveal x)) (ensures (i < reveal x))
let helper_lemma_1 i len v = ()  

#reset-options

val fdifference_aux_1:
  a:bigint -> b:bigint{Similar a b} -> ctr:nat{ctr < norm_length} ->
  ST unit
    (requires (fun h -> live h a /\ live h b /\ norm_length <= getLength h a /\ norm_length <= getLength h b
              /\ (forall (i:nat{ i >= ctr /\ i < norm_length}). v (getValue h b i) >= v (getValue h a i))))
    (ensures (fun h0 _ h1 -> 
      live h0 a /\ live h1 a /\ live h0 b /\ live h1 b
      /\ getLength h1 a = getLength h0 a /\ getLength h0 b = getLength h1 b
      /\ norm_length <= getLength h0 a /\ norm_length <= getLength h0 b /\ modifies !{getRef a} h0 h1
      /\ (forall (i:nat).
	((i >= ctr+1 /\ i < norm_length) ==>  (v (getValue h1 b i) >= v (getValue h1 a i)
						/\ getValue h1 a i == getValue h0 a i))
	/\ (((i<ctr \/ i>=norm_length) /\ i<getLength h0 a) ==> getValue h1 a i == getValue h0 a i))
      /\ v (getValue h1 a ctr) = v (getValue h0 b ctr) - v (getValue h0 a ctr)))
let fdifference_aux_1 a b ctr =
  //@@
  let h0 = ST.get() in
  let i = ctr in
  FdifferenceLemmas.helper_lemma_3 i norm_length; 
  helper_lemma_1 i norm_length (egetLength h0 a); 
  helper_lemma_1 i norm_length (egetLength h0 b); 
  let ai = index_limb a i in 
  let bi = index_limb b i in 
  assert(i >= ctr /\ i < norm_length); 
  cut(b2t(v (getValue h0 b i) >= v (getValue h0 a i))); 
  let z = sub_limb bi ai in 
  upd_limb a i z;
  let h1 = ST.get() in
  upd_lemma h0 h1 a i z;
  no_upd_lemma h0 h1 b (!{getRef a})


val fdifference_aux_2_0: 
  h0:heap -> h1:heap -> h2:heap -> a:bigint -> b:bigint{Similar a b} -> ctr:nat{ctr < norm_length} ->
  Lemma (requires (
      live h0 a /\ live h1 a /\ live h2 a /\ live h0 b /\ live h1 b /\ live h2 b
      /\ modifies !{getRef a} h0 h1 /\ modifies !{getRef a} h1 h2
      /\ getLength h0 a = getLength h1 a /\ getLength h1 a = getLength h2 a
      /\ getLength h0 b = getLength h1 b /\ getLength h1 b = getLength h2 b
      /\ (norm_length <= getLength h0 a /\ norm_length <= getLength h0 b)
      // Conditions from fdifference_aux
      /\ (modifies !{getRef a} h1 h2)
      /\ (forall (i:nat).
	  ((i>=ctr+1 /\ i<norm_length) ==> (v (getValue h2 a i) = v (getValue h1 b i) - v (getValue h1 a i)))
	  /\ (((i<ctr+1 \/ i >= norm_length) /\ i<getLength h0 a) ==> (getValue h2 a i == getValue h1 a i)))
      // Conditions from fdifference_aux_1
      /\ (forall (i:nat).
	  ((i >= ctr+1 /\ i < norm_length) ==>
	    v (getValue h1 b i) >= v (getValue h1 a i) /\ getValue h1 a i == getValue h0 a i)
	  /\ (((i<ctr \/ i >= norm_length) /\ i<getLength h0 a) ==> getValue h1 a i == getValue h0 a i))
      /\ v (getValue h1 a ctr) = v (getValue h0 b ctr) - v (getValue h0 a ctr)))
    (ensures (
      (live h0 a) /\ (live h0 b) /\ (live h2 a) /\ (live h2 b)
      /\ (norm_length <= getLength h0 a /\ norm_length <= getLength h0 b)
      /\ (modifies !{getRef a} h0 h2)
      /\ (getLength h0 a = getLength h2 a)
      /\ (forall (i:nat). (i>= ctr /\ i<norm_length) ==> (v (getValue h2 a i) = v (getValue h0 b i) - v (getValue h0 a i)))
      ))
      
let fdifference_aux_2_0 h0 h1 h2 a b ctr =
  //@@
  no_upd_lemma h0 h1 b (!{getRef a});
  assert(getLength h0 a = getLength h2 a);
  assert(forall (i:nat). (i>= ctr+1 /\ i<norm_length) ==>
	  (v (getValue h2 a i) = v (getValue h1 b i) - v (getValue h1 a i)));  
  assert(forall (i:nat). (i>=ctr+1 /\ i < norm_length) ==> getValue h1 a i == getValue h0 a i); 
  assert(getValue h2 a ctr == getValue h1 a ctr); 
  assert(v (getValue h1 a ctr) = v (getValue h0 b ctr) - v (getValue h0 a ctr));
  cut(forall (i:nat). (i>= ctr+1 /\ i<norm_length) ==>
	  (v (getValue h2 a i) = v (getValue h0 b i) - v (getValue h0 a i))); 
  cut(True /\ v (getValue h2 a ctr) = v (getValue h0 b ctr) - v (getValue h0 a ctr)); 
  FdifferenceLemmas.helper_lemma_5 ctr norm_length;
  assert(forall (i:nat). (i>=ctr /\ i < norm_length) ==>
	   (v (getValue h2 a i) = v (getValue h0 b i) - v (getValue h0 a i)))

#reset-options

val fdifference_aux_2_1:
  h0:heap -> h1:heap -> h2:heap -> a:bigint -> b:bigint{Similar a b} -> ctr:nat{ctr < norm_length} ->
  Lemma 
    (requires (
      live h0 a /\ live h1 a /\ live h2 a /\ live h0 b /\ live h1 b /\ live h2 b
      /\ modifies !{getRef a} h0 h1 /\ modifies !{getRef a} h1 h2
      /\ getLength h0 a = getLength h1 a /\ getLength h1 a = getLength h2 a
      /\ getLength h0 b = getLength h1 b /\ getLength h1 b = getLength h2 b
      /\ (norm_length <= getLength h0 a /\ norm_length <= getLength h0 b)
      // Conditions from fdifference_aux
      /\ (modifies !{getRef a} h1 h2)
      /\ (forall (i:nat).
	  ((i>=ctr+1 /\ i<norm_length) ==> (v (getValue h2 a i) = v (getValue h1 b i) - v (getValue h1 a i)))
	  /\ (((i<ctr+1 \/ i >= norm_length) /\ i<getLength h0 a) ==> (getValue h2 a i == getValue h1 a i)))
      // Conditions from fdifference_aux_1
      /\ (forall (i:nat).
	  ((i >= ctr+1 /\ i < norm_length) ==>
	    v (getValue h1 b i) >= v (getValue h1 a i) /\ getValue h1 a i == getValue h0 a i)
	  /\ (((i<ctr \/ i >= norm_length) /\ i<getLength h0 a) ==> getValue h1 a i == getValue h0 a i))
      /\ v (getValue h1 a ctr) = v (getValue h0 b ctr) - v (getValue h0 a ctr)))
    (ensures (
      (live h0 a) /\ (live h0 b) /\ (live h2 a) /\ (live h2 b)
      /\ (norm_length <= getLength h0 a /\ norm_length <= getLength h0 b)
      /\ (modifies !{getRef a} h0 h2)
      /\ (getLength h0 a = getLength h2 a)
      /\ (forall (i:nat). ((i<ctr \/ i >= norm_length) /\ i<getLength h0 a) ==> (getValue h2 a i == getValue h0 a i))
    ))

let fdifference_aux_2_1 h0 h1 h2 a b ctr = 
  //@@
  ()


val fdifference_aux_2: 
  h0:heap -> h1:heap -> h2:heap -> a:bigint -> b:bigint{Similar a b} -> ctr:nat{ctr < norm_length} ->
  Lemma
    (requires (
      live h0 a /\ live h1 a /\ live h2 a /\ live h0 b /\ live h1 b /\ live h2 b
      /\ modifies !{getRef a} h0 h1 /\ modifies !{getRef a} h1 h2
      /\ getLength h0 a = getLength h1 a /\ getLength h1 a = getLength h2 a
      /\ getLength h0 b = getLength h1 b /\ getLength h1 b = getLength h2 b
      /\ (norm_length <= getLength h0 a /\ norm_length <= getLength h0 b)
      // Conditions from fdifference_aux
      /\ (modifies !{getRef a} h1 h2)
      /\ (forall (i:nat). 
	  ((i>= ctr+1 /\ i<norm_length) ==>
	    (v (getValue h2 a i) = v (getValue h1 b i) - v (getValue h1 a i)))
	  /\ (((i<ctr+1 \/ i >= norm_length) /\ i<getLength h0 a) ==> (getValue h2 a i == getValue h1 a i)))
      // Conditions from fdifference_aux_1
      /\ (forall (i:nat).
	  ((i >= ctr+1 /\ i < norm_length) ==> v (getValue h1 b i) >= v (getValue h1 a i)
						/\ getValue h1 a i == getValue h0 a i)
	  /\ (((i<ctr \/ i >= norm_length) /\ i<getLength h0 a) ==> getValue h1 a i == getValue h0 a i))
      /\ v (getValue h1 a ctr) = v (getValue h0 b ctr) - v (getValue h0 a ctr)))
    (ensures (
      (live h0 a) /\ (live h0 b) /\ (live h2 a) /\ (live h2 b)
      /\ (norm_length <= getLength h0 a /\ norm_length <= getLength h0 b)
      /\ (modifies !{getRef a} h0 h2)
      /\ (getLength h0 a = getLength h2 a)
      /\ (forall (i:nat).
	  ((i>= ctr /\ i<norm_length) ==> 
	    (v (getValue h2 a i) = v (getValue h0 b i) - v (getValue h0 a i)))
	  /\ (((i<ctr \/ i >= norm_length) /\ i<getLength h0 a) ==> (getValue h2 a i == getValue h0 a i)))
      ))
      
let fdifference_aux_2 h0 h1 h2 a b ctr =
  //@@
  fdifference_aux_2_0 h0 h1 h2 a b ctr;
  fdifference_aux_2_1 h0 h1 h2 a b ctr

#reset-options

val fdifference_aux:
  a:bigint -> b:bigint{Similar a b} -> 
  ctr:nat{ ctr <= norm_length } ->
  ST unit
    (requires (fun h ->
      (live h a) /\ (live h b)
      /\ (norm_length <= getLength h a /\ norm_length <= getLength h b)
      /\ (forall (i:nat). (i >= ctr /\ i < norm_length) ==> (v (getValue h b i) >= v (getValue h a i)))
    ))
    (ensures (fun h0 _ h1 -> 
      (live h0 a) /\ (live h0 b) /\ (live h1 a) /\ (live h1 b)
      /\ (norm_length <= getLength h0 a /\ norm_length <= getLength h0 b)
      /\ (modifies !{getRef a} h0 h1)
      /\ (getLength h0 a = getLength h1 a)
      /\ (forall (i:nat). 
	  ((i>= ctr /\ i<norm_length) ==>  
	    (v (getValue h1 a i) = v (getValue h0 b i) - v (getValue h0 a i)))
	  /\ (((i<ctr \/ i >= norm_length) /\ i<getLength h0 a) ==> (getValue h1 a i == getValue h0 a i)))
    ))
let rec fdifference_aux a b ctr =
  //@@
  let h0 = ST.get() in
  match norm_length - ctr with
  | 0 -> 
    ()
  | _ ->       
      fdifference_aux_1 a b ctr; 
      let h1 = ST.get() in
      no_upd_lemma h0 h1 b (!{getRef a});
      fdifference_aux a b (ctr+1); 
      let h2 = ST.get() in
      fdifference_aux_2 h0 h1 h2 a b ctr

#reset-options

opaque val gsubtraction_lemma_aux:
  h0:heap ->  h1:heap -> a:bigint{(live h0 a) /\ (live h1 a)} -> 
  b:bigint{(live h0 b) /\ (getTemplate b = getTemplate a) } ->
  len:pos{ (len <= getLength h0 a) /\ (len <= getLength h0 b) /\ (len <= getLength h1 a)
	   /\ (forall (i:nat). i < len ==> v (getValue h1 a i) = v (getValue h0 b i) - v (getValue h0 a i)) } ->
  GLemma unit
    (requires ( (eval h0 b (len-1) - eval h0 a (len-1) = eval h1 a (len-1))
		/\ (v (getValue h1 a (len-1)) = v (getValue h0 b (len-1)) - v (getValue h0 a (len-1))) ) )
    (ensures (eval h0 b len - eval h0 a len = eval h1 a len)) []
let gsubtraction_lemma_aux h0 h1 a b len =
  //@@
  eval_definition h1 a len;
  assert(eval h1 a len = pow2 (bitweight (getTemplate a) (len-1)) * v (getValue h1 a (len-1)) + eval h1 a (len-1));
  assert(v (getValue h1 a (len-1)) = v (getValue h0 b (len-1)) - v (getValue h0 a (len-1))); 
  Axiomatic.distributivity_sub_right (pow2 (bitweight (getTemplate a) (len-1))) (v (getValue h0 b (len-1)))  (v (getValue h0 a (len-1))); 
  assert(eval h1 a len = (pow2 (bitweight (getTemplate a) (len-1)) * v (getValue h0 b (len-1)) - pow2 (bitweight (getTemplate a) (len-1)) * v (getValue h0 a (len-1))) + eval h1 a (len-1));
  FdifferenceLemmas.helper_lemma_2 
		(pow2 (bitweight (getTemplate a) (len-1)) * v (getValue h0 b (len-1)))
		(pow2 (bitweight (getTemplate a) (len-1)) * v (getValue h0 a (len-1)))
		(eval h0 b (len-1))
		(eval h0 a (len-1));
  eval_definition h0 a len;
  eval_definition h0 b len

#reset-options

val subtraction_lemma_aux:
  h0:heap ->  h1:heap -> a:bigint{(live h0 a) /\ (live h1 a)} -> 
  b:bigint{(live h0 b) /\ (getTemplate b = getTemplate a) } ->
  len:pos{ (len <= getLength h0 a) /\ (len <= getLength h0 b) /\ (len <= getLength h1 a)
	   /\ (forall (i:nat{ i < len }). v (getValue h1 a i) = v (getValue h0 b i) - v (getValue h0 a i)) } ->
  Lemma
    (requires ( (eval h0 b (len-1) - eval h0 a (len-1) = eval h1 a (len-1))
		/\ (v (getValue h1 a (len-1)) = v (getValue h0 b (len-1)) - v (getValue h0 a (len-1))) ) )
    (ensures (eval h0 b len - eval h0 a len = eval h1 a len))
let subtraction_lemma_aux h0 h1 a b len =
  coerce
      (requires ( (eval h0 b (len-1) - eval h0 a (len-1) = eval h1 a (len-1))
		/\ (v (getValue h1 a (len-1)) = v (getValue h0 b (len-1)) - v (getValue h0 a (len-1))) ) )
      (ensures (eval h0 b len - eval h0 a len = eval h1 a len))
      (fun _ -> gsubtraction_lemma_aux h0 h1 a b len)

val subtraction_lemma:
  h0:heap -> h1:heap -> a:bigint{(live h0 a) /\ (live h1 a)} -> 
  b:bigint{(live h0 b) /\ (getTemplate b = getTemplate a) } ->
  len:nat{ (len <= getLength h0 a) /\ (len <= getLength h0 b) /\ (len <= getLength h1 a)
	  /\ (forall (i:nat). i < len ==> v (getValue h1 a i) = v (getValue h0 b i) - v (getValue h0 a i)) } ->
  Lemma
    (requires (True))
    (ensures ( eval h0 b len - eval h0 a len = eval h1 a len ))
let rec subtraction_lemma h0 h1 a b len =
  //@@
  match len with
  | 0 -> ()
  | _ -> subtraction_lemma h0 h1 a b (len-1);
    subtraction_lemma_aux h0 h1 a b len

#reset-options

val subtraction_max_value_lemma:
  h0:heap -> 
  h1:heap -> 
  a:bigint{ (live h0 a) } -> 
  b:bigint{ (live h0 b) /\ (getLength h0 a = getLength h0 b) } ->
  c:bigint{ (live h1 c) /\ (getLength h1 c = getLength h0 a)
	    /\ (forall (i:nat). (i<getLength h1 c) ==>
		v (getValue h1 c i) = v (getValue h0 b i) - v (getValue h0 a i)) } ->
  Lemma
    (requires (True))
    (ensures (maxValue h1 c <= maxValue h0 b))
let subtraction_max_value_lemma h0 h1 a b c = 
  //@@
  ()

#reset-options

val max_value_lemma: 
  h:heap -> a:bigint{ live h a } -> m:nat ->
  Lemma 
    (requires (forall (n:nat). n < getLength h a ==> v (getValue h a n) <= m))
    (ensures (maxValue h a <= m))
let max_value_lemma h a m = 
  //@@
  ()

val subtraction_max_value_lemma_extended:
  h0:heap -> h1:heap -> a:bigint{live h0 a /\ getLength h0 a >= norm_length} -> 
  b:bigint{live h0 b /\ getLength h0 b >= norm_length} ->
  c:bigint{live h1 c /\ getLength h0 a = getLength h1 c} -> 
  Lemma
    (requires ((forall (i:nat). (i<norm_length) ==> 
		  v (getValue h1 c i) = v (getValue h0 b i) - v (getValue h0 a i))
	       /\ (forall (i:nat). (i < getLength h1 c /\ i >= norm_length) ==>
		   v (getValue h1 c i) = v (getValue h0 a i))))
    (ensures (maxValue h1 c <= max (maxValue h0 a) (maxValue h0 b)))
    
let subtraction_max_value_lemma_extended h0 h1 a b c = 
  //@@
  cut ( forall (i:nat). (i < getLength h1 c /\ i >= norm_length)
	==> (v (getValue h1 c i) = v (getValue h0 a i) /\ v (getValue h1 c i) <= maxValue h0 a));
  cut ( forall (i:nat). (i < getLength h1 c /\ i >= norm_length)
  	==> v (getValue h1 c i) <= max (maxValue h0 a) (maxValue h0 b));	
  assert ( forall (i:nat). (i < norm_length)
	==> v (getValue h1 c i) = v (getValue h0 b i) - v (getValue h0 a i));
  assert(forall (i:nat). (i < norm_length) ==> v (getValue h1 c i) = v (getValue h0 b i) - v (getValue h0 a i) ==> v (getValue h1 c i) <= v (getValue h0 b i) ==> v (getValue h1 c i) <= maxValue h0 b); 
  cut ( forall (i:nat). (i < norm_length)
	==> v (getValue h1 c i) <= maxValue h0 b); 
  cut ( forall (i:nat). (i < norm_length)
	==> (v (getValue h0 a i) <= maxValue h0 a /\ v (getValue h0 b i) <= maxValue h0 b)); 
  cut ( forall (i:nat). (i < norm_length)
	==> v (getValue h1 c i) <= max (maxValue h0 a) (maxValue h0 b))

#reset-options

opaque val gauxiliary_lemma_2: 
  ha:heap -> a:bigint{Standardized ha a} -> 
  min:pos{(forall (i:nat). i < norm_length ==> templ i <= min)} -> max:pos{max <= platform_size} ->
  hb:heap -> b:bigint{Filled hb b min max} -> i:nat{ i < norm_length} ->
  GLemma unit 
    (requires (True))
    (ensures (bitsize (v (getValue hb b i) - v (getValue ha a i)) max))
    []
    
let gauxiliary_lemma_2 ha a min max hb b i =
  //@@
  assert(True /\ bitsize (v (getValue hb b i)) max); 
  Lemmas.pow2_increases_2 min (templ i); 
  assert(bitsize (v (getValue ha a i)) (templ i)); 
  assert(v (getValue ha a i) < pow2 (templ i)); 
  cut(True /\ v (getValue ha a i) < pow2 min); 
  assert(bitsize (v (getValue ha a i)) min); 
  UInt.sub_lemma #max (v (getValue hb b i)) (v (getValue ha a i))

#reset-options

val auxiliary_lemma_2: 
  ha:heap -> a:bigint{Standardized ha a} -> 
  min:pos{(forall (i:nat). i < norm_length ==> templ i <= min)} -> max:pos{max <= platform_size} ->
  hb:heap -> b:bigint{Filled hb b min max} -> i:nat{ i < norm_length} ->
  Lemma 
    (requires (True))
    (ensures (bitsize (v (getValue hb b i) - v (getValue ha a i)) max))    
    [SMTPat (bitsize (v (getValue hb b i) - v (getValue ha a i))  max)]
let auxiliary_lemma_2 ha a min max hb b i =
  coerce
    (requires (True))
    (ensures (bitsize (v (getValue hb b i) - v (getValue ha a i)) max))
    (fun _ -> gauxiliary_lemma_2 ha a min max hb b i)

#reset-options

val auxiliary_lemma_0: 
  ha:heap -> a:bigint{Standardized ha a} -> 
  min:pos{(forall (i:nat). {:pattern (templ i)} i < norm_length ==> templ i <= min)} -> 
  max:pos{max <= platform_size} ->
  hb:heap -> b:bigint{Filled hb b min max} ->
  Lemma (requires (True))
	(ensures (forall (i:nat). i < norm_length ==> bitsize (v (getValue hb b i) - v (getValue ha a i)) max))
let auxiliary_lemma_0 ha a min max hb b = 
  //@@
  ()

#reset-options

val auxiliary_lemma_1:
  h0:heap -> h1:heap -> mods:FStar.Set.set aref ->
  min:pos{(forall (i:nat). i < norm_length ==> templ i <= min)} -> max:pos{max <= platform_size} ->
  b:bigint{Filled h0 b min max} -> 
  Lemma (requires (live h1 b /\ modifies mods h0 h1 /\ not(FStar.Set.mem (Ref (getRef b)) mods)))
	(ensures (Filled h1 b min max))
let auxiliary_lemma_1 h0 h1 mods min max b = 
  //@@
  assert(FStar.Seq.Eq (sel h0 (getRef b)) (sel h1 (getRef b))); 
  ()

#reset-options

val fdifference':
  a:bigint ->   min:pos{(forall (i:nat). i < norm_length ==> templ i <= min)} -> max:pos{max <= platform_size} ->
  b:bigint{Similar a b} -> 
  ST unit
    (requires (fun h -> Standardized h a /\ Filled h b min max))
    (ensures (fun h0 u h1 -> 
      Standardized h0 a /\ Filled h0 b min max /\ Filled h1 b min max
      /\ (live h1 a) /\ (modifies !{getRef a} h0 h1) 
      /\ (getLength h1 a = getLength h0 a) /\ (getLength h0 b = getLength h1 b)
      /\ (eval h1 a norm_length = eval h0 b norm_length - eval h0 a norm_length)
      /\ (forall (i:nat). i < norm_length ==> v (getValue h1 a i) = v (getValue h0 b i) - v (getValue h0 a i))
    ))
let fdifference' a min max b =
  //@@
  let h0 = ST.get() in
  auxiliary_lemma_0 h0 a min max h0 b; 
  fdifference_aux a b 0; 
  let h1 = ST.get() in
  auxiliary_lemma_1 h0 h1 (!{getRef a}) min max b ; 
  subtraction_lemma h0 h1 a b norm_length


