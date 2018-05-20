(*--build-config
  options:--admit_fsi FStar.Set --admit_fsi Parameters --admit_fsi Fsum --admit_fsi FsumWide --admit_fsi Fscalar --verify_module Fproduct --z3rlimit 50;
  other-files:FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi seq.fsi FStar.Seq.Base.fst FStar.Seq.Properties.fst FStar.Seq.fst FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Array.fst FStar.Ghost.fst axiomatic.fst intlib.fst lemmas.fst parameters.fsti uint.fst bigint.fst eval.fst fsum.fsti fsum_wide.fsti fscalar.fsti fproduct_lemmas.fst;
  --*)

module Fproduct

open FStar.Heap
open IntLib
open Parameters
open UInt
open Bigint
open Eval
open Fscalar

(* Type of bigintegers with constant template *)
opaque type ConstantTemplate (#size:pos) (b:biginteger size) = 
  (forall (i:nat). {:pattern (getTemplate b i)} 
    getTemplate b i = getTemplate b 0)

val constant_template_lemma: #size_a:pos -> a:biginteger size_a -> #size_b:pos -> b:biginteger size_b ->
  Lemma
    (requires (ConstantTemplate a /\ getTemplate a = getTemplate b))
    (ensures (ConstantTemplate b))
    [SMTPat (Similar a b)]
let constant_template_lemma #size_a a #size_b b = 
  //@@
  assert(getTemplate b 0 = getTemplate a 0)

(* Lemma : additivity property of the "bitweight" function if the template is normalized *)
val bitweight_lemma_1:
  t:template{forall (n:nat). t n = t 0} -> i:nat ->
  Lemma (bitweight t i = i * (t 0))
let rec bitweight_lemma_1 t i = 
  //@@
  match i with
  | 0 -> ()
  | _ -> 
    FproductLemmas.auxiliary_lemma_2 i;
    assert(t (i-1) = t 0); 
    assert(bitweight t i = t 0 + bitweight t (i-1));
    bitweight_lemma_1 t (i-1);
    FproductLemmas.auxiliary_lemma_3 (t 0) i

val bitweight_lemma_0:
  t:template{ forall (n:nat). t n = t 0 } -> i:nat -> j:nat -> 
  Lemma
    (requires (True))
    (ensures ( bitweight t (i+j) = bitweight t i + bitweight t j))
let rec bitweight_lemma_0 t i j =
  //@@
  bitweight_lemma_1 t (i+j); 
  bitweight_lemma_1 t i; bitweight_lemma_1 t j;
  FproductLemmas.auxiliary_lemma_4 (t 0) i j

(* Lemma : combines the additivity property of the bitweight function and the exponential property 
   of the pow2 function *)
val auxiliary_lemma_1: 
  t:template{ forall (n:nat). t n = t 0 } -> a:nat -> b:nat -> 
  Lemma (ensures (pow2 (bitweight t (a+b)) = pow2 (bitweight t a) * pow2 (bitweight t b)))
let auxiliary_lemma_1 t a b =
  //@@
  bitweight_lemma_0 t a b;
  Lemmas.pow2_exp_1 (bitweight t a) (bitweight t b)

opaque type PartialEquality (ha:heap) (#size_a:pos) (a:biginteger size_a{live ha a})
			    (hb:heap) (#size_b:pos) (b:biginteger size_b{live hb b}) 
			    (len:nat{len <= getLength ha a /\ len <= getLength hb b}) =
  (forall (i:nat). {:pattern (v (getValue ha a i))}
    i < len ==> v (getValue ha a i) = v (getValue hb b i))

opaque type StoresSum (hc:heap) (#size_c:pos) (c:biginteger size_c{live hc c})
		      (ha:heap) (#size_a:pos) (a:biginteger size_a{live ha a})
		      (hb:heap) (#size_b:pos) (b:biginteger size_b{live hb b})
		      (a_idx:nat)
		      (len:nat{a_idx+len <= getLength ha a /\ len <= getLength hb b /\ a_idx+len <= getLength hc c}) =
 (forall (i:nat). {:pattern (v (getValue hc c (i+a_idx)))}
   (i < len ==> v (getValue hc c (i+a_idx)) = v (getValue ha a (i+a_idx)) + v (getValue hb b i)))
			      
opaque val gmultiplication_step_lemma_1:
  h0:heap -> h1:heap -> a:bigint_wide{ConstantTemplate a /\ live h0 a} -> 
  b:bigint_wide{getTemplate a = getTemplate b /\ live h0 b} ->
  c:bigint_wide{getTemplate c = getTemplate a /\ live h1 c} ->
  idx:nat -> len:pos{(len+idx <= getLength h0 a) /\ (len <= getLength h0 b) /\ (getLength h0 a = getLength h1 c) } ->
  GLemma unit
    (requires (
      (StoresSum h1 c h0 a h0 b idx len)
      /\ (PartialEquality h1 c h0 a idx)
      /\ (eval h1 c (len-1+idx) = eval h0 a (len-1+idx) + pow2 (bitweight (getTemplate a) idx) * eval h0 b (len-1))))
    (ensures (eval h1 c (len+idx) = eval h0 a (len+idx) +  
		          pow2 (bitweight (getTemplate a) idx) * eval h0 b (len-1)  +	        
			  pow2 (bitweight (getTemplate a) (len-1+idx)) * v (getValue h0 b (len-1))))
    []
    
let gmultiplication_step_lemma_1 h0 h1 a b c idx len =
  //@@
  let t = getTemplate a in
  FproductLemmas.auxiliary_lemma_0 len idx 1; 
  eval_definition h1 c (len+idx); 
  FproductLemmas.auxiliary_lemma_00 len idx 1;   
  cut (v (getValue h1 c (len+idx-1)) = v (getValue h0 a (len+idx-1)) + v (getValue h0 b (len-1)) /\ True); 
  cut (True /\ eval h1 c (len+idx) = pow2 (bitweight t (len+idx-1)) * v (getValue h1 c (len+idx-1)) + eval h1 c (len+idx-1)); 
  cut (eval h1 c (len+idx) = eval h1 c (len+idx-1) + pow2 (bitweight t (len+idx-1)) * v (getValue h1 c (len+idx-1)) /\ True );
  cut (eval h1 c (len+idx-1) = eval h0 a (len+idx-1) + (pow2 (bitweight t idx)) * eval h0 b (len-1) /\ True); 
  cut (v (getValue h1 c (len+idx-1)) = v (getValue h0 a (len+idx-1)) + v (getValue h0 b (len-1)) /\ True); 
  cut (eval h1 c (len+idx) = 
	(eval h0 a (len+idx-1) + (pow2 (bitweight t idx)) * eval h0 b (len-1))
	+ pow2 (bitweight t (len-1+idx)) * (v (getValue h0 a (len+idx-1)) + v (getValue h0 b (len-1))) /\ True); 
  Axiomatic.distributivity_add_right (pow2 (bitweight t (len-1+idx))) (v (getValue h0 a (len+idx-1))) (v (getValue h0 b (len-1))); 
  cut (True /\ eval h1 c (len+idx) = 
	(eval h0 a (len+idx-1) + (pow2 (bitweight t idx)) * eval h0 b (len-1))
	+ (pow2 (bitweight t (len-1+idx)) * v (getValue h0 a (len+idx-1))
        + pow2 (bitweight t (len-1+idx)) * v (getValue h0 b (len-1)))); 
  FproductLemmas.remove_paren_lemma (eval h0 a (len+idx-1)) ((pow2 (bitweight t idx)) * eval h0 b (len-1)) ((pow2 (bitweight t (len-1+idx)) * v (getValue h0 a (len+idx-1)) + pow2 (bitweight t (len-1+idx)) * v (getValue h0 b (len-1)))); 
  cut (True /\ eval h1 c (len+idx) = 
	eval h0 a (len+idx-1) + (pow2 (bitweight t idx)) * eval h0 b (len-1)
	+ (pow2 (bitweight t (len-1+idx)) * v (getValue h0 a (len+idx-1))
        + pow2 (bitweight t (len-1+idx)) * v (getValue h0 b (len-1))));
  FproductLemmas.remove_paren_lemma (eval h0 a (len+idx-1) + (pow2 (bitweight t idx)) * eval h0 b (len-1)) 
		     (pow2 (bitweight t (len-1+idx)) * v (getValue h0 a (len+idx-1)))
		     (pow2 (bitweight t (len-1+idx)) * v (getValue h0 b (len-1))); 
  cut (True /\ eval h1 c (len+idx) = 
	eval h0 a (len+idx-1) + pow2 (bitweight t idx) * eval h0 b (len-1)  +
	pow2 (bitweight t (len-1+idx)) * v (getValue h0 a (len+idx-1)) +    	        
          pow2 (bitweight t (len-1+idx)) * v (getValue h0 b (len-1))); 
  FproductLemmas.auxiliary_lemma_6 (eval h0 a (len+idx-1)) 
				  (pow2 (bitweight t idx) * eval h0 b (len-1))
				  (pow2 (bitweight t (len-1+idx)) * v (getValue h0 a (len+idx-1)))    
				  (pow2 (bitweight t (len-1+idx)) * v (getValue h0 b (len-1)));
  cut (True /\ eval h1 c (len+idx) = 
	pow2 (bitweight t (len-1+idx)) * v (getValue h0 a (len+idx-1)) + eval h0 a (len+idx-1) + 
          pow2 (bitweight t idx) * eval h0 b (len-1)  +	        
          pow2 (bitweight t (len-1+idx)) * v (getValue h0 b (len-1))); 
  eval_definition h0 a (len+idx);
  cut (True /\ eval h0 a (len+idx) = pow2 (bitweight t (len+idx-1)) * v (getValue h0 a (len+idx-1)) + eval h0 a (len+idx-1)); 
  cut (True /\ eval h1 c (len+idx) = 
		eval h0 a (len+idx) 
		+ pow2 (bitweight t idx) * eval h0 b (len-1)  
		+ pow2 (bitweight t (len-1+idx)) * v (getValue h0 b (len-1)))

#reset-options

val multiplication_step_lemma_1:
  h0:heap -> h1:heap -> a:bigint_wide{ConstantTemplate a /\ live h0 a} -> 
  b:bigint_wide{getTemplate a = getTemplate b /\ live h0 b} ->
  c:bigint_wide{getTemplate c = getTemplate a /\ live h1 c} ->
  idx:nat -> len:pos{(len+idx <= getLength h0 a) /\ (len <= getLength h0 b) /\ (getLength h0 a = getLength h1 c) } ->
  Lemma 
    (requires (
      (StoresSum h1 c h0 a h0 b idx len)
      /\ (PartialEquality h1 c h0 a idx)
      /\ (eval h1 c (len-1+idx) = eval h0 a (len-1+idx) + pow2 (bitweight (getTemplate a) idx) * eval h0 b (len-1))))
    (ensures (eval h1 c (len+idx) = eval h0 a (len+idx) +  
		          pow2 (bitweight (getTemplate a) idx) * eval h0 b (len-1)  +	        
			  pow2 (bitweight (getTemplate a) (len-1+idx)) * v (getValue h0 b (len-1))))
let multiplication_step_lemma_1 h0 h1 a b c idx len = 
  coerce
    (requires (
      (StoresSum h1 c h0 a h0 b idx len)
      /\ (PartialEquality h1 c h0 a idx)    
      /\ (eval h1 c (len-1+idx) = eval h0 a (len-1+idx) + pow2 (bitweight (getTemplate a) idx) * eval h0 b (len-1))))
    (ensures (eval h1 c (len+idx) = eval h0 a (len+idx) +  
		          pow2 (bitweight (getTemplate a) idx) * eval h0 b (len-1)  +	        
			  pow2 (bitweight (getTemplate a) (len-1+idx)) * v (getValue h0 b (len-1))))
    (fun _ -> gmultiplication_step_lemma_1 h0 h1 a b c idx len)
    
#reset-options

(* Lemma : second half of the helper for the multiplication_step_lemma *)
opaque val gmultiplication_step_lemma_2:
  h0:heap -> h1:heap -> a:bigint_wide{ConstantTemplate a /\ live h0 a } -> 
  b:bigint_wide{getTemplate b = getTemplate a /\ live h0 b } -> 
  c:bigint_wide{getTemplate c = getTemplate a /\ live h1 c } -> idx:nat ->
  len:pos{(len+idx <= getLength h0 a) /\ (len <= getLength h0 b) /\ (getLength h0 a = getLength h1 c)} ->
  GLemma unit
    (requires (
	 eval h1 c (len+idx) = eval h0 a (len+idx) +  
                          pow2 (bitweight (getTemplate a) idx) * eval h0 b (len-1)  +	        
			  pow2 (bitweight (getTemplate a) (len-1+idx)) * v (getValue h0 b (len-1))
    ))
    (ensures (eval h1 c (len+idx) = eval h0 a (len+idx) + pow2 (bitweight (getTemplate a) idx) * eval h0 b len))
    []
let gmultiplication_step_lemma_2 h0 h1 a b c idx len = 
  //@@
  FproductLemmas.auxiliary_lemma_0 len idx 1;
  auxiliary_lemma_1 (getTemplate a) idx (len-1); 
  FproductLemmas.auxiliary_lemma_00 len (-1) idx;
  FproductLemmas.auxiliary_lemma_01 (len-1) idx; 
  cut (True /\ pow2 (bitweight (getTemplate a) (len-1+idx)) = pow2 (bitweight (getTemplate a) idx) * pow2 (bitweight (getTemplate a) (len-1)) ); 
  Axiomatic.paren_mul_left (pow2 (bitweight (getTemplate a) idx)) (pow2 (bitweight (getTemplate a) (len-1))) (v (getValue h0 b (len-1))); 
  cut (eval h1 c (len+idx) = eval h0 a (len+idx) 
			     + pow2 (bitweight (getTemplate a) idx) * eval h0 b (len-1)
			     + pow2 (bitweight (getTemplate a) idx) * pow2 (bitweight (getTemplate a) (len-1)) * v (getValue h0 b (len-1)) /\ True); 
  Axiomatic.distributivity_add_right (pow2 (bitweight (getTemplate a) idx)) (eval h0 b (len-1)) (pow2 (bitweight (getTemplate a) (len-1)) * v (getValue h0 b (len-1)));  
  eval_definition h0 b len; 
  cut (True /\ eval h0 b len = eval h0 b (len-1) + (pow2 (bitweight (getTemplate a) (len-1))) * v (getValue h0 b (len-1)) );  
  cut (True /\ pow2 (bitweight (getTemplate a) (len-1+idx)) * v (getValue h0 b (len-1)) =
        pow2 (bitweight (getTemplate a) idx) * pow2 (bitweight (getTemplate a) (len-1)) * v (getValue h0 b (len-1))); 
  cut ( True /\ eval h1 c (len+idx) = eval h0 a (len+idx) + pow2 (bitweight (getTemplate a) idx) * eval h0 b len) 

#reset-options

val multiplication_step_lemma_2:
  h0:heap -> h1:heap -> a:bigint_wide{ConstantTemplate a /\ live h0 a } -> 
  b:bigint_wide{getTemplate b = getTemplate a /\ live h0 b } -> 
  c:bigint_wide{getTemplate c = getTemplate a /\ live h1 c } -> idx:nat ->
  len:pos{(len+idx <= getLength h0 a) /\ (len <= getLength h0 b) /\ (getLength h0 a = getLength h1 c)} ->
  Lemma 
    (requires (
	 eval h1 c (len+idx) = eval h0 a (len+idx) +  
                          pow2 (bitweight (getTemplate a) idx) * eval h0 b (len-1)  +	        
			  pow2 (bitweight (getTemplate a) (len-1+idx)) * v (getValue h0 b (len-1))
    ))
    (ensures (eval h1 c (len+idx) = eval h0 a (len+idx) + pow2 (bitweight (getTemplate a) idx) * eval h0 b len))
let multiplication_step_lemma_2 h0 h1 a b c idx len = 
  coerce
    (requires (
	 eval h1 c (len+idx) = eval h0 a (len+idx) +  
                          pow2 (bitweight (getTemplate a) idx) * eval h0 b (len-1)  +	        
			  pow2 (bitweight (getTemplate a) (len-1+idx)) * v (getValue h0 b (len-1))
    ))
    (ensures (eval h1 c (len+idx) = eval h0 a (len+idx) + pow2 (bitweight (getTemplate a) idx) * eval h0 b len))
    (fun _ -> gmultiplication_step_lemma_2 h0 h1 a b c idx len)

#reset-options

(* Lemma : changes the result of the addition function into the equivalent relation between 
  evaluated bigints *)
val multiplication_step_lemma:
  h0:heap -> h1:heap -> a:bigint_wide{ConstantTemplate a /\ live h0 a } -> 
  b:bigint_wide{ live h0 b /\ getTemplate b = getTemplate a } -> 
  c:bigint_wide{ live h1 c /\ getTemplate c = getTemplate a } -> idx:nat ->
  len:nat{(len+idx <= getLength h0 a) /\ (len <= getLength h0 b) /\ (getLength h0 a = getLength h1 c) } ->
  Lemma
    (requires (
      (StoresSum h1 c h0 a h0 b idx len)
      /\ (PartialEquality h1 c h0 a idx)
    ))
    (ensures (eval h1 c (len+idx) = eval h0 a (len+idx) + pow2 (bitweight (getTemplate a) idx) * eval h0 b len
    ))
let rec multiplication_step_lemma h0 h1 a b c idx len =
  //@@
  match len with
  | 0 ->
    cut (forall (i:nat). i < idx ==> v (getValue h1 c i) = v (getValue h0 a i)); 
    eval_eq_lemma h0 h1 a c idx; 
    FproductLemmas.auxiliary_lemma_02 len idx;
    cut (True /\ len+idx = idx); 
    cut (True /\ eval h0 b len = 0);
    FproductLemmas.auxiliary_lemma_03 (pow2 (bitweight (getTemplate a) idx));
    cut (True /\ pow2 (bitweight (getTemplate a) idx) * 0 = 0);
    cut (True /\ eval h1 c (len+idx) = eval h0 a (len+idx))
  | _ ->   
     FproductLemmas.auxiliary_lemma_0 len idx 1; 
     FproductLemmas.auxiliary_lemma_2 len;
     multiplication_step_lemma h0 h1 a b c idx (len-1); 
     multiplication_step_lemma_1 h0 h1 a b c idx len; 
     multiplication_step_lemma_2 h0 h1 a b c idx len

#reset-options

let (max_limb:nat) = parameters_lemma_1 (); (platform_wide - log_2 norm_length - 1) / 2
let (max_wide:nat) = 2 * max_limb

opaque type FitsMaxLimbSize (h:heap) (#size:pos) 
			    (a:biginteger size{ConstantTemplate a /\ live h a /\ getLength h a >= norm_length}) =
  (forall (i:nat). {:pattern (v (getValue h a i))}
    i < norm_length ==> bitsize (v (getValue h a i)) max_limb)
  
(* Lemma *)
val auxiliary_lemma_2:
  h0:heap -> h1:heap -> h2:heap ->
  a:bigint{ ConstantTemplate a /\ (live h0 a) /\ (getLength h0 a >= norm_length)
            /\ FitsMaxLimbSize h0 a } ->
  b:bigint{ (live h1 b) /\ (getTemplate a = getTemplate b) /\ (getLength h1 b >= norm_length) /\ (forall (i:nat). i < norm_length ==> bitsize (v (getValue h1 b i)) max_limb) } ->
  ctr:nat{(ctr <= norm_length)} ->
  c:bigint{(live h2 c) /\ (maxValue h2 c <= ctr * (maxValueNorm h0 a * maxValueNorm h1 b)) } ->
  Lemma
    (requires (True))
    (ensures ((maxValueNorm h0 a <= pow2 max_limb) 
	    /\ (maxValueNorm h1 b <= pow2 max_limb)))
let auxiliary_lemma_2 h0 h1 h2 a b ctr c = 
  //@@
  ()

#reset-options

(* Lemma : bounds the maxValues product *)
val auxiliary_lemma_3:
  h0:heap -> h1:heap -> h2:heap ->
  a:bigint{ConstantTemplate a /\ (live h0 a) /\ (getLength h0 a >= norm_length)
    /\ (maxValueNorm h0 a <= pow2 max_limb) } ->
  b:bigint{ (live h1 b) /\ (getTemplate b = getTemplate b) 
    /\ (getLength h1 b >= norm_length) /\ (maxValueNorm h1 b <= pow2 max_limb) } ->
  ctr:nat{ (ctr <= norm_length) } ->
  c:bigint_wide{ 
      (live h2 c)
      /\ (maxValue h2 c <= ctr * (maxValueNorm h0 a * maxValueNorm h1 b)) } ->
  Lemma
    (requires (True))
    (ensures (maxValueNorm h0 a * maxValueNorm h1 b <= pow2 max_wide))
let auxiliary_lemma_3 h0 h1 h2 a b ctr c =
  //@@
  let s = max_wide in
  Axiomatic.slash_star_axiom max_limb 2 max_wide;
  cut (max_limb = s / 2 /\ True); 
  FproductLemmas.helper_lemma_3 (maxValueNorm h0 a) (maxValueNorm h1 b) (pow2 max_limb) (pow2 max_limb);
  Lemmas.pow2_exp_1 (s/2) (s/2); 
  cut (maxValueNorm h0 a * maxValueNorm h1 b <= pow2 ((s/2)+(s/2)) /\ True); 
  FproductLemmas.helper_lemma_2 (s/2);
  Lemmas.multiply_fractions s 2; 
  cut ((s / 2)+(s/2) <= (s) /\ True);
  if (((s/2)+(s/2)) < s ) then
	Lemmas.pow2_increases_1 s ((s/2)+(s/2));
  cut (pow2 (((s/2)+(s/2))) <= pow2 s /\ True); 
  cut (maxValueNorm h0 a * maxValueNorm h1 b <= pow2 s /\ True)

#reset-options

opaque type PartialEquality2 (ha:heap) (#size_a:pos) (a:biginteger size_a{live ha a})
			    (hb:heap) (#size_b:pos) (b:biginteger size_b{live hb b}) 
			    (len:nat)
			    (len2:nat{ len2 >= len /\ len2 <= getLength ha a /\ len2 <= getLength hb b}) =
  (forall (i:nat). {:pattern (v (getValue ha a i))}
    (i < len2 /\ i >= len) ==> v (getValue ha a i) = v (getValue hb b i))

(* Lemma : extends the "eval" property to the total length if apporpriate *)
opaque val gauxiliary_lemma_5: 
  h0:heap -> h1:heap -> #size_a:pos -> a:biginteger size_a{live h0 a } -> 
  #size_b:pos -> b:biginteger size_b{(live h1 b) /\ (getTemplate a = getTemplate b) } ->
  c:int -> len:nat -> len2:nat{ len2 >= len /\ len2 <= getLength h1 b /\ len2 <= getLength h0 a } ->
  GLemma unit
    (requires ( (eval h1 b len = eval h0 a len + c)
		/\ PartialEquality2 h1 b h0 a len len2))
    (ensures ( (eval h1 b len2 = eval h0 a len2 + c)))
    []
let rec gauxiliary_lemma_5 h0 h1 #size_a a #size_b b c len len2 =
  //@@
  match len2 - len with
  | 0 -> 
     FproductLemmas.auxiliary_lemma_8 len2 len
  | _ ->
     let t = getTemplate a in
     FproductLemmas.auxiliary_lemma_7 len2 len;
     gauxiliary_lemma_5 h0 h1 a b c len (len2-1); 
     cut (True /\ eval h1 b (len2-1) = eval h0 a (len2-1) + c); 
     eval_definition h1 b len2; 
     cut (True /\ eval h1 b len2 = eval h1 b (len2-1) + (pow2 (bitweight t (len2-1))) * v (getValue h1 b (len2-1))); 
     cut (v (getValue h1 b (len2-1)) = v (getValue h0 a (len2-1)) /\ True); 
     cut (True /\ eval h1 b len2 = (eval h0 a (len2-1) + c) + (pow2 (bitweight t (len2-1))) * v (getValue h0 a (len2-1))); 
     FproductLemmas.auxiliary_lemma_04 (eval h0 a (len2-1)) c ((pow2 (bitweight t (len2-1))) * v (getValue h0 a (len2-1)));  
     eval_definition h0 a len2;
     cut (True /\ eval h1 b len2 = eval h0 a len2 + c)

val auxiliary_lemma_5: 
  h0:heap -> h1:heap -> #size_a:pos -> a:biginteger size_a{live h0 a } -> 
  #size_b:pos -> b:biginteger size_b{(live h1 b) /\ (getTemplate a = getTemplate b) } ->
  c:int -> len:nat -> len2:nat{ len2 >= len /\ len2 <= getLength h1 b /\ len2 <= getLength h0 a } ->
  Lemma 
    (requires ( (eval h1 b len = eval h0 a len + c)
		/\ PartialEquality2 h1 b h0 a len len2))
    (ensures ( (eval h1 b len2 = eval h0 a len2 + c)))
let auxiliary_lemma_5 h0 h1 #size_a a #size_b b c len len2 =
  coerce 
    (requires ( (eval h1 b len = eval h0 a len + c)
		/\ PartialEquality2 h1 b h0 a len len2))
    (ensures ( (eval h1 b len2 = eval h0 a len2 + c)))
    (fun _ -> gauxiliary_lemma_5 h0 h1 #size_a a #size_b b c len len2)

#reset-options

opaque type IsScalarProduct 
  (hc:heap) (#size_c:pos) (c:biginteger size_c{live hc c /\ getLength hc c >= norm_length})
  (ha:heap) (#size_a:pos) (a:biginteger size_a{live ha a /\ getLength ha a >= norm_length})
  (s:usint size_a) =
    (forall (i:nat). {:pattern (v (getValue hc c i))}
      (i<norm_length) ==> v (getValue hc c i) = v (getValue ha a i) * v s)  
  
val max_limb_lemma: a:nat -> b:nat -> 
  Lemma
    (requires (a < pow2 max_limb /\ b < pow2 max_limb))
    (ensures (a * b < pow2 platform_wide))
    [SMTPat (a * b)]
let max_limb_lemma a b =
  FproductLemmas.ineq_lemma_3 a b (pow2 max_limb);
  Lemmas.pow2_exp_1 max_limb max_limb;
  FproductLemmas.helper_lemma_10 max_limb;  
  Parameters.parameters_lemma_1 (); 
  FproductLemmas.helper_lemma_11 platform_wide (log_2 norm_length) max_limb; 
  Lemmas.pow2_increases_1 platform_wide max_wide

opaque val gmax_limb_lemma2: h:heap -> a:bigint{live h a} -> b:bigint{live h b} -> i:nat{i < getLength h a} -> ctr:nat{ctr < getLength h b} ->
  GLemma unit
    (requires (v (getValue h a i) < pow2 max_limb /\ v (getValue h b ctr) < pow2 max_limb))
    (ensures (v (getValue h a i) * v (getValue h b ctr) < pow2 platform_wide))
    []
let gmax_limb_lemma2 h a b i ctr =
  max_limb_lemma (v (getValue h a i)) (v (getValue h b ctr))

val max_limb_lemma2: h:heap -> a:bigint{live h a} -> b:bigint{live h b} -> i:nat{i < getLength h a} -> ctr:nat{ctr < getLength h b} ->
  Lemma
    (requires (v (getValue h a i) < pow2 max_limb /\ v (getValue h b ctr) < pow2 max_limb))
    (ensures (v (getValue h a i) * v (getValue h b ctr) < pow2 platform_wide))
    [SMTPat (v (getValue h a i) * v (getValue h b ctr))]
let max_limb_lemma2 h a b i ctr =
    coerce
        (requires (v (getValue h a i) < pow2 max_limb /\ v (getValue h b ctr) < pow2 max_limb))
	(ensures (v (getValue h a i) * v (getValue h b ctr) < pow2 platform_wide))
	(fun _ -> gmax_limb_lemma2 h a b i ctr)

#reset-options

val is_scalar_product_lemma:
  h0:heap -> h1:heap -> a:bigint{live h0 a /\ getLength h0 a >= norm_length} -> s:limb -> res:bigint_wide{live h1 res /\ getLength h1 res >= norm_length} ->
  Lemma
    (requires (Fscalar.IsScalarProduct h0 h1 0 norm_length a s res))
    (ensures (IsScalarProduct h1 res h0 a s))
let is_scalar_product_lemma h0 h1 a s res = ()

val multiplication_step_0:
  a:bigint{ConstantTemplate a} -> b:bigint{getTemplate b = getTemplate a} -> 
  ctr:nat{ctr<norm_length/\ctr<2*norm_length-1} -> c:bigint_wide{Similar a c /\ Similar b c} -> 
  tmp:bigint_wide{Similar a tmp /\ Similar b tmp /\ Similar c tmp} -> 
  ST unit 
     (requires (fun h -> Standardized h a /\ Standardized h b /\ live h c /\ live h tmp
        /\ getLength h tmp >= norm_length /\ getLength h c >= 2*norm_length -1
	/\ maxValueNorm h a < pow2 max_limb
	/\ maxValueNorm h b < pow2 max_limb
	/\ maxValue h c <= ctr * maxValueNorm h a * maxValueNorm h b
       ))
     (ensures (fun h0 _ h1 ->
       Standardized h0 a /\ Standardized h0 b /\ live h0 c /\ live h1 tmp
       /\ live h0 tmp /\ getLength h0 tmp = getLength h1 tmp
       /\ getLength h0 c >= 2*norm_length-1 /\ getLength h1 tmp >= norm_length
       /\ modifies !{getRef tmp} h0 h1
       /\ IsScalarProduct h1 tmp h0 a (getValue h0 b ctr)
       /\ eval h1 tmp norm_length = eval h0 a norm_length * v (getValue h0 b ctr)
     ))
let multiplication_step_0 a b ctr c tmp = 
  //@@
  let h0 = ST.get() in
  let s = index_limb b ctr in 
  assert(forall (n:nat). {:pattern (v (getValue h0 b n))} n < norm_length ==> v (getValue h0 b n) <= pow2 max_limb); 
  assert(forall (n:nat). n = ctr ==> n < norm_length); 
  assert(True /\ bitsize (v s) max_limb); 
  assert(forall (i:nat). {:pattern (v (getValue h0 a i))} 
	   i < norm_length ==> v (getValue h0 a i) < pow2 max_limb);
  assert(v s < pow2 max_limb); 
  cut(forall (i:nat). (i < norm_length) ==> v (getValue h0 a i) * v s < pow2 platform_wide); 
  scalar_multiplication_tr tmp a s 0; 
  let h1 = ST.get() in
  cut(True /\ v s = v (getValue h0 b ctr)); 
  assert(Fscalar.IsScalarProduct h0 h1 0 norm_length a s tmp); 
  is_scalar_product_lemma h0 h1 a s tmp;
  theorem_scalar_multiplication h0 h1 a s norm_length tmp

#reset-options

val std_lemma:
  h0:heap -> h1:heap -> a:bigint -> tmp:bigint_wide{Similar a tmp} ->
  Lemma
    (requires (Standardized h0 a /\ live h1 tmp /\ modifies !{getRef tmp} h0 h1))
    (ensures (Standardized h1 a))
let std_lemma h0 h1 a tmp = 
  //@@
  no_upd_lemma h0 h1 a (!{getRef tmp}); 
  cut(forall (i:nat). {:pattern (v (getValue h1 a i))} i < norm_length ==> v (getValue h1 a i) = v (getValue h0 a i)); 
  cut(True /\ live h1 a); cut(True /\ getLength h1 a >= norm_length); cut (True /\ getTemplate a = templ); 
  cut(forall (i:nat). {:pattern (Standardized h1 a)} i < norm_length ==> bitsize (v (getValue h1 a i)) (getTemplate a i)); 
  cut(Standardized h1 a)
 
assume val max_wide_lemma:
  x:nat{x <= norm_length} -> Lemma (x * pow2 max_wide < pow2 platform_wide)

#reset-options

val lemma_helper_00: unit -> Lemma (forall (a:nat) (b:nat) (c:nat) (d:nat). (a <= b /\ c <= d) ==> a * c <= b * d)
let lemma_helper_00 () = 
  //@@
  ()

val lemma_helper_01: a:int -> b:int -> c:int -> Lemma (a * (b+c) + b + c = (a+1) * (b+c))
let lemma_helper_01 a b c = 
  //@@
  ()

val lemma_helper_02: a:nat -> b:nat -> c:nat -> Lemma (requires (b <= c)) (ensures (a*b <= a*c))
let lemma_helper_02 a b c = 
  //@@
  ()

val multiplication_step_lemma_0010:  h0:heap -> h1:heap ->
  a:bigint{ConstantTemplate a} -> b:bigint{getTemplate b = getTemplate a} -> 
  ctr:nat{ctr<norm_length} -> c:bigint_wide{Similar a c /\ Similar b c} -> 
  tmp:bigint_wide{Similar a tmp /\ Similar b tmp /\ Similar c tmp} -> 
  Lemma
     (requires (
       Standardized h0 a /\ Standardized h0 b /\ live h0 c /\ live h1 tmp
       /\ getLength h1 tmp >= norm_length /\ getLength h0 c >= 2*norm_length -1
       /\ maxValueNorm h0 a < pow2 max_limb /\ maxValueNorm h0 b < pow2 max_limb
       /\ maxValue h0 c <= ctr * maxValueNorm h0 a * maxValueNorm h0 b
       /\ modifies !{getRef tmp} h0 h1
       /\ IsScalarProduct h1 tmp h0 a (getValue h0 b ctr) ))
     (ensures (live h1 tmp /\ Standardized h0 a /\ Standardized h0 b
       /\ getLength h1 tmp >= norm_length
       /\ (forall (i:nat). {:pattern (v (getValue h1 tmp i))} i < norm_length ==> v (getValue h1 tmp i) <= maxValueNorm h0 a * maxValueNorm h0 b) ))
let multiplication_step_lemma_0010 h0 h1 a b ctr c tmp = 
  //@@
  lemma_helper_00 ()

val multiplication_step_lemma_001: 
  h0:heap -> h1:heap ->
  a:bigint{ConstantTemplate a} -> b:bigint{getTemplate b = getTemplate a} -> 
  ctr:nat{ctr<norm_length} -> c:bigint_wide{Similar a c /\ Similar b c} -> 
  tmp:bigint_wide{Similar a tmp /\ Similar b tmp /\ Similar c tmp} -> 
  Lemma
     (requires (
       (Standardized h0 a) /\ (Standardized h0 b) /\ (live h0 c) /\ (live h1 tmp)
        /\ (getLength h1 tmp >= norm_length) /\ (getLength h0 c >= 2*norm_length -1)
	/\ (maxValueNorm h0 a < pow2 max_limb) /\ (maxValueNorm h0 b < pow2 max_limb)
	/\ (maxValue h0 c <= ctr * maxValueNorm h0 a * maxValueNorm h0 b)
	/\ modifies !{getRef tmp} h0 h1
       /\ IsScalarProduct h1 tmp h0 a (getValue h0 b ctr)
       ))
     (ensures (
       (live h1 c) /\ (live h1 tmp) /\ (ctr+norm_length <= getLength h1 c) 
       /\ (0+norm_length <= getLength h1 tmp)
       /\ FsumWide.WillNotOverflow h1 ctr 0 norm_length 0 c tmp
     ))
let multiplication_step_lemma_001 h0 h1 a b ctr c tmp =
  //@@
  multiplication_step_lemma_0010 h0 h1 a b ctr c tmp;
  Axiomatic.distributivity_add_left ctr 1 (maxValueNorm h0 a * maxValueNorm h0 b);
  cut(forall (i:nat). {:pattern (v (getValue h1 c i))} i < norm_length ==> v (getValue h1 c (i+ctr)) <= ctr * maxValueNorm h0 a * maxValueNorm h0 b);
  cut (True /\ ctr * maxValueNorm h0 a * maxValueNorm h0 b + maxValueNorm h0 a * maxValueNorm h0 b
    = (ctr+1) * (maxValueNorm h0 a * maxValueNorm h0 b) );
  cut (forall (i:nat). {:pattern (v (getValue h1 c (i+ctr)) + v (getValue h1 tmp i))} i < norm_length ==> v (getValue h1 c (i+ctr)) + v (getValue h1 tmp i) <= (ctr+1) * (maxValueNorm h0 a * maxValueNorm h0 b));
  auxiliary_lemma_3 h0 h0 h1 a b ctr c;
  assert ((maxValueNorm h0 a * maxValueNorm h0 b) <= pow2 max_wide);
  lemma_helper_02 (ctr+1) (maxValueNorm h0 a * maxValueNorm h0 b) (pow2 max_wide);
  cut(True /\ (ctr+1) * (maxValueNorm h0 a * maxValueNorm h0 b) <= (ctr + 1) * pow2 max_wide);
  max_wide_lemma (ctr+1); 
  assert((ctr+1) * pow2 max_wide < pow2 platform_wide);
  FproductLemmas.helper_lemma_4 (maxValueNorm h0 a) (maxValueNorm h0 b);
  FproductLemmas.helper_lemma_4 (ctr+1) (maxValueNorm h0 a * maxValueNorm h0 b);
  FproductLemmas.helper_lemma_4 (ctr+1) (pow2 max_wide);
  FproductLemmas.ineq_lemma_2 ((ctr+1) * (maxValueNorm h0 a * maxValueNorm h0 b)) ((ctr+1) * pow2 max_wide) (pow2 platform_wide);
  assert ((ctr+1) * (maxValueNorm h0 a * maxValueNorm h0 b) < pow2 platform_wide);
  assert(forall (i:nat). i < norm_length ==> v (getValue h1 c (i+ctr)) + v (getValue h1 tmp i) <= (ctr+1) * (maxValueNorm h0 a * maxValueNorm h0 b) ==> v (getValue h1 c (i+ctr)) + v (getValue h1 tmp i) < pow2 platform_wide); 
  cut(forall (i:nat). i < norm_length ==> v (getValue h1 c (i+ctr)) + v (getValue h1 tmp i) < pow2 platform_wide); 
  assert(FsumWide.WillNotOverflow h1 ctr 0 norm_length 0 c tmp)

val multiplication_step_lemma_01: 
  h0:heap -> h1:heap ->
  a:bigint{ConstantTemplate a} -> b:bigint{getTemplate b = getTemplate a} -> 
  ctr:nat{ctr<norm_length} -> c:bigint_wide{Similar a c /\ Similar b c} -> 
  tmp:bigint_wide{Similar a tmp /\ Similar b tmp /\ Similar c tmp} -> 
  Lemma
     (requires (
       (Standardized h0 a) /\ (Standardized h0 b) /\ (live h0 c) /\ (live h1 tmp)
        /\ (getLength h1 tmp >= norm_length) /\ (getLength h0 c >= 2*norm_length -1)
	/\ (maxValueNorm h0 a < pow2 max_limb) /\ (maxValueNorm h0 b < pow2 max_limb)
	/\ (maxValue h0 c <= ctr * maxValueNorm h0 a * maxValueNorm h0 b)
	/\ modifies !{getRef tmp} h0 h1
       /\ IsScalarProduct h1 tmp h0 a (getValue h0 b ctr)
       ))
     (ensures (
       (live h1 c) /\ (live h1 tmp) /\ (ctr+norm_length <= getLength h1 c) 
       /\ (Standardized h1 a) /\ (Standardized h1 b)
       /\ (0+norm_length <= getLength h1 tmp)
       /\ FsumWide.WillNotOverflow h1 ctr 0 norm_length 0 c tmp
     ))
let multiplication_step_lemma_01 h0 h1 a b ctr c tmp =
  //@@
  no_upd_lemma h0 h1 c (!{getRef tmp}); 
  cut(True /\ getLength h1 c >= ctr + norm_length); 
  std_lemma h0 h1 a tmp;
  std_lemma h0 h1 b tmp; 
  multiplication_step_lemma_001 h0 h1 a b ctr c tmp

val partial_equality_lemma: h0:heap -> h1:heap -> c:bigint_wide{live h0 c /\ live h1 c /\ getLength h0 c = getLength h1 c} -> ctr:nat{ ctr + norm_length <= getLength h0 c} ->
  Lemma
    (requires (FsumWide.IsNotModified h0 h1 ctr norm_length 0 c))
    (ensures (PartialEquality h1 c h0 c ctr))
let partial_equality_lemma h0 h1 c ctr = 
  //@@
  ()

val lemma_helper_10: a:nat -> b:nat -> c:nat -> Lemma (a <= a + (b * c))
let lemma_helper_10 a b c = 
  //@@
  ()

#reset-options

val max_value_lemma_1: 
  h0:heap -> h1:heap -> h2:heap -> 
  a:bigint{ConstantTemplate a} ->
  b:bigint{getTemplate b = getTemplate a} -> ctr:nat{ctr < norm_length} -> 
  c:bigint_wide{Similar a c /\ Similar b c /\ getTemplate c = getTemplate a} -> 
  tmp:bigint_wide{Similar a tmp /\ Similar b tmp /\ Similar c tmp /\ getTemplate tmp = getTemplate a} ->
  Lemma
    (requires (
      Standardized h0 a /\ Standardized h0 b /\ live h0 c /\ live h1 tmp /\ live h2 c
      /\ modifies !{getRef tmp} h0 h1
      /\ getLength h1 tmp >= norm_length /\ getLength h0 c >= 2 * norm_length - 1
      /\ getLength h2 c = getLength h0 c /\ live h1 c /\ getLength h1 c = getLength h0 c
      /\ (maxValue h0 c <= ctr * maxValueNorm h0 a * maxValueNorm h0 b)
      /\ (forall (i:nat). {:pattern (v (getValue h2 c (i+ctr)))} 
	  i < norm_length ==> v (getValue h2 c (i+ctr)) = v (getValue h0 c (i+ctr)) + (v (getValue h0 a i) * v (getValue h0 b ctr))) 
      /\ (forall (i:nat). {:pattern (v (getValue h2 c i))} ((i < ctr \/ i >= norm_length + ctr) /\ i < getLength h2 c) ==> v (getValue h2 c i) = v (getValue h0 c i))
    ))
    (ensures (
       Standardized h0 a /\ Standardized h0 b /\ live h2 c
       /\ (maxValue h2 c <= (ctr+1) * maxValueNorm h0 a * maxValueNorm h0 b)))
let max_value_lemma_1 h0 h1 h2 a b ctr c tmp =
  //@@
  cut(forall (i:nat). {:pattern (v (getValue h0 a i))} 
    i < norm_length ==> v (getValue h0 a i) <= maxValueNorm h0 a);
  cut(forall (i:nat). {:pattern (v (getValue h0 b i))} 
	   i < norm_length ==> v (getValue h0 b i) <= maxValueNorm h0 b);
  cut(forall (i:nat). {:pattern (v (getValue h0 c i))} i < getLength h0 c ==> v (getValue h0 c i) <= maxValue h0 c);
  cut(forall (i:nat). {:pattern (v (getValue h0 c (i+ctr)))} 
	   i < norm_length ==> v (getValue h0 c (i+ctr)) <= maxValue h0 c);
  FproductLemmas.ineq_lemma ();
  assert(forall (a:nat) (b':nat) (c:nat) (d:nat). {:pattern (v (getValue h0 b ctr))} a <= c /\ b' <= d ==> a * b' <= c * d);
  assert(v (getValue h0 b ctr) <= maxValueNorm h0 b);
  cut(forall (i:nat). {:pattern (v (getValue h0 a i) * v (getValue h0 b ctr))} i < norm_length ==>
    (v (getValue h0 a i)) <= maxValueNorm h0 a /\ v (getValue h0 b ctr) <= maxValueNorm h0 b); 
  cut(forall (i:nat). {:pattern (v (getValue h0 a i) * v (getValue h0 b ctr))} i < norm_length ==>
    (v (getValue h0 a i) * v (getValue h0 b ctr)) <= maxValueNorm h0 a * maxValueNorm h0 b);
  assert(forall (a':nat) (b':nat) (c':nat) (d:nat). {:pattern (maxValue h0 c + (maxValueNorm h0 a * maxValueNorm h0 b))} a' <= c' /\ b' <= d ==> a' + b' <= c' + d); 
  cut(forall (i:nat). {:pattern (v (getValue h0 c (i+ctr)) + (v (getValue h0 a i) * v (getValue h0 b ctr)))} i < norm_length ==> v (getValue h0 c (i+ctr)) + (v (getValue h0 a i) * v (getValue h0 b ctr)) <= maxValue h0 c + (maxValueNorm h0 a * maxValueNorm h0 b)); 
  assert(forall (i:nat). i < norm_length ==> v (getValue h2 c (i+ctr)) <= maxValue h0 c + (maxValueNorm h0 a * maxValueNorm h0 b)); 
  assert(forall (i:nat). {:pattern (i < getLength h0 c)} i < getLength h0 c ==>
	   ((i >= ctr /\ i < norm_length+ctr) \/ ((i < ctr \/ i >= norm_length + ctr) /\ i < getLength h0 c))); 
  cut(forall (i:nat). (i>=ctr /\ i<norm_length+ctr) ==> (i-ctr>=0 /\ i-ctr < norm_length /\ ((i-ctr)+ctr) = i)); 
  cut(forall (i:nat). {:pattern (i >= ctr /\ i < norm_length+ctr)} (i >= ctr /\ i < norm_length+ctr) ==> v (getValue h2 c i) <= maxValue h0 c + (maxValueNorm h0 a * maxValueNorm h0 b));
  assert(forall (i:nat). {:pattern ((i < ctr \/ i >= norm_length + ctr) /\ i < getLength h2 c)} 
    ((i < ctr \/ i >= norm_length + ctr) /\ i < getLength h2 c) ==> v (getValue h2 c i) <= maxValue h0 c); 
    lemma_helper_10 (maxValue h0 c) (maxValueNorm h0 a) (maxValueNorm h0 b); 
  cut(True /\ maxValue h0 c <= maxValue h0 c + (maxValueNorm h0 a * maxValueNorm h0 b)); 
  assert(forall (i:nat).  ((i < ctr \/ i >= norm_length + ctr) /\ i < getLength h2 c) ==> v (getValue h2 c i) <= maxValue h0 c); 
  assert(forall (i:nat). {:pattern (v (getValue h2 c i))} ((i < ctr \/ i >= norm_length + ctr) /\ i < getLength h0 c) ==> v (getValue h2 c i) <= maxValue h0 c + (maxValueNorm h0 a * maxValueNorm h0 b)); 
  cut(forall (i:nat). {:pattern(maxValue h0 c + (maxValueNorm h0 a * maxValueNorm h0 b))}
    i < getLength h0 c ==> 
      ((i >= ctr /\ i < norm_length+ctr) \/ ((i < ctr \/ i >= norm_length + ctr) /\ i < getLength h0 c)) ==>
	v (getValue h2 c i) <= maxValue h0 c + (maxValueNorm h0 a * maxValueNorm h0 b)); 
  Axiomatic.paren_mul_right ctr (maxValueNorm h0 a) (maxValueNorm h0 b); 
  cut(True /\ maxValue h0 c <= ctr * (maxValueNorm h0 a * maxValueNorm h0 b)); 
  FproductLemmas.factorise_lemma (maxValueNorm h0 a * maxValueNorm h0 b) ctr;
  assert(True /\ maxValue h0 c + (maxValueNorm h0 a * maxValueNorm h0 b) <= (ctr+1) * (maxValueNorm h0 a * maxValueNorm h0 b)); 
  assert(forall (i:nat). 
    i < getLength h0 c ==> 
	v (getValue h2 c i) <= (ctr+1) * (maxValueNorm h0 a * maxValueNorm h0 b)); 
  assert(maxValue h2 c <= (ctr+1) * (maxValueNorm h0 a * maxValueNorm h0 b))

val max_value_lemma: 
  h0:heap -> h1:heap -> h2:heap -> 
  a:bigint{ConstantTemplate a} ->
  b:bigint{getTemplate b = getTemplate a} -> ctr:nat{ctr < norm_length} -> 
  c:bigint_wide{Similar a c /\ Similar b c /\ getTemplate c = getTemplate a} -> 
  tmp:bigint_wide{Similar a tmp /\ Similar b tmp /\ Similar c tmp /\ getTemplate tmp = getTemplate a} ->
  Lemma
    (requires (
      Standardized h0 a /\ Standardized h0 b /\ live h0 c /\ live h1 tmp /\ live h2 c
      /\ modifies !{getRef tmp} h0 h1
      /\ getLength h1 tmp >= norm_length /\ getLength h0 c >= 2 * norm_length - 1
      /\ getLength h2 c = getLength h0 c /\ live h1 c /\ getLength h1 c = getLength h0 c
      /\ (maxValue h0 c <= ctr * maxValueNorm h0 a * maxValueNorm h0 b)
      /\ IsScalarProduct h1 tmp h0 a (getValue h0 b ctr)
      /\ FsumWide.IsSum h1 h2 ctr 0 norm_length 0 c tmp
      /\ FsumWide.IsNotModified h1 h2 ctr norm_length 0 c))
    (ensures (
       Standardized h0 a /\ Standardized h0 b /\ live h2 c
       /\ (maxValue h2 c <= (ctr+1) * maxValueNorm h0 a * maxValueNorm h0 b)))
let max_value_lemma h0 h1 h2 a b ctr c tmp =
  //@@
  cut(forall (i:nat). {:pattern (v (getValue h1 tmp i))} i < norm_length ==> v (getValue h1 tmp i) = v (getValue h0 a i) * v (getValue h0 b ctr)); 
  cut(forall (i:nat). {:pattern (v (getValue h2 c (i+ctr)))} i < norm_length ==> v (getValue h2 c (i+ctr)) = v (getValue h1 c (i+ctr)) + v (getValue h1 tmp i)); 
  cut(forall (i:nat). {:pattern (v (getValue h2 c i))} 
    ((i < ctr \/ i >= norm_length + ctr) /\ i < getLength h2 c) ==> v (getValue h2 c i) = v (getValue h1 c i)); 
  no_upd_lemma h0 h1 c (!{getRef tmp});
  cut(forall (i:nat). {:pattern (v (getValue h1 c i))} i < getLength h0 c ==> v (getValue h1 c i) = v (getValue h0 c i)); 
  cut(forall (i:nat). {:pattern (v (getValue h1 tmp i))}
    i < norm_length ==> v (getValue h1 tmp i) = v (getValue h0 a i) * v (getValue h0 b ctr)); 
  cut(forall (i:nat). i < norm_length ==> v (getValue h2 c (i+ctr)) = v (getValue h0 c (i+ctr)) + (v (getValue h0 a i) * v (getValue h0 b ctr))); 
  max_value_lemma_1 h0 h1 h2 a b ctr c tmp
  
val standardized_lemma: 
  h0:heap -> h1:heap -> h2:heap ->
  a:bigint{ConstantTemplate a} ->
  c:bigint_wide{Similar a c /\ getTemplate c = getTemplate a} -> 
  tmp:bigint_wide{Similar a tmp /\ Similar c tmp /\ getTemplate tmp = getTemplate a} ->
  Lemma
    (requires (
	(Standardized h0 a) /\ (live h0 c) /\ (live h1 tmp) /\ (live h1 c)
	/\ modifies !{getRef tmp} h0 h1
	/\ (modifies !{getRef c} h1 h2)
    ))
     (ensures (
       (Standardized h0 a) /\ (Standardized h2 a)
       /\ (live h0 c)  /\ (live h1 tmp) /\ (live h2 tmp) 
       /\ (modifies !{getRef c,getRef tmp} h0 h2)
     ))
let standardized_lemma h0 h1 h2 a c tmp =
  //@@
  cut(modifies !{getRef c,getRef tmp} h0 h2); 
  no_upd_lemma h0 h2 a (!{getRef c, getRef tmp}); 
  no_upd_lemma h1 h2 tmp (!{getRef c});
  cut(forall (i:nat). {:pattern (v (getValue h2 a i))} i < norm_length ==> v (getValue h2 a i) = v (getValue h0 a i));
  cut(True /\ live h2 a); cut(True /\ getLength h2 a >= norm_length); cut (True /\ getTemplate a = templ); 
  cut(forall (i:nat). {:pattern (Standardized h2 a)} i < norm_length ==> bitsize (v (getValue h2 a i)) (getTemplate a i)); 
  cut(Standardized h2 a)

val length_lemma:
  h0:heap -> h1:heap -> h2:heap ->
  c:bigint_wide -> ctr:nat{ctr < norm_length} -> 
  tmp:bigint_wide{Similar c tmp} ->
  Lemma 
     (requires (
	(live h0 c) /\ (live h1 tmp) /\ (live h1 c)
	/\ live h0 tmp /\ (getLength h0 tmp >= norm_length) /\ (getLength h1 tmp = getLength h0 tmp)
	/\ (getLength h0 c >= 2 * norm_length - 1)
	/\ modifies !{getRef tmp} h0 h1
	/\ (live h2 c) /\ (live h2 tmp)
	/\ (ctr+norm_length <= getLength h1 c /\ 0+norm_length <= getLength h1 tmp)
	/\ (modifies !{getRef c} h1 h2)
	/\ (getLength h1 c = getLength h2 c)
    ))
     (ensures (
       (live h0 c) /\ (live h2 c)  /\ (live h0 tmp) /\ (live h2 tmp) 
       /\ (getLength h0 tmp >= norm_length) /\ (getLength h2 tmp = getLength h0 tmp)
       /\ (getLength h0 c >= 2 * norm_length - 1) /\ (getLength h2 c = getLength h0 c)
       /\ (modifies !{getRef c,getRef tmp} h0 h2)
     ))
let length_lemma h0 h1 h2 c ctr tmp =
  //@@
  no_upd_lemma h0 h1 c (!{getRef tmp});
  no_upd_lemma h1 h2 tmp (!{getRef c})

val lemma_helper_20:   h0:heap -> h1:heap -> h2:heap -> a:bigint -> b:bigint -> ctr:nat{ctr < norm_length} -> 
  c:bigint_wide{Similar a c /\ Similar b c} -> tmp:bigint_wide{Similar a tmp /\ Similar b tmp /\ Similar c tmp} -> Lemma 
  (requires(live h2 tmp /\ live h1 tmp 
    /\ live h1 c /\ live h2 c 
    /\ getLength h2 c >= 2 * norm_length - 1 /\ getLength h1 c = getLength h2 c
    /\ getLength h2 tmp >= norm_length 
    /\ getLength h1 tmp = getLength h2 tmp 
    /\ FsumWide.IsSum h1 h2 ctr 0 norm_length 0 c tmp 
    ))
  (ensures (
    live h2 tmp /\ live h1 tmp 
    /\ live h2 c /\ live h1 c 
    /\ getLength h2 c >= 2 * norm_length - 1 /\ getLength h1 c = getLength h2 c
    /\ getLength h2 tmp >= norm_length /\ getLength h1 tmp = getLength h2 tmp
    /\ FsumWide.IsSum h1 h2 ctr 0 norm_length 0 c tmp
    /\ StoresSum h2 c h1 c h1 tmp ctr norm_length
    ))
let lemma_helper_20 h0 h1 h2 a b ctr c tmp = ()

val multiplication_step_lemma_02:
  h0:heap -> h1:heap -> h2:heap ->
  a:bigint{ConstantTemplate a} ->
  b:bigint{getTemplate b = getTemplate a} -> ctr:nat{ctr < norm_length} -> 
  c:bigint_wide{Similar a c /\ Similar b c /\ getTemplate c = getTemplate a} -> 
  tmp:bigint_wide{Similar a tmp /\ Similar b tmp /\ Similar c tmp /\ getTemplate tmp = getTemplate a} ->
  Lemma 
     (requires (
	(Standardized h0 a) /\ (Standardized h0 b) /\ (live h0 c) /\ (live h1 tmp) /\ (live h1 c)
	/\ live h0 tmp /\ (getLength h0 tmp >= norm_length) /\ (getLength h1 tmp = getLength h0 tmp)
	/\ (getLength h0 c >= 2 * norm_length - 1)
	/\ (maxValueNorm h0 a < pow2 max_limb)
	/\ (maxValueNorm h0 b < pow2 max_limb)
	/\ (maxValue h0 c <= ctr * maxValueNorm h0 a * maxValueNorm h0 b) 
	// After fscalar
	/\ modifies !{getRef tmp} h0 h1
	/\ IsScalarProduct h1 tmp h0 a (getValue h0 b ctr)
        /\ eval h1 tmp norm_length = eval h0 a norm_length * v (getValue h0 b ctr)
 	// After fsum
	/\ (live h2 c) /\ (live h2 tmp)
	/\ (ctr+norm_length <= getLength h1 c /\ 0+norm_length <= getLength h1 tmp)
	/\ (modifies !{getRef c} h1 h2)
	/\ (getLength h1 c = getLength h2 c)
	/\ FsumWide.IsSum h1 h2 ctr 0 norm_length 0 c tmp
	/\ FsumWide.IsNotModified h1 h2 ctr norm_length 0 c
    ))
     (ensures (
       (Standardized h0 a) /\ (Standardized h2 a) /\ (Standardized h0 b) /\ (Standardized h2 b) 
       /\ (live h0 c) /\ (live h2 c)  /\ (live h0 tmp) /\ (live h2 tmp) 
       /\ (getLength h0 tmp >= norm_length) /\ (getLength h2 tmp = getLength h0 tmp)
       /\ (getLength h0 c >= 2 * norm_length - 1) /\ (getLength h2 c = getLength h0 c)
       /\ (ctr < norm_length) /\ (modifies !{getRef c,getRef tmp} h0 h2)
       /\ (maxValueNorm h0 a < pow2 max_limb)
       /\ (maxValueNorm h0 b < pow2 max_limb)
       /\ (maxValue h0 c <= ctr * maxValueNorm h0 a * maxValueNorm h0 b)
       /\ (maxValue h2 c <= (ctr+1) * maxValueNorm h0 a * maxValueNorm h0 b)
       /\ (eval h2 c (2*norm_length-1) = eval h0 c (2*norm_length-1) + pow2 (bitweight (getTemplate a) ctr) * eval h0 a norm_length * v (getValue h0 b ctr))
     ))
let multiplication_step_lemma_02 h0 h1 h2 a b ctr c tmp =
  //@@ timeout 50
  assert(forall (i:nat). (i >= norm_length + ctr /\ i < 2 * norm_length - 1) ==>
  	   v (getValue h2 c i) = v (getValue h1 c i));
  eval_partial_eq_lemma h1 h2 c c (norm_length+ctr) (2*norm_length-1); 
  no_upd_lemma h0 h1 c (!{getRef tmp});
  (* cut(forall (i:nat). i < getLength h0 c ==> v (getValue h0 c i) = v (getValue h1 c i));  *)
  eval_eq_lemma h0 h1 c c (2*norm_length-1);
  eval_eq_lemma h0 h1 c c (norm_length+ctr);
  cut(True /\ eval h2 c (2*norm_length-1) - eval h2 c (norm_length+ctr) = eval h0 c (2*norm_length-1) - eval h0 c (norm_length+ctr)); 
  (* cut (True /\ eval h1 tmp norm_length = eval h0 a norm_length * v (getValue h0 b ctr));  *)
  lemma_helper_20 h0 h1 h2 a b ctr c tmp;
  (* cut (StoresSum h2 c h1 c h1 tmp ctr norm_length); *)
  partial_equality_lemma h1 h2 c ctr; 
  constant_template_lemma a c; constant_template_lemma a tmp; 
  cut (PartialEquality h2 c h1 c ctr); 
  multiplication_step_lemma h1 h2 c tmp c ctr norm_length; 
  cut (True /\ eval h2 c (norm_length+ctr) = eval h1 c (norm_length+ctr) + pow2 (bitweight (getTemplate a) ctr) * eval h0 a norm_length * v (getValue h0 b ctr));
  cut (True /\ eval h2 c (norm_length+ctr) = eval h0 c (norm_length+ctr) + pow2 (bitweight (getTemplate a) ctr) * eval h0 a norm_length * v (getValue h0 b ctr));
  cut (True /\ eval h2 c (2*norm_length-1) = eval h0 c (2*norm_length-1) + pow2 (bitweight (getTemplate a) ctr) * eval h0 a norm_length * v (getValue h0 b ctr));
  max_value_lemma h0 h1 h2 a b ctr c tmp; 
  Axiomatic.paren_mul_right (ctr+1) (maxValueNorm h0 a) (maxValueNorm h0 b);
  assert(maxValue h2 c <= (ctr+1) * maxValueNorm h0 a * maxValueNorm h0 b); 
  standardized_lemma h0 h1 h2 a c tmp; 
  constant_template_lemma a b; 
  standardized_lemma h0 h1 h2 b c tmp;
  length_lemma h0 h1 h2 c ctr tmp;
  ()
  
#reset-options

val multiplication_step_p1:
  a:bigint{ConstantTemplate a} -> b:bigint{getTemplate b = getTemplate a} -> 
  ctr:nat{ctr<norm_length} -> c:bigint_wide{Similar a c /\ Similar b c} -> 
  tmp:bigint_wide{Similar a tmp /\ Similar b tmp /\ Similar c tmp} -> 
  ST unit 
     (requires (fun h -> (Standardized h a) /\ (Standardized h b) /\ (live h c) /\ (live h tmp)
        /\ (getLength h tmp >= norm_length) /\ (getLength h c >= 2*norm_length -1)
	/\ (maxValueNorm h a < pow2 max_limb)
	/\ (maxValueNorm h b < pow2 max_limb)
	/\ (maxValue h c <= ctr * maxValueNorm h a * maxValueNorm h b)
	/\ (eval h c (2*norm_length-1) = eval h a (norm_length) * eval h b ctr)
       ))
     (ensures (fun h0 u h1 ->
       (Standardized h0 a) /\ (Standardized h0 b) /\ (live h0 c) /\ (live h0 tmp)       
       /\ (Standardized h1 a) /\ (Standardized h1 b) /\ (live h1 c) /\ (live h1 tmp)
       /\ (getLength h0 tmp >= norm_length) /\ (getLength h0 c >= 2*norm_length -1)
       /\ getLength h0 tmp = getLength h1 tmp
       /\ (getLength h1 c = getLength h0 c) /\ (ctr < norm_length)
       /\ (modifies !{getRef c,getRef tmp} h0 h1)
       /\ (maxValue h0 c <= ctr * maxValueNorm h0 a * maxValueNorm h0 b)
       /\ (maxValue h1 c <= (ctr+1) * (maxValueNorm h0 a * maxValueNorm h0 b))
       /\ (eval h0 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b ctr)
       /\ (eval h1 c (2*norm_length-1) = eval h0 c (2*norm_length-1) + pow2 (bitweight (getTemplate a) ctr) * eval h0 a norm_length * v (getValue h0 b ctr))
     ))
let multiplication_step_p1 a b ctr c tmp =
  //@@
  let h0 = ST.get() in
  multiplication_step_0 a b ctr c tmp; 
  let h1 = ST.get() in
  multiplication_step_lemma_01 h0 h1 a b ctr c tmp; 
  FsumWide.fsum_index c ctr tmp 0 norm_length 0; 
  let h2 = ST.get() in 
  multiplication_step_lemma_02 h0 h1 h2 a b ctr c tmp

opaque val ghelper_lemma_6:
  h0:heap -> h1:heap ->
  a:bigint{ConstantTemplate a} -> 
  b:bigint{getTemplate b = getTemplate a} -> ctr:nat{ctr < norm_length} -> 
  c:bigint_wide{Similar a c /\ Similar b c} -> 
  tmp:bigint_wide{Similar a tmp /\ Similar b tmp /\ Similar c tmp} ->
  GLemma unit
     (requires (
	(Standardized h0 a) /\ (Standardized h0 b) /\ (live h0 c)
	/\ (getLength h0 c >= 2 * norm_length - 1)
       ))
    (ensures (
	(Standardized h0 a) /\ (Standardized h0 b) /\ (live h0 c)
	/\ (getLength h0 c >= 2 * norm_length - 1)
       /\ eval h0 c (2*norm_length-1) + pow2 (bitweight (getTemplate a) ctr) * eval h0 a (norm_length) * v (getValue h0 b ctr)  = eval h0 a (norm_length) * v (getValue h0 b ctr) * pow2 (bitweight (getTemplate a) ctr) + eval h0 c (2*norm_length-1)
    ))
    []
let ghelper_lemma_6 h0 h1 a b ctr c tmp =
  FproductLemmas.helper_lemma_5 (eval h0 c (2*norm_length-1)) (pow2 (bitweight (getTemplate a) ctr)) (eval h0 a norm_length) (v (getValue h0 b ctr))

val helper_lemma_6:
  h0:heap -> h1:heap ->
  a:bigint{ConstantTemplate a} -> 
  b:bigint{getTemplate b = getTemplate a} -> ctr:nat{ctr < norm_length} -> 
  c:bigint_wide{Similar a c /\ Similar b c} -> 
  tmp:bigint_wide{Similar a tmp /\ Similar b tmp /\ Similar c tmp} ->
  Lemma
     (requires (
	(Standardized h0 a) /\ (Standardized h0 b) /\ (live h0 c)
	/\ (getLength h0 c >= 2 * norm_length - 1)
       ))
    (ensures (
	(Standardized h0 a) /\ (Standardized h0 b) /\ (live h0 c)
	/\ (getLength h0 c >= 2 * norm_length - 1)
       /\ eval h0 c (2*norm_length-1) + pow2 (bitweight (getTemplate a) ctr) * eval h0 a (norm_length) * v (getValue h0 b ctr)  = eval h0 a (norm_length) * v (getValue h0 b ctr) * pow2 (bitweight (getTemplate a) ctr) + eval h0 c (2*norm_length-1)
    ))
let helper_lemma_6 h0 h1 a b ctr c tmp =
  coerce 
     (requires (
	(Standardized h0 a) /\ (Standardized h0 b) /\ (live h0 c)
	/\ (getLength h0 c >= 2 * norm_length - 1)
       ))
    (ensures (
	(Standardized h0 a) /\ (Standardized h0 b) /\ (live h0 c)
	/\ (getLength h0 c >= 2 * norm_length - 1)
       /\ eval h0 c (2*norm_length-1) + pow2 (bitweight (getTemplate a) ctr) * eval h0 a (norm_length) * v (getValue h0 b ctr)  = eval h0 a (norm_length) * v (getValue h0 b ctr) * pow2 (bitweight (getTemplate a) ctr) + eval h0 c (2*norm_length-1)
    ))
    (fun _ -> ghelper_lemma_6 h0 h1 a b ctr c tmp)

(* Code : does 1 step of the multiplication (1 scalar multiplication), 
   and infers the appropriate properties on sizes, values and evaluated
   values for the resulting bigint *)
val multiplication_step:
  a:bigint{ConstantTemplate a} -> 
  b:bigint{getTemplate b = getTemplate a} -> ctr:nat{ctr < norm_length} -> 
  c:bigint_wide{Similar a c /\ Similar b c} -> 
  tmp:bigint_wide{Similar a tmp /\ Similar b tmp /\ Similar c tmp} ->
  ST unit  
     (requires (fun h ->
	(Standardized h a) /\ (Standardized h b) /\ (live h c) /\ (live h tmp)
	/\ (getLength h tmp >= norm_length) /\ (getLength h c >= 2 * norm_length - 1)
	/\ (maxValueNorm h a < pow2 max_limb)
	/\ (maxValueNorm h b < pow2 max_limb)
	/\ (maxValue h c <= ctr * maxValueNorm h a * maxValueNorm h b) 
	/\ (eval h c (2*norm_length-1) = eval h a (norm_length) * eval h b ctr)
       ))
     (ensures (fun h0 u h1 ->
       (Standardized h0 a) /\ (Standardized h1 a) /\ (Standardized h0 b) /\ (Standardized h1 b) 
       /\ (live h0 c) /\ (live h1 c)  /\ (live h0 tmp) /\ (live h1 tmp) 
       /\ (getLength h1 tmp >= norm_length) /\ (getLength h1 tmp = getLength h0 tmp)
       /\ (getLength h0 c >= 2 * norm_length - 1) /\ (getLength h1 c = getLength h0 c)
       /\ (ctr < norm_length) /\ (modifies !{getRef c,getRef tmp} h0 h1)
       /\ (maxValueNorm h0 a < pow2 max_limb)
       /\ (maxValueNorm h0 b < pow2 max_limb)
       /\ (maxValue h0 c <= ctr * maxValueNorm h0 a * maxValueNorm h0 b)
       /\ (maxValue h1 c <= (ctr+1) * maxValueNorm h0 a * maxValueNorm h0 b)
       /\ (eval h0 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b ctr)
       /\ (eval h1 c (2*norm_length-1) = eval h0 a (norm_length) * v (getValue h0 b ctr) * pow2 (bitweight (getTemplate a) ctr) + eval h0 c (2*norm_length-1))
     ))
let multiplication_step a b ctr c tmp =
  let h0 = ST.get() in
  multiplication_step_p1 a b ctr c tmp;  
  let h1 = ST.get() in
  helper_lemma_6 h0 h1 a b ctr c tmp
  
(* Lemma : factorizes "eval" equation *)
opaque val gmultiplication_step_lemma_03:
  h0:heap -> h1:heap -> 
  a:bigint{ConstantTemplate a /\ Standardized h0 a } -> 
  b:bigint{getTemplate b = getTemplate a /\ Standardized h0 b } ->
  ctr:pos{ ctr <= norm_length } ->
  c:bigint_wide{(live h1 c) /\ (getLength h1 c >= 2*norm_length - 1) /\ (getTemplate c = getTemplate a) } ->
  GLemma unit
    (requires (eval h1 c (2*norm_length-1) = (eval h0 a (norm_length) * v (getValue h0 b (norm_length - ctr))) * pow2 (bitweight (getTemplate a) (norm_length - ctr)) + eval h0 a (norm_length) * eval h0 b (norm_length - ctr) ))
    (ensures ( eval h1 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length - ctr + 1)))
    []
let gmultiplication_step_lemma_03 h0 h1 a b ctr c =
  //@@
  let t = getTemplate a in 
  Axiomatic.paren_mul_left (eval h0 a norm_length) (v (getValue h0 b (norm_length - ctr))) (pow2 (bitweight t (norm_length - ctr))); 
  cut (True /\ eval h1 c (2*norm_length-1) = eval h0 a norm_length * v (getValue h0 b (norm_length - ctr)) * pow2 (bitweight t (norm_length - ctr)) + eval h0 a norm_length * eval h0 b (norm_length - ctr) ); 
  Axiomatic.swap_mul (v (getValue h0 b (norm_length - ctr))) (pow2 (bitweight t (norm_length - ctr))); 
  cut (True /\ eval h1 c (2*norm_length-1) = eval h0 a norm_length * pow2 (bitweight t (norm_length - ctr)) * v (getValue h0 b (norm_length - ctr)) + eval h0 a norm_length * eval h0 b (norm_length - ctr) ) ; 
  Axiomatic.distributivity_add_right (eval h0 a norm_length) (pow2 (bitweight t (norm_length - ctr)) * v (getValue h0 b (norm_length - ctr))) (eval h0 b (norm_length - ctr)); 
  cut (True /\ eval h1 c (2*norm_length-1) = eval h0 a norm_length * (pow2 (bitweight t (norm_length - ctr)) * v (getValue h0 b (norm_length - ctr)) + eval h0 b (norm_length - ctr))); 
  eval_definition h0 b (norm_length-ctr+1)

#reset-options

val multiplication_step_lemma_03:
  h0:heap -> h1:heap -> 
  a:bigint{ConstantTemplate a /\ Standardized h0 a } -> 
  b:bigint{getTemplate b = getTemplate a /\ Standardized h0 b } ->
  ctr:pos{ ctr <= norm_length } ->
  c:bigint_wide{(live h1 c) /\ (getLength h1 c >= 2*norm_length - 1) /\ (getTemplate c = getTemplate a) } ->
  Lemma
    (requires (eval h1 c (2*norm_length-1) = (eval h0 a (norm_length) * v (getValue h0 b (norm_length - ctr))) * pow2 (bitweight (getTemplate a) (norm_length - ctr)) + eval h0 a (norm_length) * eval h0 b (norm_length - ctr) ))
    (ensures ( eval h1 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length - ctr + 1)))
let multiplication_step_lemma_03 h0 h1 a b ctr c = 
  coerce
    (requires (eval h1 c (2*norm_length-1) = (eval h0 a (norm_length) * v (getValue h0 b (norm_length - ctr))) * pow2 (bitweight (getTemplate a) (norm_length - ctr)) + eval h0 a (norm_length) * eval h0 b (norm_length - ctr) ))
    (ensures ( eval h1 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length - ctr + 1)))
    (fun _ -> gmultiplication_step_lemma_03 h0 h1 a b ctr c)

val helper_lemma_7: ctr:pos{ctr < norm_length} -> 
  Lemma 
    (requires (True))
    (ensures (norm_length - ctr + 1 >= 0 /\ norm_length - ctr + 1 <= norm_length))
    [SMTPat (norm_length - ctr + 1)]
let helper_lemma_7 ctr = 
  FproductLemmas.helper_lemma_7 norm_length ctr

val gmultiplication_aux_lemma:
  h0:heap -> h1:heap -> 
  a:bigint{ConstantTemplate a} -> 
  b:bigint{getTemplate a = getTemplate b} -> ctr:pos{ctr <= norm_length} -> 
  c:bigint_wide{Similar a c /\ Similar b c} -> 
  tmp:bigint_wide{Similar a tmp /\ Similar b tmp /\ Similar c tmp} -> 
  GLemma unit
    (requires (
       (Standardized h0 a) /\ (Standardized h1 a) /\ (Standardized h0 b) /\ (Standardized h1 b) 
       /\ (live h0 c) /\ (live h1 c)  /\ (live h0 tmp) /\ (live h1 tmp) 
       /\ (getLength h1 tmp >= norm_length) /\ (getLength h1 tmp = getLength h0 tmp)
       /\ (getLength h0 c >= 2 * norm_length - 1) /\ (getLength h1 c = getLength h0 c)
       /\ ((norm_length - ctr) < norm_length) /\ (modifies !{getRef c,getRef tmp} h0 h1)
       /\ (maxValueNorm h0 a < pow2 max_limb)
       /\ (maxValueNorm h0 b < pow2 max_limb)
       /\ (maxValue h0 c <= (norm_length - ctr) * maxValueNorm h0 a * maxValueNorm h0 b)
       /\ (maxValue h1 c <= ((norm_length - ctr)+1) * maxValueNorm h0 a * maxValueNorm h0 b)
       /\ (eval h0 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length - ctr))
       /\ (eval h1 c (2*norm_length-1) = eval h0 a (norm_length) * v (getValue h0 b (norm_length - ctr)) * pow2 (bitweight (getTemplate a) (norm_length - ctr)) + eval h0 c (2*norm_length-1))
))
    (ensures (
	(Standardized h1 a) /\ (Standardized h1 b) /\ (live h1 c) /\ (live h1 tmp)
	/\ (getLength h1 tmp >= norm_length) /\ (getLength h1 c >= 2 * norm_length - 1)
	/\ (maxValueNorm h1 a < pow2 max_limb)
	/\ (maxValueNorm h1 b < pow2 max_limb)
	/\ (maxValue h1 c <= (norm_length - ctr + 1) * (maxValueNorm h1 a * maxValueNorm h1 b))
	/\ (eval h1 c (2*norm_length-1) = eval h1 a (norm_length) * eval h1 b (norm_length - ctr + 1)) 
      ))
    []
let gmultiplication_aux_lemma h0 h1 a b ctr c tmp =
  //@@ timeout 50
  no_upd_lemma h0 h1 a (!{getRef c,getRef tmp});
  maxValueNorm_eq_lemma h0 h1 a a; 
  eval_eq_lemma h0 h1 a a norm_length;
  no_upd_lemma h0 h1 b (!{getRef c,getRef tmp}); 
  maxValueNorm_eq_lemma h0 h1 b b; 
  eval_eq_lemma h0 h1 b b (norm_length - ctr);
  eval_eq_lemma h0 h1 b b (norm_length - ctr + 1);
  cut((maxValueNorm h1 a = maxValueNorm h0 a)
       /\ (maxValueNorm h1 b = maxValueNorm h0 b)); 
  cut((norm_length - ctr)+1 = norm_length - ctr + 1 /\ True);
  cut(eval h0 a norm_length = eval h1 a norm_length /\ eval h0 b (norm_length-ctr) = eval h1 b (norm_length - ctr) /\ eval h0 b (norm_length - ctr + 1) = eval h1 b (norm_length - ctr + 1) /\ v (getValue h0 b (norm_length - ctr)) = v (getValue h1 b (norm_length - ctr)));
  Axiomatic.paren_mul_right (norm_length - ctr + 1) (maxValueNorm h1 a) (maxValueNorm h1 b);
  cut(norm_length - ctr + 1 > 0 /\ getLength h0 b >= norm_length - ctr + 1);
  eval_definition h0 b (norm_length - ctr + 1); 
  assert (eval h0 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length - ctr));
  assert (eval h1 c (2*norm_length-1) = eval h0 a (norm_length) * v (getValue h0 b (norm_length - ctr)) * pow2 (bitweight (getTemplate a) (norm_length - ctr)) + eval h0 c (2*norm_length-1));
  assert (eval h1 c (2*norm_length-1) = eval h0 a (norm_length) * v (getValue h0 b (norm_length - ctr)) * pow2 (bitweight (getTemplate a) (norm_length - ctr)) + (eval h0 a (norm_length) * eval h0 b (norm_length - ctr))); 
  FproductLemmas.helper_lemma_12 (eval h0 a norm_length) (v (getValue h0 b (norm_length - ctr))) (pow2 (bitweight (getTemplate a) (norm_length - ctr))) (eval h0 b (norm_length - ctr))

val multiplication_aux_lemma:
  h0:heap -> h1:heap -> 
  a:bigint{ConstantTemplate a} -> 
  b:bigint{getTemplate a = getTemplate b} -> ctr:pos{ctr <= norm_length} -> 
  c:bigint_wide{Similar a c /\ Similar b c} -> 
  tmp:bigint_wide{Similar a tmp /\ Similar b tmp /\ Similar c tmp} -> 
  Lemma
    (requires (
       (Standardized h0 a) /\ (Standardized h1 a) /\ (Standardized h0 b) /\ (Standardized h1 b) 
       /\ (live h0 c) /\ (live h1 c)  /\ (live h0 tmp) /\ (live h1 tmp) 
       /\ (getLength h1 tmp >= norm_length) /\ (getLength h1 tmp = getLength h0 tmp)
       /\ (getLength h0 c >= 2 * norm_length - 1) /\ (getLength h1 c = getLength h0 c)
       /\ ((norm_length - ctr) < norm_length) /\ (modifies !{getRef c,getRef tmp} h0 h1)
       /\ (maxValueNorm h0 a < pow2 max_limb)
       /\ (maxValueNorm h0 b < pow2 max_limb)
       /\ (maxValue h0 c <= (norm_length - ctr) * maxValueNorm h0 a * maxValueNorm h0 b)
       /\ (maxValue h1 c <= ((norm_length - ctr)+1) * maxValueNorm h0 a * maxValueNorm h0 b)
       /\ (eval h0 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length - ctr))
       /\ (eval h1 c (2*norm_length-1) = eval h0 a (norm_length) * v (getValue h0 b (norm_length - ctr)) * pow2 (bitweight (getTemplate a) (norm_length - ctr)) + eval h0 c (2*norm_length-1))
))
    (ensures (
	(Standardized h1 a) /\ (Standardized h1 b) /\ (live h1 c) /\ (live h1 tmp)
	/\ (getLength h1 tmp >= norm_length) /\ (getLength h1 c >= 2 * norm_length - 1)
	/\ (maxValueNorm h1 a < pow2 max_limb)
	/\ (maxValueNorm h1 b < pow2 max_limb)
	/\ (maxValue h1 c <= (norm_length - ctr + 1) * (maxValueNorm h1 a * maxValueNorm h1 b))
	/\ (eval h1 c (2*norm_length-1) = eval h1 a (norm_length) * eval h1 b (norm_length - ctr + 1)) 
      ))
let multiplication_aux_lemma h0 h1 a b ctr c tmp = 
  coerce 
    (requires (
       (Standardized h0 a) /\ (Standardized h1 a) /\ (Standardized h0 b) /\ (Standardized h1 b) 
       /\ (live h0 c) /\ (live h1 c)  /\ (live h0 tmp) /\ (live h1 tmp) 
       /\ (getLength h1 tmp >= norm_length) /\ (getLength h1 tmp = getLength h0 tmp)
       /\ (getLength h0 c >= 2 * norm_length - 1) /\ (getLength h1 c = getLength h0 c)
       /\ ((norm_length - ctr) < norm_length) /\ (modifies !{getRef c,getRef tmp} h0 h1)
       /\ (maxValueNorm h0 a < pow2 max_limb)
       /\ (maxValueNorm h0 b < pow2 max_limb)
       /\ (maxValue h0 c <= (norm_length - ctr) * maxValueNorm h0 a * maxValueNorm h0 b)
       /\ (maxValue h1 c <= ((norm_length - ctr)+1) * maxValueNorm h0 a * maxValueNorm h0 b)
       /\ (eval h0 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length - ctr))
       /\ (eval h1 c (2*norm_length-1) = eval h0 a (norm_length) * v (getValue h0 b (norm_length - ctr)) * pow2 (bitweight (getTemplate a) (norm_length - ctr)) + eval h0 c (2*norm_length-1))
))
    (ensures (
	(Standardized h1 a) /\ (Standardized h1 b) /\ (live h1 c) /\ (live h1 tmp)
	/\ (getLength h1 tmp >= norm_length) /\ (getLength h1 c >= 2 * norm_length - 1)
	/\ (maxValueNorm h1 a < pow2 max_limb)
	/\ (maxValueNorm h1 b < pow2 max_limb)
	/\ (maxValue h1 c <= (norm_length - ctr + 1) * (maxValueNorm h1 a * maxValueNorm h1 b))
	/\ (eval h1 c (2*norm_length-1) = eval h1 a (norm_length) * eval h1 b (norm_length - ctr + 1)) 
      ))
  (fun _ -> gmultiplication_aux_lemma h0 h1 a b ctr c tmp)
  
val multiplication_aux_lemma_2:
  h0:heap -> h1:heap -> h2:heap ->
  a:bigint{ConstantTemplate a} -> 
  b:bigint{getTemplate a = getTemplate b} -> ctr:nat{ctr <= norm_length} -> 
  c:bigint_wide{Similar a c /\ Similar b c} -> 
  tmp:bigint_wide{Similar a tmp /\ Similar b tmp /\ Similar c tmp} -> 
  Lemma 
    (requires (
       (Standardized h0 a) /\ (Standardized h0 b) /\ (live h1 c) /\ (live h1 tmp)
       /\ (Standardized h1 a) /\ (Standardized h1 b) /\ (live h1 c) /\ (live h1 tmp)
       /\ (Standardized h2 a) /\ (Standardized h2 b) /\ (live h2 c) /\ (live h2 tmp)
       /\ (getLength h2 c >= 2 * norm_length - 1)
       /\ (modifies !{getRef c, getRef tmp} h1 h2)
       /\ (modifies !{getRef c, getRef tmp} h0 h1)
       /\ (eval h2 c (2*norm_length-1) = eval h1 a (norm_length) * eval h1 b (norm_length))
    ))
    (ensures (
       (Standardized h0 a) /\ (Standardized h0 b) /\ (live h1 c) 
       /\ (Standardized h2 a) /\ (Standardized h2 b) /\ (live h2 c) 
       /\ (getLength h2 c >= 2 * norm_length - 1)
       /\ (modifies !{getRef c, getRef tmp} h0 h2)
       /\ (eval h2 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length))
  ))
let multiplication_aux_lemma_2 h0 h1 h2 a b ctr c tmp =
  //@@
    cut(modifies !{getRef c, getRef tmp} h0 h2);
    no_upd_lemma h0 h1 a (!{getRef c, getRef tmp}); 
    no_upd_lemma h0 h1 b (!{getRef c, getRef tmp}); 
    eval_eq_lemma h0 h1 a a norm_length; 
    eval_eq_lemma h0 h1 b b norm_length

(* Code : tail recursive calls to run the multiplication *)
val multiplication_aux:
  a:bigint{ConstantTemplate a} -> 
  b:bigint{getTemplate a = getTemplate b} -> ctr:nat{ctr <= norm_length} -> 
  c:bigint_wide{Similar a c /\ Similar b c} -> 
  tmp:bigint_wide{Similar a tmp /\ Similar b tmp /\ Similar c tmp} -> 
  ST unit
     (requires (fun h -> 
	(Standardized h a) /\ (Standardized h b) /\ (live h c) /\ (live h tmp)
	/\ (getLength h tmp >= norm_length) /\ (getLength h c >= 2 * norm_length - 1)
	/\ (maxValueNorm h a < pow2 max_limb)
	/\ (maxValueNorm h b < pow2 max_limb)
	/\ (maxValue h c <= (norm_length - ctr) * (maxValueNorm h a * maxValueNorm h b))
	/\ (eval h c (2*norm_length-1) = eval h a (norm_length) * eval h b (norm_length - ctr))
     ))
     (ensures (fun h0 u h1 -> 
       (Standardized h0 a) /\ (Standardized h0 b) /\ (live h0 c) /\ (live h0 tmp)
       /\ (Standardized h1 a) /\ (Standardized h1 b) /\ (live h1 c) /\ (live h1 tmp)
       /\ (getLength h1 c >= 2 * norm_length - 1)
       /\ (modifies !{getRef c, getRef tmp} h0 h1)
       /\ (maxValueNorm h0 a < pow2 max_limb)
       /\ (maxValueNorm h0 b < pow2 max_limb)
       /\ (eval h1 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length))
       /\ (maxValue h1 c <= norm_length * (maxValueNorm h0 a * maxValueNorm h0 b))
     ))
let rec multiplication_aux a b ctr c tmp = 
  //@@ timeout 50
  let h0 = ST.get() in
  match ctr with
  | 0 -> 
    ()
  | _ -> 
    FproductLemmas.helper_lemma_8 norm_length ctr;
    multiplication_step a b (norm_length - ctr) c tmp;
    let h1 = ST.get() in    
    multiplication_aux_lemma h0 h1 a b ctr c tmp;
    multiplication_aux a b (ctr-1) c tmp;
    let h2 = ST.get() in
    multiplication_aux_lemma_2 h0 h1 h2 a b ctr c tmp

#reset-options

val helper_lemma_16: h0:heap -> h1:heap -> a:bigint -> mods:FStar.Set.set aref ->
  Lemma (requires (Standardized h0 a /\ modifies mods h0 h1 /\ not(FStar.Set.mem (Ref (getRef a)) mods)))
	(ensures (Standardized h1 a))
let helper_lemma_16 h0 h1 a mods = 
  no_upd_lemma h0 h1 a mods

val helper_lemma_13: h0:heap -> h1:heap -> a:bigint ->
  Lemma 
    (requires ((Standardized h0 a) /\ modifies !{} h0 h1))
    (ensures (Standardized h0 a /\ Standardized h1 a
	      /\ live h1 a /\ getLength h1 a >= norm_length
	      /\ maxValueNorm h0 a = maxValueNorm h1 a
	      /\ eval h0 a norm_length = eval h1 a norm_length))
let helper_lemma_13 h0 h1 a = 
  //@@
  no_upd_lemma h0 h1 a (!{});
  helper_lemma_16 h0 h1 a !{};
  eval_eq_lemma h0 h1 a a norm_length; 
  maxValueNorm_eq_lemma h0 h1 a a

val helper_lemma_15: h0:heap -> h1:heap -> c:bigint_wide ->
  Lemma
    (requires (live h0 c /\ IsNull h0 c /\ getLength h0 c >= 2 * norm_length - 1 /\ modifies !{} h0 h1))
    (ensures (live h1 c /\ IsNull h1 c /\ maxValue h1 c <= 0 /\ getLength h1 c >= 2 * norm_length - 1 /\ eval h1 c (2*norm_length-1) = 0))
let helper_lemma_15 h0 h1 c =
  //@@
  no_upd_lemma h0 h1 c !{}; 
  eval_null h1 c (2*norm_length - 1); 
  max_value_of_null_lemma h1 c

#reset-options

opaque val gmultiplication_lemma_1:
  h0:heap -> h1:heap ->
  c:bigint_wide{ConstantTemplate c} -> 
  a:bigint{Similar c a} -> 
  b:bigint{Similar c b} -> 
  GLemma unit
     (requires (
	(Standardized h0 a) /\ (Standardized h0 b) /\ (live h0 c) /\ (IsNull h0 c)
	/\ (getLength h0 c >= 2*norm_length-1)
	/\ (maxValueNorm h0 a < pow2 max_limb)
	/\ (maxValueNorm h0 b < pow2 max_limb)
	/\ (modifies !{} h0 h1)
     ))
     (ensures (
	(Standardized h1 a) /\ (Standardized h1 b) /\ (live h1 c) /\ (IsNull h1 c)
	/\ (getLength h1 c >= 2*norm_length-1)
	/\ (maxValueNorm h1 a < pow2 max_limb)
	/\ (maxValueNorm h1 b < pow2 max_limb)
	/\ (maxValue h1 c <= (norm_length - norm_length) * (maxValueNorm h1 a * maxValueNorm h1 b))
	/\ (eval h1 c (2*norm_length-1) = eval h1 a (norm_length) * eval h1 b (norm_length - norm_length))
     ))
     []
let gmultiplication_lemma_1 h0 h1 c a b =
  helper_lemma_13 h0 h1 a;
  helper_lemma_13 h0 h1 b;
  helper_lemma_15 h0 h1 c;   
  cut(norm_length - norm_length = 0 /\ True); 
  FproductLemmas.auxiliary_lemma_90 (norm_length); 
  FproductLemmas.helper_lemma_13 (maxValueNorm h1 a * maxValueNorm h1 b); 
  cut(True /\ eval h1 b 0 = 0); 
  FproductLemmas.helper_lemma_13 (eval h1 a norm_length)

val multiplication_lemma_1:
  h0:heap -> h1:heap ->
  c:bigint_wide{ConstantTemplate c} -> 
  a:bigint{Similar c a} -> 
  b:bigint{Similar c b} -> 
  Lemma
     (requires (
	(Standardized h0 a) /\ (Standardized h0 b) /\ (live h0 c) /\ (IsNull h0 c)
	/\ (getLength h0 c >= 2*norm_length-1)
	/\ (maxValueNorm h0 a < pow2 max_limb)
	/\ (maxValueNorm h0 b < pow2 max_limb)
	/\ (modifies !{} h0 h1)
     ))
     (ensures (
	(Standardized h1 a) /\ (Standardized h1 b) /\ (live h1 c) /\ (IsNull h1 c)
	/\ (getLength h1 c >= 2*norm_length-1)
	/\ (maxValueNorm h1 a < pow2 max_limb)
	/\ (maxValueNorm h1 b < pow2 max_limb)
	/\ (maxValue h1 c <= (norm_length - norm_length) * (maxValueNorm h1 a * maxValueNorm h1 b))
	/\ (eval h1 c (2*norm_length-1) = eval h1 a (norm_length) * eval h1 b (norm_length - norm_length))
     ))
let multiplication_lemma_1 h0 h1 c a b =
  coerce
     (requires (
	(Standardized h0 a) /\ (Standardized h0 b) /\ (live h0 c) /\ (IsNull h0 c)
	/\ (getLength h0 c >= 2*norm_length-1)
	/\ (maxValueNorm h0 a < pow2 max_limb)
	/\ (maxValueNorm h0 b < pow2 max_limb)
	/\ (modifies !{} h0 h1)
     ))
     (ensures (
	(Standardized h1 a) /\ (Standardized h1 b) /\ (live h1 c) /\ (IsNull h1 c)
	/\ (getLength h1 c >= 2*norm_length-1)
	/\ (maxValueNorm h1 a < pow2 max_limb)
	/\ (maxValueNorm h1 b < pow2 max_limb)
	/\ (maxValue h1 c <= (norm_length - norm_length) * (maxValueNorm h1 a * maxValueNorm h1 b))
	/\ (eval h1 c (2*norm_length-1) = eval h1 a (norm_length) * eval h1 b (norm_length - norm_length))
     ))
     (fun _ -> gmultiplication_lemma_1 h0 h1 c a b)

val helper_lemma_14: h0:heap -> h1:heap -> h2:heap -> c:bigint_wide -> tmp:bigint_wide{Similar c tmp} ->
  Lemma
    (requires (live h0 c /\ live h2 c /\ not(contains h0 (getRef tmp))
	       /\ modifies !{} h0 h1 /\ live h1 tmp /\ modifies !{getRef c, getRef tmp} h1 h2))
    (ensures (modifies !{getRef c} h0 h2))
let helper_lemma_14 h0 h1 h2 c tmp =
  //@@
  ()

val multiplication_lemma_2:
  h0:heap -> h1:heap -> h2:heap -> 
  c:bigint_wide{ConstantTemplate c} -> 
  a:bigint{Similar c a} -> 
  b:bigint{Similar c b} -> 
  tmp:bigint_wide{Similar a tmp /\ Similar b tmp /\ Similar c tmp} ->
  Lemma
     (requires (
	(Standardized h0 a) /\ (Standardized h0 b) /\ (live h0 c) /\ (IsNull h0 c)
	/\ (getLength h0 c >= 2*norm_length-1)
	/\ (maxValueNorm h0 a < pow2 max_limb)
	/\ (maxValueNorm h0 b < pow2 max_limb)
	/\ (modifies !{} h0 h1) /\ not(contains h0 (getRef tmp)) /\ contains h1 (getRef tmp)
	/\ (Standardized h1 a) /\ (Standardized h1 b) /\ (live h1 c) /\ (IsNull h1 c)
	/\ (getLength h1 c >= 2*norm_length-1)
	/\ (maxValueNorm h1 a < pow2 max_limb)
	/\ (maxValueNorm h1 b < pow2 max_limb)
	/\ (maxValue h1 c <= (norm_length - norm_length) * (maxValueNorm h1 a * maxValueNorm h1 b))
	/\ (eval h1 c (2*norm_length-1) = eval h1 a (norm_length) * eval h1 b (norm_length - norm_length))
       /\ (Standardized h2 a) /\ (Standardized h2 b) /\ (live h2 c)
       /\ (getLength h2 c >= 2*norm_length-1)
       /\ (modifies !{getRef c, getRef tmp} h1 h2)
       /\ (eval h2 c (2*norm_length-1) = eval h1 a (norm_length) * eval h1 b (norm_length))
       /\ (maxValue h2 c <= norm_length * (maxValueNorm h1 a * maxValueNorm h1 b))
     ))
     (ensures (
       (Standardized h0 a) /\ (Standardized h0 b) /\ (live h0 c)
       /\ (Standardized h2 a) /\ (Standardized h2 b) /\ (live h2 c)
       /\ (getLength h0 c >= 2*norm_length-1) /\ (getLength h2 c >= 2*norm_length-1)
       /\ (IsNull h0 c) /\ (modifies !{getRef c} h0 h2)
       /\ (maxValueNorm h0 a < pow2 max_limb)
       /\ (maxValueNorm h0 b < pow2 max_limb)
       /\ (eval h2 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length))
       /\ (maxValue h2 c <= norm_length * maxValueNorm h0 a * maxValueNorm h0 b)
     ))
let multiplication_lemma_2 h0 h1 h2 c a b tmp =
  //@@
  helper_lemma_14 h0 h1 h2 c tmp;
  helper_lemma_13 h0 h1 a;
  helper_lemma_13 h0 h1 b

(* Code : core multiplication function *)
val multiplication:
  c:bigint_wide{ConstantTemplate c} -> 
  a:bigint{Similar c a} -> 
  b:bigint{Similar c b} -> 
  ST unit
     (requires (fun h -> 
	(Standardized h a) /\ (Standardized h b) /\ (live h c) /\ (IsNull h c)
	/\ (getLength h c >= 2*norm_length-1)
	/\ (maxValueNorm h a < pow2 max_limb)
	/\ (maxValueNorm h b < pow2 max_limb)
     ))
     (ensures (fun h0 u h1 ->
       (Standardized h0 a) /\ (Standardized h0 b) /\ (live h0 c)
       /\ (Standardized h1 a) /\ (Standardized h1 b) /\ (live h1 c)
       /\ (getLength h0 c >= 2*norm_length-1) /\ (getLength h1 c >= 2 * norm_length - 1)
       /\ (IsNull h0 c) /\ (modifies !{getRef c} h0 h1)
       /\ (maxValueNorm h0 a < pow2 max_limb)
       /\ (maxValueNorm h0 b < pow2 max_limb)
       /\ (eval h1 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length))
       /\ (maxValue h1 c <= norm_length * maxValueNorm h0 a * maxValueNorm h0 b)
     ))
let multiplication c a b =
  //@@
  let h0 = ST.get() in
  let tmp = create_wide norm_length in
  let h1 = ST.get() in
  assert(modifies !{} h0 h1); 
  multiplication_lemma_1 h0 h1 c a b; 
  cut(True /\ getLength h1 tmp >= norm_length);
  constant_template_lemma c a; 
  multiplication_aux a b norm_length c tmp; 
  let h2 = ST.get() in 
  multiplication_lemma_2 h0 h1 h2 c a b tmp
