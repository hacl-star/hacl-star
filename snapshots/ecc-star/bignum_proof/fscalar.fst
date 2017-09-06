(*--build-config
  options:--admit_fsi FStar.Set --admit_fsi Parameters --verify_module Fscalar --z3rlimit 15;
  other-files:FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi seq.fsi FStar.Seq.Base.fst FStar.Seq.Properties.fst FStar.Seq.fst FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Array.fst FStar.Ghost.fst axiomatic.fst intlib.fst lemmas.fst parameters.fsti uint.fst bigint.fst eval.fst fscalar_lemmas.fst;
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

#reset-options

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

#reset-options

(* Lemma *)
val gscalar_multiplication_lemma_aux:
  h0:heap -> h1:heap -> a:bigint{live h0 a} ->
  b:bigint_wide{live h1 b /\ getTemplate b = getTemplate a} ->
  s:int -> len:pos{ (len <= getLength h0 a)  /\ (len <= getLength h1 b) } ->
  GLemma unit
    (requires ( (eval h0 a (len-1) * s = eval h1 b (len-1))
		/\ (v (getValue h0 a (len-1)) * s = v (getValue h1 b (len-1)))))
    (ensures ( eval h0 a len * s = eval h1 b len )) []
let gscalar_multiplication_lemma_aux h0 h1 a b s len =
  //@@
  paren_mul_left (pow2 (bitweight (getTemplate a) (len-1))) (v (getValue h0 a (len-1))) s;
  distributivity_add_left ((pow2 (bitweight (getTemplate a) (len-1))) * (v (getValue h0 a (len-1)))) (eval h0 a (len-1)) s

#reset-options

(* Lemma *)
val scalar_multiplication_lemma_aux:
  h0:heap -> h1:heap -> a:bigint{live h0 a} ->
  b:bigint_wide{live h1 b /\ getTemplate b = getTemplate a} ->
  s:int -> len:pos{ (len <= getLength h0 a)  /\ (len <= getLength h1 b) } ->
  Lemma
    (requires ( (eval h0 a (len-1) * s = eval h1 b (len-1))
		/\ (v (getValue h0 a (len-1)) * s = v (getValue h1 b (len-1)))))
    (ensures ( eval h0 a len * s = eval h1 b len ))
let scalar_multiplication_lemma_aux h0 h1 a b s len =
  coerce
    (requires ( (eval h0 a (len-1) * s = eval h1 b (len-1))
		/\ (v (getValue h0 a (len-1)) * s = v (getValue h1 b (len-1)))))
    (ensures ( eval h0 a len * s = eval h1 b len ))
    (fun _ -> gscalar_multiplication_lemma_aux h0 h1 a b s len)

#reset-options

(* Lemma *)
val scalar_multiplication_lemma:
  h0:heap -> h1:heap -> a:bigint{live h0 a} -> 
  b:bigint_wide{live h1 b /\ getTemplate b = getTemplate a} ->
  s:int -> len:nat{len <= getLength h0 a /\ len <= getLength h1 b} ->
  Lemma
    (requires (forall (i:nat). i < len ==> v (getValue h0 a i) * s = v (getValue h1 b i)))
    (ensures (eval h0 a len * s = eval h1 b len))

let rec scalar_multiplication_lemma h0 h1 a b s len =
//@@
  match len with
  | 0 -> 
    assert(eval h0 a len = 0); 
    FscalarLemmas.lemma_1 s
  | _ -> 
    FscalarLemmas.lemma_3 len;
    scalar_multiplication_lemma h0 h1 a b s (len-1); 
    scalar_multiplication_lemma_aux h0 h1 a b s len

val scalar_multiplication_tr_1:
  res:bigint_wide -> a:bigint{Similar res a} -> s:limb -> ctr:nat{ctr<norm_length} -> 
  ST unit
     (requires (fun h -> 
       (live h res) /\ (live h a) /\ (getLength h a >= norm_length) /\ (getLength h res >= norm_length)
       /\ (forall (i:nat). (i >= ctr /\ i < norm_length) ==> v (getValue h a i) * v s < pow2 platform_wide)))
     (ensures (fun h0 u h1 -> 
       (live h0 res) /\ (live h1 res) /\ (live h0 a) /\ (live h1 a)
       /\ (getLength h0 res >= norm_length) /\ (getLength h1 res = getLength h0 res)
       /\ (modifies !{getRef res} h0 h1) /\ (getLength h0 a >= norm_length)
       /\ (forall (i:nat). (i >= ctr+1 /\ i < norm_length) ==> v (getValue h0 a i) * v s < pow2 platform_wide) 
       /\ (forall (i:nat). (i < getLength h1 res /\ i <> ctr) ==> (getValue h1 res i == getValue h0 res i))
       /\ (v (getValue h1 res ctr) = v (getValue h0 a ctr) * v s)
     ))
let rec scalar_multiplication_tr_1 res a s ctr =
    let ai = index_limb a ctr in
    let z = mul_limb_to_wide ai s in
    upd_wide res ctr z

val scalar_multiplication_tr_2:
  h0:heap -> h1:heap -> h2:heap -> res:bigint_wide -> a:bigint{Similar res a} -> s:limb -> ctr:nat{ctr<norm_length} -> 
  Lemma
     (requires (
       (live h1 res) /\ (live h2 res) /\ (live h1 a) /\ (live h2 a) /\ live h0 a /\ live h0 res
       /\ modifies !{getRef res} h0 h1
       /\ (modifies !{getRef res} h1 h2) /\ (getLength h1 a >= norm_length)
       /\ (forall (i:nat). {:pattern (getValue h1 a i)} (i >= ctr+1 /\ i < norm_length) ==> v (getValue h1 a i) * v s < pow2 platform_wide)
       /\ (getLength h1 res >= norm_length) /\ (getLength h2 res = getLength h1 res)
       /\ getLength h0 res = getLength h1 res
       /\ (forall (i:nat). {:pattern (getValue h1 res i)} (i < getLength h1 res /\ i <> ctr) ==> getValue h1 res i == getValue h0 res i)
       /\ v (getValue h1 res ctr) = v (getValue h0 a ctr) * v s
       /\ (forall (i:nat{(i>= ctr+1 /\ i < norm_length)}). {:pattern (getValue h2 res i)} v (getValue h2 res i) = v (getValue h1 a i) * v s)
       /\ (forall (i:nat{(i < getLength h2 res /\ (i < ctr+1 \/ i >= norm_length))}). {:pattern (getValue h2 res i)}
	   (getValue h2 res i == getValue h1 res i))
       /\ (Seq.Eq (sel h1 (getRef a)) (sel h2 (getRef a))) ))
     (ensures (
       (live h0 res) /\ (live h2 res) /\ (live h0 a) /\ (live h2 a)
       /\ (modifies !{getRef res} h0 h2) /\ (getLength h0 a >= norm_length)
       /\ (forall (i:nat). (i >= ctr /\ i < norm_length) ==> v (getValue h0 a i) * v s < pow2 platform_wide)
       /\ (getLength h0 res >= norm_length) /\ (getLength h2 res = getLength h0 res)
       /\ (forall (i:nat{(i>= ctr /\ i < norm_length)}). v (getValue h2 res i) = v (getValue h0 a i) * v s)
       /\ (forall (i:nat{(i < getLength h2 res /\ (i < ctr \/ i >= norm_length))}). 
	   (getValue h2 res i == getValue h0 res i))
       /\ (Seq.Eq (sel h0 (getRef a)) (sel h2 (getRef a)))
     ))
let scalar_multiplication_tr_2 h0 h1 h2 res a s ctr =
  no_upd_lemma h0 h1 a !{getRef res};
  no_upd_lemma h1 h2 a !{getRef res};
  ()

(* Code *)
(* Tail recursive version of the scalar multiplication *)
val scalar_multiplication_tr:
  res:bigint_wide -> a:bigint{Similar res a} -> s:limb -> ctr:nat{ctr<=norm_length} -> 
  ST unit
     (requires (fun h -> 
       (live h res) /\ (live h a) /\ (getLength h a >= norm_length) /\ (getLength h res >= norm_length)
       /\ (forall (i:nat). (i >= ctr /\ i < norm_length) ==> v (getValue h a i) * v s < pow2 platform_wide)))
     (ensures (fun h0 u h1 -> 
       (live h0 res) /\ (live h1 res) /\ (live h0 a) /\ (live h1 a)
       /\ (modifies !{getRef res} h0 h1) /\ (getLength h0 a >= norm_length)
       /\ (forall (i:nat). (i >= ctr /\ i < norm_length) ==> v (getValue h0 a i) * v s < pow2 platform_wide)
       /\ (getLength h0 res >= norm_length) /\ (getLength h1 res = getLength h0 res)
       /\ (forall (i:nat{(i>= ctr /\ i < norm_length)}). v (getValue h1 res i) = v (getValue h0 a i) * v s)
       /\ (forall (i:nat{(i < getLength h1 res /\ (i < ctr \/ i >= norm_length))}). 
	   (getValue h1 res i == getValue h0 res i))
       /\ (Seq.Eq (sel h0 (getRef a)) (sel h1 (getRef a)))
     ))
let rec scalar_multiplication_tr res a s ctr =
  //@@
  let h0 = ST.get() in
  match norm_length - ctr with
  | 0 -> ()
  | _ -> 
     let i = ctr in
     FscalarLemmas.lemma_4 norm_length ctr; 
     scalar_multiplication_tr_1 res a s ctr; 
     let h1 = ST.get() in 
     no_upd_lemma h0 h1 a (!{getRef res});
     scalar_multiplication_tr res a s (ctr+1); 
     let h2 = ST.get() in
     scalar_multiplication_tr_2 h0 h1 h2 res a s ctr

(* Lemma *)   	 
val gtheorem_scalar_multiplication: 
  h0:heap -> h1:heap -> a:bigint{live h0 a} -> s:limb -> len:nat{len <= getLength h0 a} ->
  b:bigint_wide{live h1 b /\ len <= getLength h1 b /\ getTemplate a = getTemplate b} ->
  GLemma unit
    (requires (forall (i:nat). i < len ==> v (getValue h1 b i) = v (getValue h0 a i) * v s))
    (ensures ((eval h1 b len) = (eval h0 a len) * v s)) []
let gtheorem_scalar_multiplication h0 h1 a s len b = 
  scalar_multiplication_lemma h0 h1 a b (v s) len; ()

(* Lemma *)   	 
val theorem_scalar_multiplication: 
  h0:heap -> h1:heap -> a:bigint{live h0 a} -> s:limb -> len:nat{len <= getLength h0 a} ->
  b:bigint_wide{live h1 b /\ len <= getLength h1 b /\ getTemplate a = getTemplate b} ->
  Lemma 
    (requires (forall (i:nat). i < len ==> v (getValue h1 b i) = v (getValue h0 a i) * v s))
    (ensures ((eval h1 b len) = (eval h0 a len) * v s))
let theorem_scalar_multiplication h0 h1 a s len b = 
  coerce
    (requires (forall (i:nat). i < len ==> v (getValue h1 b i) = v (getValue h0 a i) * v s))
    (ensures ((eval h1 b len) = (eval h0 a len) * v s))
    (fun _ -> gtheorem_scalar_multiplication h0 h1 a s len b)

#reset-options

val gauxiliary_lemma_2: 
  ha:heap -> a:bigint{Standardized ha a} -> s:limb -> i:nat{ i < norm_length} ->
  GLemma unit
    (requires (True))
    (ensures (bitsize (v (getValue ha a i) * v s) (platform_wide)))
    []
let gauxiliary_lemma_2 ha a s i =
  UInt.mul_lemma #(templ i) (v (getValue ha a i)) #platform_size (v s);
  parameters_lemma_0 ();
  Lemmas.pow2_increases_2 platform_wide (templ i + platform_size)

val auxiliary_lemma_2: 
  ha:heap -> a:bigint{Standardized ha a} ->
  s:limb -> i:nat{ i < norm_length} ->
  Lemma (requires (True))
	(ensures (bitsize (v (getValue ha a i) * v s) (platform_wide)))
	[SMTPat (v (getValue ha a i) * v s)]
let auxiliary_lemma_2 ha a s i =
  coerce
    (requires (True))
    (ensures (bitsize (v (getValue ha a i) * v s) (platform_wide)))
    (fun _ -> gauxiliary_lemma_2 ha a s i)

#reset-options

val auxiliary_lemma_0: 
  ha:heap -> a:bigint{Standardized ha a} -> s:limb ->
  Lemma (requires (True))
	(ensures (forall (i:nat). i < norm_length ==> bitsize (v (getValue ha a i) * v s) platform_wide))
let auxiliary_lemma_0 ha a s = ()

val auxiliary_lemma_1:
  h0:heap -> h1:heap -> b:bigint{Standardized h0 b} -> mods:FStar.Set.set aref ->
  Lemma (requires (live h1 b /\ modifies mods h0 h1 /\ not (FStar.Set.mem (Ref (getRef b)) mods)))
	(ensures (Standardized h1 b))
let auxiliary_lemma_1 h0 h1 b mods = ()	

#reset-options

val scalar':
  res:bigint_wide{getTemplate res = templ} -> 
  a:bigint{Similar res a} -> s:limb ->  
  ST unit
     (requires (fun h -> 
       (Standardized h a) /\ (live h res) /\ (getLength h res >= norm_length)))
     (ensures (fun h0 u h1 -> 
       (live h0 res) /\ (live h1 res) /\ (Standardized h0 a) /\ (Standardized h1 a) 
       /\ (modifies !{getRef res} h0 h1)
       /\ (getLength h0 res >= norm_length)
       /\ (getLength h1 res = getLength h0 res)
       /\ (eval h1 res norm_length = eval h0 a norm_length * v s)
     ))
let scalar' res a s =
  let h0 = ST.get() in  
  auxiliary_lemma_0 h0 a s; 
  scalar_multiplication_tr res a s 0; 
  let h1 = ST.get() in
  no_upd_lemma h0 h1 a (!{getRef res});
  auxiliary_lemma_1 h0 h1 a (!{getRef res}); 
  theorem_scalar_multiplication h0 h1 a s norm_length res; 
  ()

	       
