(*--build-config
  options:--admit_fsi FStar.Set --admit_fsi Parameters --admit_fsi Modulo --verify_module Bignum --z3rlimit 100;
  other-files:FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi seq.fsi FStar.Seq.Base.fst FStar.Seq.Properties.fst FStar.Seq.fst FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Array.fst FStar.Ghost.fst axiomatic.fst intlib.fst lemmas.fst parameters.fsti ../math_interfaces/definitions.fst ../math_interfaces/field.fst uint.fst bigint.fst eval.fst modulo.fsti fsum_lemmas.fst fsum.fst fsum_wide.fst fdifference_lemmas.fst fdifference.fst fscalar_lemmas.fst fscalar.fst fproduct_lemmas.fst fproduct.fst bignum_lemmas.fst;
  --*)

module Bignum

open FStar.Ghost
open FStar.Heap
open Field
open IntLib
open Parameters
open UInt
open Bigint
open Eval
open Modulo

(* Proper bigints to use in the field *)
type Live (h:FStar.Heap.heap) (#size:pos) (b:biginteger size) = (live h b) /\ (getLength h b >= norm_length)

(* Natural mapping from Field elements to Z/pZ *)
assume val nat_to_felem: x:nat{x < reveal prime} -> GTot felem
assume val felem_to_nat: felem -> GTot (x:nat{x < reveal prime})
assume val finite_field_implementation: x:nat{x < reveal prime} -> Lemma (felem_to_nat (nat_to_felem x) = x)
assume val felem_lemma: x:nat -> y:nat -> 
  Lemma (requires (True))
	(ensures (nat_to_felem (x % reveal prime) ^+ nat_to_felem (y % reveal prime) = 
		  nat_to_felem ((x + y) % reveal prime)
		  /\ nat_to_felem (x % reveal prime) ^- nat_to_felem (y % reveal prime) = 
		  nat_to_felem ((x - y) % reveal prime)
		  /\ nat_to_felem (x % reveal prime) ^* nat_to_felem (y % reveal prime) = 
		  nat_to_felem ((x * y) % reveal prime)))
assume val valueOf: h:FStar.Heap.heap -> #size:pos -> b:biginteger size{Live h b} -> GTot (f:felem{f = nat_to_felem ((eval h #size b norm_length)%reveal prime)})

(* Equality in the prime field *)
type Eq (ha:FStar.Heap.heap) (#size_a:pos) (a:biginteger size_a) 
	(hb:FStar.Heap.heap) (#size_b:pos) (b:biginteger size_b) = 
  live ha a /\ live hb b /\ getLength ha a >= norm_length /\ getLength hb b >= norm_length
  /\ valueOf ha a == valueOf hb b

type Eq' (ha:FStar.Heap.heap) (#size_a:pos) (a:biginteger size_a) (la:pos) (hb:FStar.Heap.heap) (#size_b:pos) (b:biginteger size_b) (lb:pos) = 
  live ha a /\ live hb b /\ getLength ha a >= la /\ getLength hb b >= lb 
  /\ Eval.eval ha a la % (reveal prime) = Eval.eval hb b lb % (reveal prime)

(* Normal big integer *)
type Norm (h:FStar.Heap.heap) (#size:pos) (b:biginteger size) =
  Live h b /\ (forall (n:nat). {:pattern (v (getValue h b n))} n < norm_length ==> bitsize (v (getValue h b n)) (getTemplate b n))

(* Serialized values, received and sent to other parties *)
opaque type Serialized (h:FStar.Heap.heap) (b:serialized) =
  live h b /\ getLength h b = bytes_length /\ (forall (n:nat). {:pattern (getValue h b n)} n < bytes_length ==> bitsize (v (getValue h b n)) 8)

val valueOfBytes: h:FStar.Heap.heap -> b:serialized{Serialized h b} -> GTot nat
let valueOfBytes h b = eval h b bytes_length

opaque val gcast_lemma_1: x:wide{v x < pow2 platform_size} -> GLemma unit
  (requires (True)) (ensures (v x % pow2 platform_size = v x)) []
let gcast_lemma_1 x = BignumLemmas.modulo_lemma_1 (v x) (pow2 platform_size)

val cast_lemma_1: x:wide{v x < pow2 platform_size} -> Lemma (v x % pow2 platform_size = v x)
let cast_lemma_1 x = 
  coerce   (requires (True)) (ensures (v x % pow2 platform_size = v x)) 
    (fun _ -> gcast_lemma_1 x)

val copy_to_bigint':
  output:bigint -> input:bigint_wide{Similar input output} -> idx:nat -> len:nat -> ctr:nat{ctr <= len} ->
  ST unit
    (requires (fun h -> 
      (Live h output) /\ (Live h input) /\ (idx+len <= getLength h output) /\ (idx+len<=getLength h input)
      /\ (forall (i:nat). {:pattern (v (getValue h input i))} (i >= idx /\ i < idx+len) ==> v (getValue h input i) < pow2 platform_size) 
      /\ (EqSub h output idx h input idx ctr)
))
    (ensures (fun h0 _ h1 -> 
      Live h0 output /\ Live h1 output
      /\ (EqSub h1 output idx h0 input idx len)
      /\ (modifies !{getRef output} h0 h1)
      /\ (getLength h0 output = getLength h1 output)
    ))
let rec copy_to_bigint' output b idx len ctr = 
  //@@
  let h0 = ST.get() in
  match len - ctr with
  | 0 -> ()
  | _ -> 
    let bi = index_wide b (idx+ctr) in
    let cast = wide_to_limb bi in
    cast_lemma_1 bi;
    cut (v cast = v bi /\ True); 
    upd_limb output (idx+ctr) cast; 
    let h1 = ST.get() in
    no_upd_lemma h0 h1 b !{getRef output}; 
    upd_lemma h0 h1 output (idx+ctr) cast; 
    copy_to_bigint' output b idx len (ctr+1)

val pow2_increases_lemma: n:nat -> m:nat -> Lemma (requires (m < n))
					      (ensures (pow2 m < pow2 n))
					      [SMTPat (pow2 n); SMTPat (pow2 m)]
let pow2_increases_lemma n m = Lemmas.pow2_increases_1 n m

val norm_bigint_lemma_1: h:heap -> b:bigint_wide{Norm h b} -> 
  Lemma (requires (True))
	(ensures (forall (i:nat). {:pattern (v (getValue h b i))} i < norm_length ==> v (getValue h b i) < pow2 platform_size))
let norm_bigint_lemma_1 h b =
  //@@
  parameters_lemma_0 ();
  cut (forall (i:nat). {:pattern (v (getValue h b i))} i < norm_length ==> templ i < platform_size); 
  cut(forall (n:nat) (m:nat). {:pattern (getValue h b)} m < n ==> pow2 m < pow2 n);
  cut (forall (i:nat). {:pattern (v (getValue h b i))} i < norm_length ==> v (getValue h b i) < pow2 (templ i));
  cut (forall (i:nat). {:pattern (v (getValue h b i))} i < norm_length ==> v (getValue h b i) < pow2 platform_size)
  
val copy_to_bigint:
  output:bigint -> 
  input:bigint_wide{Similar input output} -> 
  ST unit
    (requires (fun h -> (Live h output) /\ (Norm h input))) 
    (ensures (fun h0 _ h1 -> Norm h1 output /\ Norm h0 input /\ (modifies !{getRef output} h0 h1)
      /\ eval h0 input norm_length % reveal prime = eval h1 output norm_length % reveal prime
      /\ valueOf h1 output = valueOf h0 input))
let copy_to_bigint output b = 
  //@@
  let h0 = ST.get() in
  norm_bigint_lemma_1 h0 b;
  copy_to_bigint' output b 0 norm_length 0; 
  let h1 = ST.get() in
  cut (forall (i:nat). i < norm_length ==> v (getValue h1 output (0+i)) = v (getValue h0 b (0+i))); 
  cut (forall (i:nat). i < norm_length ==> v (getValue h1 output i) = v (getValue h0 b i));
  eval_eq_lemma h0 h1 b output norm_length;
  cut (eval h0 b norm_length % reveal prime = eval h1 output norm_length % reveal prime /\ True); 
  cut (Norm h1 output); cut(Norm h0 b);
  cut (valueOf h0 b = valueOf h1 output /\ True); cut (modifies !{getRef output} h0 h1)
  
val copy_to_bigint_wide':
  output:bigint_wide -> 
  input:bigint{Similar input output} -> idx:nat -> len:nat -> ctr:nat{ctr <= len} ->
  ST unit
    (requires (fun h -> 
      (Live h output) /\ (Live h input) /\ (idx+len <= getLength h output) /\ (idx+len<=getLength h input)
      /\ (EqSub h output idx h input idx ctr) ))
    (ensures (fun h0 _ h1 -> 
      Live h0 output /\ Live h1 output
      /\ (EqSub h1 output idx h0 input idx len)
      /\ (modifies !{getRef output} h0 h1)
      /\ (getLength h0 output = getLength h1 output)
      /\ (forall (i:nat). {:pattern (v (getValue h1 output i))} (i < idx \/ (i >= idx + len /\ i < getLength h0 output))
	  ==> v (getValue h1 output i) = v (getValue h0 output i))
    ))
let rec copy_to_bigint_wide' output b idx len ctr = 
  //@@
  let h0 = ST.get() in
  match len - ctr with
  | 0 -> ()
  | _ -> 
    let bi = index_limb b (idx+ctr) in
    let cast = limb_to_wide bi in
    cut (v cast = v bi /\ True);
    upd_wide output (idx+ctr) cast;
    let h1 = ST.get() in
    no_upd_lemma h0 h1 b !{getRef output};
    upd_lemma h0 h1 output (idx+ctr) cast;
    copy_to_bigint_wide' output b idx len (ctr+1)

val copy_to_bigint_wide:
  output:bigint_wide -> 
  input:bigint{Similar input output} -> 
  ST unit
    (requires (fun h -> 
      (Live h output) /\ (Live h input)
    )) 
    (ensures (fun h0 _ h1 -> 
      Live h0 output /\ Live h1 output
      /\ (EqSub h1 output 0 h0 input 0 norm_length)
      /\ (Eq h1 output h0 input)
      /\ (modifies !{getRef output} h0 h1)
      /\ (getLength h0 output = getLength h1 output)
      /\ (forall (i:nat). {:pattern (v (getValue h1 output i))} (i >= norm_length /\ i < getLength h0 output)
	  ==> v (getValue h1 output i) = v (getValue h0 output i))
    ))
let copy_to_bigint_wide output b = 
  //@@
  let h0 = ST.get() in
  copy_to_bigint_wide' output b 0 norm_length 0; 
  let h1 = ST.get() in
  cut (forall (i:nat). i < norm_length ==> v (getValue h1 output (0+i)) = v (getValue h0 b (0+i))); 
  cut (forall (i:nat). i < norm_length ==> v (getValue h1 output i) = v (getValue h0 b i));
  eval_eq_lemma h0 h1 b output norm_length;
  cut (eval h0 b norm_length % reveal prime = eval h1 output norm_length % reveal prime /\ True); 
  cut (Live h1 output); cut(Live h0 b)

val copy_lemma: h0:heap -> h1:heap -> #sa:pos -> a:biginteger sa -> #sb:pos -> b:biginteger sb{Similar a b} -> 
  Lemma (requires (Live h0 a /\ Norm h0 b /\ EqSub h1 a 0 h0 b 0 norm_length))
	(ensures (Norm h1 a))
let copy_lemma h0 h1 #sa a #sb b =
  //@@
  cut (forall (i:nat). i < norm_length ==> v (getValue h1 a (0+i)) = v (getValue h0 b (0+i)));
  assert(forall (i:nat). i < norm_length ==> v (getValue h1 a i) = v (getValue h0 b i)); 
  assert(forall (i:nat). getTemplate b i = getTemplate a i)

val erase: b:bigint -> idx:nat -> len:nat -> ctr:nat{ctr <= len} -> ST unit 
    (requires (fun h -> (Live h b) /\ getLength h b >= idx+len
      /\ (forall (i:nat). {:pattern (v (getValue h b i))} (i>= idx /\ i < idx+ctr) ==> v (getValue h b i) = 0))) 
    (ensures (fun h0 _ h1 -> 
      (Live h0 b) /\ (Live h1 b)
      /\ (getLength h0 b = getLength h1 b) /\ (getLength h1 b >= idx+len)
      /\ (forall (i:nat). {:pattern (v (getValue h1 b i))} (i >= idx /\ i < idx+len) ==> v (getValue h1 b i) = 0)
      /\ (EqSub h1 b 0 h0 b 0 idx) /\ (EqSub h1 b (idx+len) h0 b (idx+len) (getLength h0 b-(idx+len)))
      /\ (modifies !{getRef b} h0 h1)
    ))
let rec erase b idx len ctr = 
  //@@
  let h0 = ST.get() in
  match len - ctr with
  | 0 -> ()
  | _ -> 
    upd_limb b (idx+ctr) zero_limb; 
    let h1 = ST.get() in
    upd_lemma h0 h1 b (idx+ctr) zero_limb;
    erase b idx len (ctr+1)

val erase_wide: b:bigint_wide -> idx:nat -> len:nat -> ctr:nat{ctr <= len} -> ST unit 
    (requires (fun h -> (Live h b) /\ getLength h b >= idx+len
      /\ (forall (i:nat). {:pattern (v (getValue h b i))} (i>= idx /\ i < idx+ctr) ==> v (getValue h b i) = 0))) 
    (ensures (fun h0 _ h1 -> 
      (Live h0 b) /\ (Live h1 b)
      /\ (getLength h0 b = getLength h1 b) /\ (getLength h1 b >= idx+len)
      /\ (forall (i:nat). {:pattern (v (getValue h1 b i))} (i >= idx /\ i < idx+len) ==> v (getValue h1 b i) = 0)
      /\ (EqSub h1 b 0 h0 b 0 idx) /\ (EqSub h1 b (idx+len) h0 b (idx+len) (getLength h0 b-(idx+len)))
      /\ (modifies !{getRef b} h0 h1)
    ))
let rec erase_wide b idx len ctr = 
  //@@
  let h0 = ST.get() in
  match len - ctr with
  | 0 -> ()
  | _ -> 
    upd_wide b (idx+ctr) zero_wide; 
    let h1 = ST.get() in
    upd_lemma h0 h1 b (idx+ctr) zero_wide;
    erase_wide b idx len (ctr+1)

#reset-options

val standardized_eq_norm: h:heap -> #size:pos -> b:biginteger size{getTemplate b = templ} -> Lemma
  (ensures (Norm h b <==> Standardized h b))
let standardized_eq_norm h #size b = ()

val modulo:
  output:bigint{getTemplate output = templ} -> 
  input:bigint_wide{Similar input output} -> 
  ST unit
    (requires (fun h -> 
      (Live h input) /\ (Live h output) /\ (satisfies_modulo_constraints h input)
      /\ getLength h input >= 2*norm_length - 1
    )) 
    (ensures (fun h0 _ h1 -> (Live h0 input) /\ getLength h0 input >= 2*norm_length-1
      /\ (Norm h1 output) /\ (Live h0 input)
      /\ eval h1 output norm_length % reveal prime = eval h0 input (2*norm_length-1) % reveal prime
      /\ (modifies !{getRef output, getRef input} h0 h1)
    ))
let modulo output b = 
  //@@
  let h0 = ST.get() in
  freduce_degree b; 
  freduce_coefficients b; 
  let h = ST.get() in
  standardized_eq_norm h b;
  copy_to_bigint output b

#reset-options

opaque val gfsum_lemma: h0:heap -> h1:heap -> res:bigint -> a:bigint -> b:bigint -> GLemma unit
  (requires (Norm h0 a /\ Norm h0 b /\ Norm h1 res
    /\ eval h1 res norm_length % reveal prime = (eval h0 a norm_length + eval h0 b norm_length) % reveal prime ))
  (ensures (Norm h0 a /\ Norm h0 b /\ Norm h1 res
   /\ valueOf h1 res = (valueOf h0 a ^+ valueOf h0 b))) []
let gfsum_lemma h0 h1 res a b =
  felem_lemma (eval h0 a norm_length) (eval h0 b norm_length)

val fsum_lemma: h0:heap -> h1:heap -> res:bigint -> a:bigint -> b:bigint -> Lemma 
  (requires (Norm h0 a /\ Norm h0 b /\ Norm h1 res
    /\ eval h1 res norm_length % reveal prime = (eval h0 a norm_length + eval h0 b norm_length) % reveal prime ))
  (ensures (Norm h0 a /\ Norm h0 b /\ Norm h1 res
   /\ valueOf h1 res = (valueOf h0 a ^+ valueOf h0 b)))
let fsum_lemma h0 h1 res a b =
  coerce   (requires (Norm h0 a /\ Norm h0 b /\ Norm h1 res
    /\ eval h1 res norm_length % reveal prime = (eval h0 a norm_length + eval h0 b norm_length) % reveal prime ))
  (ensures (Norm h0 a /\ Norm h0 b /\ Norm h1 res
   /\ valueOf h1 res = (valueOf h0 a ^+ valueOf h0 b))) 
   (fun _ -> gfsum_lemma h0 h1 res a b)

#reset-options

val lemma_helper_sum_0: h0:heap -> h1:heap -> a:bigint -> b:bigint -> Lemma
  (requires (live h1 a /\ Norm h0 a /\ Norm h0 b /\ 
    getLength h1 a = getLength h0 a /\ Fsum.IsSum h0 h1 a b 0))
  (ensures (live h1 a /\ Norm h0 a /\ Norm h0 b /\ getLength h1 a = getLength h0 a
    /\ (forall (i:nat). {:pattern (v (getValue h1 a i))} i < norm_length ==> 
    v (getValue h1 a i) = v (getValue h0 a i) + v (getValue h0 b i)) ))
let lemma_helper_sum_0 h0 h1 a b = ()

val lemma_helper_sum_1: h0:heap -> h1:heap -> a:bigint -> b:bigint_wide -> Lemma
  (requires (live h0 a /\ live h1 b /\ getLength h0 a >= norm_length /\ getLength h1 b >= norm_length
    /\ EqSub h1 b 0 h0 a 0 norm_length))
  (ensures (live h0 a /\ live h1 b /\ getLength h0 a >= norm_length /\ getLength h1 b >= norm_length
    /\ (forall (i:nat). {:pattern (v (getValue h1 b i))} i < norm_length ==> v (getValue h1 b (i)) = 
	 v (getValue h0 a (i))) ))
let lemma_helper_sum_1 h0 h1 a b = 
  cut(forall (i:nat). {:pattern (0+i)} 0+i = i);
  cut(forall (i:nat). {:pattern (v (getValue h1 b i))} i < norm_length ==> v (getValue h1 b (0+i)) = v (getValue h0 a (0+i)));
  cut(forall (i:nat). {:pattern (v (getValue h1 b i))} i < norm_length ==> v (getValue h1 b (i)) = v (getValue h0 a (i)));
  ()

val lemma_helper_fsum_3: a:nat -> b:nat -> Lemma ( a * 0 + b = b )
let lemma_helper_fsum_3 a b = ()

val glemma_helper_fsum_2: h:heap -> tmp:bigint_wide -> len:nat{len >= norm_length} -> GLemma unit
  (requires (live h tmp /\ getLength h tmp = 2*norm_length - 1 /\ len <= getLength h tmp
    /\ (forall (i:nat). {:pattern (v (getValue h tmp i))} (i >= norm_length /\ i < len) ==> v (getValue h tmp i) = 0) ))
  (ensures (live h tmp /\ getLength h tmp = 2*norm_length - 1 /\ len <= getLength h tmp
    /\ Eval.eval h tmp len = Eval.eval h tmp norm_length)) []
let rec glemma_helper_fsum_2 h tmp len =
  //@@
  if len = norm_length then ()
  else begin 
    glemma_helper_fsum_2 h tmp (len-1);
    assert(Eval.eval h tmp (len-1) = Eval.eval h tmp norm_length);
    Eval.eval_definition h tmp len;
    cut (True /\ Eval.eval h tmp len = pow2 (bitweight (getTemplate tmp) (len-1)) * v (getValue h tmp (len-1))
      + Eval.eval h tmp (len-1));
    lemma_helper_fsum_3 (pow2 (bitweight (getTemplate tmp) (len-1))) (Eval.eval h tmp (len-1))
  end

val lemma_helper_fsum_2: h:heap -> tmp:bigint_wide -> len:nat{len >= norm_length} -> Lemma
  (requires (live h tmp /\ getLength h tmp = 2*norm_length - 1 /\ len <= getLength h tmp
    /\ (forall (i:nat). {:pattern (v (getValue h tmp i))} (i >= norm_length /\ i < len) ==> v (getValue h tmp i) = 0) ))
  (ensures (live h tmp /\ getLength h tmp = 2*norm_length - 1 /\ len <= getLength h tmp
    /\ Eval.eval h tmp len = Eval.eval h tmp norm_length))
let lemma_helper_fsum_2 h tmp len =
  coerce
    (requires (live h tmp /\ getLength h tmp = 2*norm_length - 1 /\ len <= getLength h tmp
    /\ (forall (i:nat). {:pattern (v (getValue h tmp i))} (i >= norm_length /\ i < len) ==> v (getValue h tmp i) = 0) ))
    (ensures (live h tmp /\ getLength h tmp = 2*norm_length - 1 /\ len <= getLength h tmp
    /\ Eval.eval h tmp len = Eval.eval h tmp norm_length))
    (fun _ -> glemma_helper_fsum_2 h tmp len)

#reset-options

val lemma_fsum_1: h1:heap -> h2:heap -> a:bigint -> Lemma
  (requires (live h1 a /\ getLength h1 a >= norm_length /\ modifies !{} h1 h2))
  (ensures  (live h2 a /\ live h1 a /\ getLength h1 a = getLength h2 a  /\ getLength h1 a >= norm_length
    /\ eval h2 a norm_length = eval h1 a norm_length ))
let lemma_fsum_1 h1 h2 a = 
  no_upd_lemma h1 h2 a !{};
  Eval.eval_eq_lemma h1 h2 a a norm_length

val fsum:
  a:bigint{getTemplate a = templ} -> b:bigint{Similar a b} ->
  ST unit
    (requires (fun h -> (Norm h a) /\ (Norm h b) ))
    (ensures (fun h0 _ h1 -> 
      (Norm h0 a) /\ (Norm h1 a) /\ (Norm h0 b)
      /\ (valueOf h1 a = (valueOf h0 a ^+ valueOf h0 b))
      /\ (modifies !{getRef a} h0 h1) ))
let fsum a b =
  //@@
  let h0 = ST.get() in
  standardized_eq_norm h0 a; standardized_eq_norm h0 b;
  Fsum.fsum' a b;
  let h1 = ST.get() in
  let tmp = create_wide (2*norm_length-1) in
  let h2 = ST.get() in
  lemma_fsum_1 h1 h2 a; 
  cut (eval h2 a norm_length = eval h0 a norm_length + eval h0 b norm_length /\ True); 
  copy_to_bigint_wide tmp a;
  let h3 = ST.get() in
  lemma_helper_sum_0 h0 h2 a b;
  lemma_helper_sum_1 h2 h3 a tmp;
  Eval.eval_eq_lemma h2 h3 a tmp norm_length;
  lemma_helper_fsum_2 h3 tmp (2*norm_length-1);
  sum_satisfies_constraints h0 h3 tmp a b;
  cut (True /\ eval h3 tmp norm_length = eval h0 a norm_length + eval h0 b norm_length);
  modulo a tmp;
  let h4 = ST.get() in
  fsum_lemma h0 h4 a a b

#reset-options

opaque val gfdifference_lemma: h0:heap -> h1:heap -> res:bigint -> a:bigint -> b:bigint -> GLemma unit
  (requires (Norm h0 a /\ Norm h0 b /\ Norm h1 res
    /\ eval h1 res norm_length % reveal prime = (eval h0 a norm_length - eval h0 b norm_length) % reveal prime ))
  (ensures (Norm h0 a /\ Norm h0 b /\ Norm h1 res
   /\ valueOf h1 res = (valueOf h0 a ^- valueOf h0 b))) []
let gfdifference_lemma h0 h1 res a b =
  felem_lemma (eval h0 a norm_length) (eval h0 b norm_length)

val fdifference_lemma: h0:heap -> h1:heap -> res:bigint -> a:bigint -> b:bigint -> Lemma 
  (requires (Norm h0 a /\ Norm h0 b /\ Norm h1 res
    /\ eval h1 res norm_length % reveal prime = (eval h0 a norm_length - eval h0 b norm_length) % reveal prime ))
  (ensures (Norm h0 a /\ Norm h0 b /\ Norm h1 res
   /\ valueOf h1 res = (valueOf h0 a ^- valueOf h0 b)))
let fdifference_lemma h0 h1 res a b =
  coerce   (requires (Norm h0 a /\ Norm h0 b /\ Norm h1 res
    /\ eval h1 res norm_length % reveal prime = (eval h0 a norm_length - eval h0 b norm_length) % reveal prime ))
  (ensures (Norm h0 a /\ Norm h0 b /\ Norm h1 res
   /\ valueOf h1 res = (valueOf h0 a ^- valueOf h0 b))) 
   (fun _ -> gfdifference_lemma h0 h1 res a b)

#reset-options

val lemma_helper_diff_0: h0:heap -> h1:heap -> a:bigint -> b:bigint -> Lemma
  (requires (Norm h0 a /\ EqSub h0 a 0 h1 b 0 norm_length))
  (ensures (Norm h1 b /\ Norm h0 a /\
    (forall (i:nat). {:pattern (v (getValue h1 b i))} i < norm_length ==> v (getValue h1 b i) = v (getValue h0 a i))
    /\ Eval.eval h1 b norm_length = Eval.eval h0 a norm_length ))
let lemma_helper_diff_0 h0 h1 a b =
  cut(forall (i:nat). {:pattern (0+i)} 0+i = i);
  cut(forall (i:nat). {:pattern (v (getValue h1 b i))} i < norm_length ==> v (getValue h1 b (0+i)) = v (getValue h0 a (0+i)));
  cut(forall (i:nat). {:pattern (v (getValue h1 b i))} i < norm_length ==> v (getValue h1 b (i)) = v (getValue h0 a (i)));
  Eval.eval_eq_lemma h0 h1 a b norm_length

assume val lemma_helper_diff_1: a:nat -> b:nat -> p:erased pos -> Lemma ( ((a % reveal p) - b) % reveal p = (a - b) % reveal p )

val fdifference:
  a:bigint{getTemplate a = templ} -> b:bigint{Similar a b} ->
  ST unit 
    (requires (fun h -> (Norm h a) /\ (Norm h b))) 
    (ensures (fun h0 _ h1 -> 
      (Norm h0 a) /\ (Norm h0 b) /\ (Norm h1 a)
      /\ (valueOf h1 a = (valueOf h0 b ^- valueOf h0 a))
      /\ (modifies !{getRef a} h0 h1) ))
let fdifference a b = 
  let h0 = ST.get() in
  standardized_eq_norm h0 a; standardized_eq_norm h0 b;
  let b' = create_limb norm_length in
  blit_limb b b' norm_length;
  let h1 = ST.get() in
  no_upd_lemma h0 h1 b !{getRef b'};
  Eval.eval_eq_lemma h0 h1 b b norm_length;
  lemma_helper_diff_0 h0 h1 b b';
  add_big_zero b';
  let h2 = ST.get() in 
  cut (True /\ eval h2 b' norm_length % reveal prime = eval h0 b norm_length % reveal prime);
  no_upd_lemma h0 h2 a !{getRef b'};
  Eval.eval_eq_lemma h0 h2 a a norm_length;
  cut (Standardized h2 a); 
  Fdifference.fdifference' a ndiff' ndiff b';
  let h3 = ST.get() in
  admitP (True /\ eval h3 a norm_length % reveal prime = (eval h0 b norm_length - eval h0 a norm_length) % reveal prime);
  let tmp = create_wide (2*norm_length-1) in 
  let h4 = ST.get() in
  copy_to_bigint_wide tmp a; 
  let h5 = ST.get() in
  admitP(True /\ live h5 a); 
  difference_satisfies_constraints h2 h5 tmp b' a; 
  modulo a tmp;
  let h6 = ST.get() in
  lemma_helper_fsum_2 h5 tmp (2*norm_length-1);
  cut (True /\ eval h6 a norm_length % reveal prime = (eval h0 b norm_length - eval h0 a norm_length) % reveal prime);
  fdifference_lemma h0 h6 a b a;
  cut (modifies !{getRef a} h0 h6)

#reset-options

val fscalar:
  res:bigint{getTemplate res = templ} -> b:bigint{Similar res b} -> #n:nat{n <= ndiff'} -> s:limb{bitsize (v s) n} -> ST unit
  (requires (fun h -> (Live h res) /\ (Norm h b)))
  (ensures (fun h0 _ h1 -> 
    (Norm h0 b) /\ (Live h0 b) /\ (Norm h1 res)
    /\ (valueOf h1 res = (v s +* valueOf h0 b))
    /\ (modifies !{getRef res} h0 h1)
  ))
let fscalar res b #n s =
  //@@
  let h0 = ST.get() in
  standardized_eq_norm h0 b; 
  let tmp = create_wide (2*norm_length-1) in
  Fscalar.scalar' tmp b s; 
  let h = ST.get() in
  admitP(b2t(satisfies_modulo_constraints h tmp));  
  modulo res tmp;
  let h1 = ST.get() in
  admitP(True /\ (valueOf h1 res = (v s +* valueOf h0 b)))

#reset-options

assume val norm_lemma_2: h:heap -> b:bigint -> 
  Lemma (requires (Norm h b))
	(ensures (Norm h b /\ maxValueNorm h b < pow2 Fproduct.max_limb))

val norm_lemma_3: h:heap -> b:bigint -> 
  Lemma (requires (Norm h b /\ getTemplate b = templ))
	(ensures (Standardized h b))
let norm_lemma_3 h b = ()

opaque val gfmul_lemma: h0:heap -> h1:heap -> res:bigint -> a:bigint -> b:bigint -> GLemma unit
  (requires (Norm h0 a /\ Norm h0 b /\ Norm h1 res
    /\ eval h1 res norm_length % reveal prime = (eval h0 a norm_length * eval h0 b norm_length) % reveal prime ))
  (ensures (Norm h0 a /\ Norm h0 b /\ Norm h1 res
   /\ valueOf h1 res = (valueOf h0 a ^* valueOf h0 b))) []
let gfmul_lemma h0 h1 res a b =
  felem_lemma (eval h0 a norm_length) (eval h0 b norm_length)

val fmul_lemma: h0:heap -> h1:heap -> res:bigint -> a:bigint -> b:bigint -> Lemma 
  (requires (Norm h0 a /\ Norm h0 b /\ Norm h1 res
    /\ eval h1 res norm_length % reveal prime = (eval h0 a norm_length * eval h0 b norm_length) % reveal prime ))
  (ensures (Norm h0 a /\ Norm h0 b /\ Norm h1 res
   /\ valueOf h1 res = (valueOf h0 a ^* valueOf h0 b)))
let fmul_lemma h0 h1 res a b =
  coerce   (requires (Norm h0 a /\ Norm h0 b /\ Norm h1 res
    /\ eval h1 res norm_length % reveal prime = (eval h0 a norm_length * eval h0 b norm_length) % reveal prime ))
  (ensures (Norm h0 a /\ Norm h0 b /\ Norm h1 res
   /\ valueOf h1 res = (valueOf h0 a ^* valueOf h0 b))) 
   (fun _ -> gfmul_lemma h0 h1 res a b)

#reset-options

val fmul:
  res:bigint{getTemplate res = templ} -> 
  a:bigint{Similar res a} -> 
  b:bigint{Similar res b} ->
  ST unit 
    (requires (fun h -> (Live h res) /\ (Norm h a) /\ (Norm h b))) 
    (ensures (fun h0 _ h1 -> 
      (Norm h0 a) /\ (Norm h0 b) /\ (Norm h1 res)
      /\ (valueOf h1 res = (valueOf h0 a ^* valueOf h0 b))
      /\ (modifies !{getRef res} h0 h1)
    ))
let fmul res a b = 
  //@@
  let h0 = ST.get() in
  standardized_eq_norm h0 a; standardized_eq_norm h0 b;
  let tmp = create_wide (2*norm_length-1) in
  let h1 = ST.get() in  
  no_upd_lemma h0 h1 a !{};
  no_upd_lemma h0 h1 b !{};
  norm_lemma_2 h1 a; norm_lemma_2 h1 b; 
  norm_lemma_3 h1 a; norm_lemma_3 h1 b;
  Fproduct.multiplication tmp a b;
  let h2 = ST.get() in
  mul_satisfies_constraints h1 h2 tmp a b; 
  modulo res tmp;
  let h3 = ST.get() in
  cut (True /\ eval h3 res norm_length % reveal prime = (eval h0 a norm_length * eval h0 b norm_length) % reveal prime);
  fmul_lemma h0 h3 res a b

val fsquare:
  res:bigint -> a:bigint{Similar res a} ->
  ST unit 
    (requires (fun h -> (Live h res) /\ (Norm h a))) 
    (ensures (fun h0 _ h1 -> 
      (Norm h0 a) /\ (Live h0 res) /\ (Norm h1 res)
      /\ (valueOf h1 res = (valueOf h0 a ^* valueOf h0 a))
      /\ (modifies !{getRef res} h0 h1)
    ))
let fsquare res a =
  fmul res a a
