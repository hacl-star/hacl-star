(**
  This library file should contain types and functions related to big integer 
  representation.
 **)

module Eval

open Field
open IntLib
open Parameters
open UInt
open Bigint
open FStar.ST
open FStar.Seq
open FStar.Heap
open FStar.Array

#reset-options

(* Bit weight of each of the cells of the array of the big integer *)
val bitweight : t:template -> n:nat -> Tot nat
let rec bitweight t n = 
  match n with 
  | 0 -> 0
  | _ -> 
    Lemmas.non_zero_nat_is_pos_2 n;
    Lemmas.nat_plus_nat_is_nat (t (n-1)) (bitweight t (n-1));
    t (n-1) + bitweight t (n-1)

(* GHOST : Eval computes the mathematical value of the bigint from its content and its template *)
val eval : h:heap -> #size:pos -> b:biginteger size{ live h b } -> n:nat{ n <= getLength h b } -> GTot nat
let rec eval h #size b n =
  match n with
  | 0 -> 0
  | _ -> 
    let t = getTemplate b in
    Lemmas.non_zero_nat_is_pos_2 n;    
    Lemmas.nat_times_nat_is_nat (pow2 (bitweight t (n-1))) (v (getValue h b (n-1)));
    Lemmas.nat_plus_nat_is_nat (pow2 (bitweight t (n-1)) * v (getValue h b (n-1))) (eval h b (n-1));
    pow2 (bitweight t (n-1)) * v (getValue h b (n-1)) + eval h b (n-1)

val bitweight_definition: t:template -> n:nat ->
  Lemma (ensures (bitweight t (n+1) = bitweight t n + t n))
let bitweight_definition t n = ()

val eval_definition: h:heap -> #size:pos -> b:biginteger size{live h b} -> n:pos{n <= getLength h b} ->
  Lemma (ensures (eval h b n = pow2 (bitweight (getTemplate b) (n-1)) * v (getValue h b (n-1)) + 
			       eval h b (n-1)))
let eval_definition h #size b n = ()			       

(* Function returning the size of the integer *)
assume val sizeOf: x:nat -> Tot (n:nat{ bitsize x n /\ (forall (m:nat). bitsize x m ==> m >= n) }) 

assume val maxValue: 
  h:heap ->
  #size:pos -> a:biginteger size{ live h a } -> 
  Tot (m:nat{ (forall (n:nat). 
	    n < getLength h a ==> v (getValue h a n) <= m)
	    /\ (exists (i:nat). i < getLength h a /\ v (getValue h a i) = m) })

assume val maxValueNorm: h:heap -> #size:pos -> b:biginteger size{live h b /\ getLength h b >= Parameters.norm_length} -> 
  Tot (m:nat{(forall (n:nat). n < Parameters.norm_length ==> v (getValue h b n) <= m) /\ (exists (i:nat). i < Parameters.norm_length /\ v (getValue h b i) = m)})

assume val maxValueIdx: 
  h:heap ->
  #size:pos -> a:biginteger size{ live h a } -> 
  Tot (m:nat{ (m < getLength h a) 
	    /\ (forall (n:nat). n < getLength h a ==> v (getValue h a n) <= v (getValue h a (m))) })

val maxValue_eq_lemma: 
  ha:heap -> hb:heap -> #size:pos -> a:biginteger size{ live ha a }  -> b:biginteger size{ live hb b } -> 
  Lemma 
    (requires (EqualBigint ha a hb b)) 
    (ensures (maxValue ha a = maxValue hb b))
let maxValue_eq_lemma ha hb #size a b = ()

val maxValueNorm_eq_lemma: 
  ha:heap -> hb:heap -> #size:pos -> a:biginteger size{ live ha a /\ getLength ha a >= Parameters.norm_length }  -> b:biginteger size{ live hb b /\ getLength hb b >= Parameters.norm_length } -> 
  Lemma 
    (requires (EqualBigint ha a hb b)) 
    (ensures (maxValueNorm ha a = maxValueNorm hb b))
let maxValueNorm_eq_lemma ha hb #size a b = ()

val eval_eq_lemma:
  ha:heap -> hb:heap -> 
  #size_a:pos -> a:biginteger size_a{ live ha a } ->
  #size_b:pos -> b:biginteger size_b{ (live hb b) /\ (getTemplate a = getTemplate b) } ->
  len:nat{ (len <= getLength ha a) /\ (len <= getLength hb b) } ->
  Lemma
    (requires ( (forall (i:nat). {:pattern (getValue ha a i) \/ (getValue hb b i)} i < len 
		 ==> v (getValue ha a i) = v (getValue hb b i)) ))
    (ensures ( eval ha a len = eval hb b len ))
let rec eval_eq_lemma ha hb #size_a a #size_b b len =
  match len with
  | 0 -> ()
  | _ -> 
    let t = getTemplate a in
    cut (len > 0 /\ True);
    cut (len-1 <= getLength ha a /\ len-1 <= getLength hb b); 
    cut (forall (i:nat). i < len - 1 ==> i < len); 
    cut (forall (i:nat). i < len - 1 ==> i < len ==> v (getValue ha a i) = v (getValue hb b i)); 
    eval_eq_lemma ha hb a b (len-1); 
    eval_definition ha a len;
    cut (eval ha a len = pow2 (bitweight t (len-1)) * v (getValue ha a (len-1)) + eval ha a (len-1)/\ True)

val eval_partial_eq_lemma:
  ha:heap -> hb:heap -> 
  #size_a:pos -> a:biginteger size_a{ live ha a } ->
  #size_b:pos -> b:biginteger size_b{ (live hb b) /\ (getTemplate a = getTemplate b) } ->
  ctr:nat -> len:nat{ ctr <= len /\ len <= getLength ha a /\ len <= getLength hb b} ->
  Lemma
    (requires ( (forall (i:nat). (i >= ctr /\ i < len) ==> v (getValue ha a i) = v (getValue hb b i))))
    (ensures ( eval ha a len - eval ha a ctr = eval hb b len - eval hb b ctr ))
let rec eval_partial_eq_lemma ha hb #size_a a #size_b b ctr len =
  match len-ctr with
  | 0 -> ()
  | _ -> 
    eval_partial_eq_lemma ha hb a b ctr (len-1)

#reset-options

val helper_lemma_0: n:nat -> Lemma (requires (True)) (ensures (n*0 = 0))
let helper_lemma_0 n = ()

val eval_null:
  h:heap -> #size:pos -> b:biginteger size{ live h b } -> len:nat{ len <= getLength h b } ->
  Lemma
    (requires (forall (i:nat). i < len ==> v (getValue h b i) = 0))
    (ensures (eval h b len = 0))
let rec eval_null h #size b len =
  match len with
  | 0 -> ()
  | _ -> 
    cut (True /\ len > 0);
    eval_null h b (len-1);
    cut (eval h b len = pow2 (bitweight (getTemplate b) (len-1)) * v (getValue h b (len-1)) +
      eval h b (len-1) /\ True);
    cut (v (getValue h b (len-1)) = 0 /\ eval h b (len-1) = 0); 
    helper_lemma_0 (pow2 (bitweight (getTemplate b) (len-1)))

val max_value_of_null_lemma:
  h:heap -> #size:pos -> b:biginteger size{ live h b } ->
  Lemma
    (requires (IsNull h b))
    (ensures (maxValue h b = 0))
let max_value_of_null_lemma h #size b = ()
