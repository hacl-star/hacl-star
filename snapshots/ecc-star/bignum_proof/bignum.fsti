(*--build-config
  options:--admit_fsi FStar.Set --admit_fsi Parameters --admit_fsi Modulo --verify_module Bignum;
  other-files:FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst seq.fsi FStar.Seq.Base.fst FStar.Seq.Properties.fst FStar.Seq.fst FStar.Array.fst FStar.Ghost.fst axiomatic.fst intlib.fst lemmas.fst parameters.fsti ../math_interfaces/definitions.fst ../math_interfaces/field.fst uint.fst bigint.fst eval.fst modulo.fsti;
  --*)

(* Interface to be made available to the concrete curve code *)

module Bignum

open FStar.Ghost
open Field
open IntLib
open Parameters
open UInt
open Bigint
open Eval
open Modulo

(* Proper bigints to use in the field *)
type Live (h:FStar.Heap.heap) (#size:pos) (b:biginteger size) = (live h b) /\ (getLength h b >= norm_length)

val nat_to_felem: x:nat{x < reveal prime} -> GTot felem
val felem_to_nat: felem -> GTot (x:nat{x < reveal prime})
val finite_field_implementation: x:nat{x < reveal prime} -> Lemma (felem_to_nat (nat_to_felem x) = x)
val felem_lemma: x:nat -> y:nat -> 
  Lemma (requires (True))
	(ensures (nat_to_felem (x % reveal prime) ^+ nat_to_felem (y % reveal prime) = 
		  nat_to_felem ((x + y) % reveal prime)
		  /\ nat_to_felem (x % reveal prime) ^- nat_to_felem (y % reveal prime) = 
		  nat_to_felem ((x - y) % reveal prime)
		  /\ nat_to_felem (x % reveal prime) ^* nat_to_felem (y % reveal prime) = 
		  nat_to_felem ((x * y) % reveal prime)))
(* Shorter standard version of the 'eval' function *)
val valueOf: h:FStar.Heap.heap -> #size:pos -> b:biginteger size{Live h b} -> GTot (f:felem{f = nat_to_felem ((eval h #size b norm_length)%reveal prime)})

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
  Live h b /\ (forall (n:nat). n < norm_length ==> bitsize (v (getValue h b n)) (getTemplate b n))

(* Serialized values, received and sent to other parties *)
opaque type Serialized (h:FStar.Heap.heap) (b:serialized) =
  live h b /\ getLength h b = bytes_length /\ (forall (n:nat). {:pattern (getValue h b n)} n < bytes_length ==> bitsize (v (getValue h b n)) 8)
  
val valueOfBytes: h:FStar.Heap.heap -> b:serialized{Serialized h b} -> GTot (f:nat{f = eval h b bytes_length})

(* Copy from a large big integer to a standard big integer *)
(* val copy_to_bigint: *)
(*   output:bigint ->  *)
(*   input:bigint_wide{Similar input output} ->  *)
(*   ST unit *)
(*     (requires (fun h ->  *)
(*       (Live h output) /\ (Live h input)  *)
(*       /\ (maxValueNorm h input < pow2 platform_size) *)
(*     ))  *)
(*     (ensures (fun h0 _ h1 ->  *)
(*       Live h0 output /\ Live h1 output *)
(*       /\ (EqSub h1 output 0 h0 input 0 norm_length) *)
(*       /\ (Eq h1 output h0 input) *)
(*       /\ (modifies !{getRef output} h0 h1) *)
(*       /\ (getLength h0 output = getLength h1 output) *)
(*     )) *)

val copy_bigint:
  output:bigint -> 
  input:bigint_wide{Similar input output} -> 
  ST unit
    (requires (fun h -> 
      (Live h output) /\ (Norm h input) 
    )) 
    (ensures (fun h0 _ h1 -> 
      Norm h1 output /\ Norm h0 input
      /\ (modifies !{getRef output} h0 h1)
      /\ valueOf h1 output == valueOf h0 input
    ))

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

val copy_to_bigint:
  output:bigint -> 
  input:bigint_wide{Similar input output} -> 
  ST unit
    (requires (fun h -> (Live h output) /\ (Norm h input))) 
    (ensures (fun h0 _ h1 -> Norm h1 output /\ Norm h0 input /\ (modifies !{getRef output} h0 h1)
      /\ eval h0 input norm_length % reveal prime = eval h1 output norm_length % reveal prime
      /\ valueOf h1 output = valueOf h0 input))

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
    ))

val copy_bigint_wide:
  output:bigint_wide -> 
  input:bigint{Similar input output} -> 
  ST unit
    (requires (fun h -> 
      (Live h output) /\ (Norm h input) 
    )) 
    (ensures (fun h0 _ h1 -> 
      Norm h1 output /\ Norm h0 input
      /\ (modifies !{getRef output} h0 h1)
      /\ valueOf h1 output == valueOf h0 input
    ))

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
    ))

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

val fsum:
  a:bigint{getTemplate a = templ} -> b:bigint{Similar a b} ->
  ST unit
    (requires (fun h -> (Norm h a) /\ (Norm h b) ))
    (ensures (fun h0 _ h1 -> 
      (Norm h0 a) /\ (Norm h1 a) /\ (Norm h0 b)
      /\ (valueOf h1 a = (valueOf h0 a ^+ valueOf h0 b))
      /\ (modifies !{getRef a} h0 h1) ))

val fdifference:
  a:bigint{getTemplate a = templ} -> b:bigint{Similar a b} ->
  ST unit 
    (requires (fun h -> (Norm h a) /\ (Norm h b))) 
    (ensures (fun h0 _ h1 -> 
      (Norm h0 a) /\ (Norm h0 b) /\ (Norm h1 a)
      /\ (valueOf h1 a = (valueOf h0 b ^- valueOf h0 a))
      /\ (modifies !{getRef a} h0 h1)
    ))

val fscalar:
  res:bigint{getTemplate res = templ} -> b:bigint{Similar res b} -> #n:nat{n <= ndiff'} -> s:limb{bitsize (v s) n} -> ST unit
  (requires (fun h -> (Live h res) /\ (Norm h b)))
  (ensures (fun h0 _ h1 -> 
    (Norm h0 b) /\ (Live h0 b) /\ (Norm h1 res)
    /\ (valueOf h1 res = (v s +* valueOf h0 b))
    /\ (modifies !{getRef res} h0 h1)
  ))

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

val fsquare:
  res:bigint -> a:bigint{Similar res a} ->
  ST unit 
    (requires (fun h -> (Live h res) /\ (Norm h a))) 
    (ensures (fun h0 _ h1 -> 
      (Norm h0 a) /\ (Live h0 res) /\ (Norm h1 res)
      /\ (valueOf h1 res = (valueOf h0 a ^* valueOf h0 a))
      /\ (modifies !{getRef res} h0 h1)
    ))
