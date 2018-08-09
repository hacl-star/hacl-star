module Hacl.Spec.Bignum.Modulo

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul
open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Bignum.Limb


#set-options "--initial_fuel 0 --max_fuel 0"

val reduce_pre: seqelem -> GTot Type0
let reduce_pre s = admit()

val reduce_spec: s:seqelem{reduce_pre s} -> Tot (s':seqelem)
let reduce_spec s = admit()

val lemma_reduce_spec: s:seqelem{reduce_pre s} -> Lemma
  (seval (reduce_spec s) % prime
   = (pow2 limb_size * seval (Seq.append (Seq.slice s 1 len) (Seq.slice s 0 1))) % prime)
let lemma_reduce_spec s = admit()


val carry_top_pre: seqelem -> GTot Type0
let carry_top_pre s = admit()

val carry_top_spec: s:seqelem{carry_top_pre s} -> Tot seqelem
let carry_top_spec s = admit()

val lemma_carry_top_spec_: s:seqelem{carry_top_pre s} -> Lemma
  (let s' = carry_top_spec s in
    v (Seq.index s' 2) = v (Seq.index s 2) % pow2 42
    /\ v (Seq.index s' 0) = 5 * (v (Seq.index s 2) / pow2 42) + v (Seq.index s 0)
    /\ v (Seq.index s' 1) = v (Seq.index s 1))
let lemma_carry_top_spec_ s = admit()

val carry_top_wide_pre: seqelem_wide -> GTot Type0
let carry_top_wide_pre s = admit()

val carry_top_wide_spec: s:seqelem_wide{carry_top_wide_pre s} -> Tot seqelem_wide
let carry_top_wide_spec s = admit()

val lemma_carry_top_wide_spec: s:seqelem_wide{carry_top_wide_pre s} -> Lemma
  (seval_wide (carry_top_wide_spec s) % prime = seval_wide s % prime)
let lemma_carry_top_wide_spec s = admit()
