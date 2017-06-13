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


module U32 = FStar.UInt32

val add_zero_pre: seqelem -> GTot Type0

val add_zero_spec: s:seqelem{add_zero_pre s} -> Tot seqelem

val lemma_add_zero_spec: s:seqelem{add_zero_pre s} -> Lemma
  (seval (add_zero_spec s) % prime = seval s % prime)

val carry_top_pre: seqelem -> GTot Type0

val carry_top_spec: s:seqelem{carry_top_pre s} -> Tot seqelem

val lemma_carry_top_spec: s:seqelem{carry_top_pre s} -> Lemma
  (seval (carry_top_spec s) % prime = seval s % prime)

val reduce_pre: seqelem -> GTot Type0

val reduce_spec: s:seqelem{reduce_pre s} -> Tot seqelem

val lemma_reduce_spec: s:seqelem{reduce_pre s} -> Lemma
  (seval (reduce_spec s) % prime
   = (pow2 limb_size * seval (Seq.append (Seq.slice s 1 len) (Seq.slice s 0 1))) % prime)

val carry_top_wide_pre: seqelem_wide -> GTot Type0

val carry_top_wide_spec: s:seqelem_wide{carry_top_wide_pre s} -> Tot seqelem_wide

val lemma_carry_top_wide_spec: s:seqelem_wide{carry_top_wide_pre s} -> Lemma
  (seval_wide (carry_top_wide_spec s) % prime = seval_wide s % prime)
