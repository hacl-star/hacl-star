module Hacl.Spec.Bignum.Fscalar

open FStar.Mul

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Bignum.Bigint
open Hacl.Bignum.Limb

module U32 = FStar.UInt32

#set-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 20"

val fscalar_spec_:
  output:seqelem_wide -> input:seqelem -> s:limb -> ctr:nat{ctr <= len} ->
  Tot (s':seqelem_wide{
    (forall (i:nat). {:pattern (w (Seq.index s' i))} i < ctr ==>
              w (Seq.index s' i) = v (Seq.index input i) * v s)
    /\ (forall (i:nat). {:pattern (Seq.index s' i)} (i >= ctr /\ i < len) ==>
              Seq.index s' i == Seq.index output i)
       })
  (decreases ctr)
let rec fscalar_spec_ output input s ctr =
  if ctr = 0 then output
  else (
    let i = ctr - 1 in
    let inputi = Seq.index input i in
    let open Hacl.Bignum.Wide in
    let output' = Seq.upd output i (inputi *^ s) in
    fscalar_spec_ output' input s i
  )


val fscalar_spec:
  input:seqelem -> s:limb ->
  Tot (s':seqelem_wide{(forall (i:nat). {:pattern (w (Seq.index s' i))} i < len ==>
                          w (Seq.index s' i) = v (Seq.index input i) * v s) })
let fscalar_spec input s = fscalar_spec_ (Seq.create len wide_zero) input s len


#set-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 100"

val lemma_fscalar_eval_:  a:seqelem_wide -> b:seqelem -> s:limb ->
  ctr:nat{ctr <= len} ->
  Lemma (seval_wide_ (fscalar_spec_ a b s len) ctr = seval_ b ctr * v s)
let rec lemma_fscalar_eval_ a b s ctr =
  if ctr = 0 then ()
  else (
    lemma_fscalar_eval_ a b s (ctr-1);
    cut (seval_wide_ (fscalar_spec_ a b s len) (ctr-1) = seval_ b (ctr-1) * v s);
    cut (w (Seq.index (fscalar_spec_ a b s len) (ctr-1)) = v (Seq.index b (ctr-1)) * v s);
    let x = fscalar_spec_ a b s len in
    cut (seval_wide_ x ctr = pow2 (limb_size * (ctr-1)) * (w (Seq.index x (ctr-1))) + seval_wide_ x (ctr-1));
    cut (seval_ b ctr = pow2 (limb_size * (ctr-1)) * (v (Seq.index b (ctr-1))) + seval_ b (ctr-1));
    Math.Lemmas.distributivity_add_left (seval_ b (ctr-1)) (pow2 (limb_size * (ctr-1)) * (v (Seq.index b (ctr-1)))) (v s)
  )


val lemma_fscalar_eval_0: a:seqelem_wide -> b:seqelem -> s:limb -> Lemma
  (fscalar_spec b s == fscalar_spec_ a b s len)
let lemma_fscalar_eval_0 a b s =
  let s0 = fscalar_spec b s in
  let s1 = fscalar_spec_ a b s len in
  assert(forall (i:nat). i < len ==> w (Seq.index s0 i) == w (Seq.index s1 i));
  Seq.lemma_eq_intro (fscalar_spec b s) (fscalar_spec_ a b s len)

val lemma_fscalar_eval: b:seqelem -> s:limb -> Lemma (seval_wide (fscalar_spec b s) = seval b * v s)
let rec lemma_fscalar_eval b s = lemma_fscalar_eval_ (Seq.create len wide_zero) b s len
