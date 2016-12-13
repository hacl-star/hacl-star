module Hacl.Bignum.Fscalar.Spec

open FStar.Mul

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Bignum.Bigint
open Hacl.Bignum.Limb

module U32 = FStar.UInt32

#set-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 20"

val fscalar_spec:
  output:seqelem_wide -> input:seqelem -> s:limb -> ctr:nat{ctr <= len} ->
  Tot (s':seqelem_wide{
    (forall (i:nat). {:pattern (w (Seq.index s' i))} i < ctr ==>
              w (Seq.index s' i) = v (Seq.index input i) * v s)
    /\ (forall (i:nat). {:pattern (Seq.index s' i)} (i >= ctr /\ i < len) ==>
              Seq.index s' i == Seq.index output i)
       })
  (decreases ctr)
let rec fscalar_spec output input s ctr =
  if ctr = 0 then output
  else (
    let i = ctr - 1 in
    let inputi = Seq.index input i in
    let open Hacl.Bignum.Wide in
    let output' = Seq.upd output i (inputi *^ s) in
    fscalar_spec output' input s i
  )

#set-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 50"

val lemma_fscalar_eval_:  a:seqelem_wide -> b:seqelem -> s:limb ->
  ctr:nat{ctr <= len} ->
  Lemma (seval_wide_ (fscalar_spec a b s len) ctr = seval_ b ctr * v s)
let rec lemma_fscalar_eval_ a b s ctr =
  if ctr = 0 then ()
  else (
    lemma_fscalar_eval_ a b s (ctr-1);
    cut (seval_wide_ (fscalar_spec a b s len) (ctr-1) = seval_ b (ctr-1) * v s);
    cut (w (Seq.index (fscalar_spec a b s len) (ctr-1)) = v (Seq.index b (ctr-1)) * v s);
    let x = fscalar_spec a b s len in
    cut (seval_wide_ x ctr = pow2 (limb_size * (ctr-1)) * (w (Seq.index x (ctr-1))) + seval_wide_ x (ctr-1));
    cut (seval_ b ctr = pow2 (limb_size * (ctr-1)) * (v (Seq.index b (ctr-1))) + seval_ b (ctr-1));
    Math.Lemmas.distributivity_add_left (seval_ b (ctr-1)) (pow2 (limb_size * (ctr-1)) * (v (Seq.index b (ctr-1)))) (v s)
  )


val lemma_fscalar_eval:  a:seqelem_wide -> b:seqelem -> s:limb ->
  Lemma (seval_wide_ (fscalar_spec a b s len) len = seval_ b len * v s)
let rec lemma_fscalar_eval a b s = lemma_fscalar_eval_ a b s len
