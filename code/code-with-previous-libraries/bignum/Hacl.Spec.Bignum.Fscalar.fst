module Hacl.Spec.Bignum.Fscalar

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Bignum.Limb

module U32 = FStar.UInt32

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 20"

val fscalar_spec:
  input:seqelem -> s:limb ->
  Tot (s':seqelem_wide{
    (forall (i:nat). {:pattern (w (Seq.index s' i))} i < len ==>
              w (Seq.index s' i) = v (Seq.index input i) * v s)
       })
let fscalar_spec input s =
  Spec.Loops.seq_map (fun x -> Hacl.Bignum.Wide.mul_wide x s) input


#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 400"

private
val lemma_fscalar_eval_: b:seqelem -> s:limb ->
  ctr:nat{ctr <= len} ->
  Lemma (seval_wide_ (fscalar_spec b s) ctr = seval_ b ctr * v s)
let rec lemma_fscalar_eval_ b s ctr =
  if ctr = 0 then ()
  else (
    lemma_fscalar_eval_ b s (ctr-1);
    cut (seval_wide_ (fscalar_spec b s) (ctr-1) = seval_ b (ctr-1) * v s);
    cut (w (Seq.index (fscalar_spec b s) (ctr-1)) = v (Seq.index b (ctr-1)) * v s);
    let x = fscalar_spec b s in
    cut (seval_wide_ x ctr = pow2 (limb_size * (ctr-1)) * (w (Seq.index x (ctr-1))) + seval_wide_ x (ctr-1));
    cut (seval_ b ctr = pow2 (limb_size * (ctr-1)) * (v (Seq.index b (ctr-1))) + seval_ b (ctr-1));
    Math.Lemmas.distributivity_add_left (seval_ b (ctr-1)) (pow2 (limb_size * (ctr-1)) * (v (Seq.index b (ctr-1)))) (v s)
  )


val lemma_fscalar_eval: b:seqelem -> s:limb -> Lemma (seval_wide (fscalar_spec b s) = seval b * v s)
let lemma_fscalar_eval b s = lemma_fscalar_eval_ b s len
