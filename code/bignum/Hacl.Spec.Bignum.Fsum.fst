module Hacl.Spec.Bignum.Fsum

open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Bignum.Limb


module U32 = FStar.UInt32

#set-options "--max_fuel 1 --initial_fuel 0 --z3rlimit 50"

let red (s:seqelem) (l:nat{l <= len}) = (forall (i:nat). {:pattern (v (Seq.index s i))} (i < l)
                                                 ==> v (Seq.index s i) < pow2 (n - 1))


val fsum_spec:
  s:seqelem -> s':seqelem -> ctr:nat{ctr <= len /\ red s ctr /\ red s' ctr} ->
  Tot (s'':seqelem{(forall (i:nat). {:pattern (v (Seq.index s'' i))}
                              i < ctr ==> v (Seq.index s'' i) = v (Seq.index s i) + v (Seq.index s' i))
    /\ (forall (i:nat). {:pattern (Seq.index s'' i)} (i >= ctr /\ i < len) ==> Seq.index s'' i == Seq.index s i)})
  (decreases ctr)
let rec fsum_spec a b ctr =
  if ctr = 0 then a
  else (
    let i = ctr - 1 in
    let ai = Seq.index a i in
    let bi = Seq.index b i in
    Math.Lemmas.pow2_double_sum (n-1);
    let a' = Seq.upd a i (ai +^ bi) in
    let s'' = fsum_spec a' b i in
    s''
  )



val lemma_fsum_eval_: s:seqelem -> s':seqelem -> ctr:nat{ctr <= len /\ red s len /\ red s' len} ->
  Lemma (seval_ (fsum_spec s s' len) ctr = seval_ s ctr + seval_ s' ctr)
let rec lemma_fsum_eval_ s s' ctr =
  if ctr = 0 then ()
  else lemma_fsum_eval_ s s' (ctr-1)

val lemma_fsum_eval: s:seqelem -> s':seqelem{red s len /\ red s' len} ->
  Lemma (seval (fsum_spec s s' len) = seval s + seval s')
let lemma_fsum_eval s s' = lemma_fsum_eval_ s s' len
