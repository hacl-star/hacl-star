module Hacl.Spec.Bignum.Fsum

open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Bignum.Limb


module U32 = FStar.UInt32


(* Field definition *)
type elem = e:int{e >= 0 /\ e < prime}
let fadd (e1:elem) (e2:elem) : Tot (elem) = (e1 + e2) % prime
let op_At_Plus (e1:elem) (e2:elem) : Tot (elem) = fadd e1 e2
let to_field (s:seqelem) : GTot elem = seval s % prime


#set-options "--max_fuel 1 --initial_fuel 1"

let fsum_spec_pre (s:seqelem) (s':seqelem) (l:nat{l <= len}) =
  (forall (i:nat). {:pattern (v (Seq.index s i)) \/ (v (Seq.index s' i))} (i < l)
             ==> v (Seq.index s i) + v (Seq.index s' i) < pow2 n)


val fsum_spec:
  s:seqelem -> s':seqelem -> ctr:nat{ctr <= len /\ fsum_spec_pre s s' ctr} ->
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


#set-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 20"


val lemma_fsum_eval_: s:seqelem -> s':seqelem -> ctr:nat{ctr <= len /\ fsum_spec_pre s s' len} ->
  Lemma (seval_ (fsum_spec s s' len) ctr = seval_ s ctr + seval_ s' ctr)
let rec lemma_fsum_eval_ s s' ctr =
  if ctr = 0 then ()
  else lemma_fsum_eval_ s s' (ctr-1)

#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val lemma_fsum_field: s:seqelem -> s':seqelem{fsum_spec_pre s s' len} ->
  Lemma (to_field (fsum_spec s s' len) = to_field s @+ to_field s')
let lemma_fsum_field s s' =
  lemma_fsum_eval_ s s' len;
  Math.Lemmas.lemma_mod_plus_distr_l (seval s) (seval s') prime;
  Math.Lemmas.lemma_mod_plus_distr_l (seval s') (to_field s) prime
