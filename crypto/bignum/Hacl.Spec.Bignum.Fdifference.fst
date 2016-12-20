module Hacl.Spec.Bignum.Fdifference

open Hacl.Bignum.Parameters
open Hacl.Bignum.Bigint
open Hacl.Bignum.Limb

module U32 = FStar.UInt32

#set-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 20"

let gte_limbs (a:seqelem) (b:seqelem) (l:nat{l <= len}) : GTot Type0 =
  (forall (i:nat). {:pattern (Seq.index a i) \/ (Seq.index b i)} i < l ==> v (Seq.index b i) >= v (Seq.index a i))


val fdifference_spec:
  a:seqelem -> b:seqelem ->
  ctr:nat{ctr <= len /\ gte_limbs a b ctr} ->
  Tot (s:seqelem{
    (forall (i:nat). {:pattern (v (Seq.index s i))} i < ctr ==> v (Seq.index s i) = v (Seq.index b i) - v (Seq.index a i))
    /\ (forall (i:nat). {:pattern (Seq.index s i)} (i >= ctr /\ i < len) ==> Seq.index s i == Seq.index a i)})
    (decreases ctr)
let rec fdifference_spec a b ctr =
  if ctr = 0 then a
  else (
    let i = ctr - 1 in
    let ai = Seq.index a i in
    let bi = Seq.index b i in
    let a' = Seq.upd a i (bi -^ ai) in
    fdifference_spec a' b i
  )


val lemma_fdifference_eval_:  a:seqelem -> b:seqelem ->
  ctr:nat{ctr <= len /\ gte_limbs a b len} ->
  Lemma (seval_ (fdifference_spec a b len) ctr = seval_ b ctr - seval_ a ctr)
let rec lemma_fdifference_eval_ s s' ctr =
  if ctr = 0 then ()
  else lemma_fdifference_eval_ s s' (ctr-1)

val lemma_fdifference_eval:  a:seqelem -> b:seqelem{gte_limbs a b len} ->
  Lemma (seval_ (fdifference_spec a b len) len = seval_ b len - seval_ a len)
let rec lemma_fdifference_eval s s' = lemma_fdifference_eval_ s s' len
