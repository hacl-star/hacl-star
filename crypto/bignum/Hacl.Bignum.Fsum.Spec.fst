module Hacl.Bignum.Fsum.Spec

open Hacl.Bignum.Parameters
open Hacl.Bignum.Bigint
open Hacl.Bignum.Limb
open Hacl.Bignum.Predicates


module U32 = FStar.UInt32

#set-options "--max_fuel 1 --initial_fuel 1"

let red (s:seqelem) (l:nat{l <= len}) = (forall (i:nat). (i < l) ==> v (Seq.index s i) < pow2 (n - 1))


val fsum_spec: s:seqelem -> s':seqelem -> ctr:nat{ctr <= len /\ red s ctr /\ red s' ctr} -> Tot seqelem
  (decreases ctr)
let rec fsum_spec a b ctr =
  if ctr = 0 then a
  else (
    let i = ctr - 1 in
    let ai = Seq.index a i in
    let bi = Seq.index b i in
    Math.Lemmas.pow2_double_sum (n-1);
    let a' = Seq.upd a i (ai +^ bi) in
    fsum_spec a' b i
  )

