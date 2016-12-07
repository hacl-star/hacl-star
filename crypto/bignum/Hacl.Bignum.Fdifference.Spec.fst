module Hacl.Bignum.Fdifference.Spec

open Hacl.Bignum.Parameters
open Hacl.Bignum.Bigint
open Hacl.Bignum.Limb

module U32 = FStar.UInt32

#set-options "--initial_fuel 1 --max_fuel 1 --z3timeout 20"

let gte_limbs (a:seqelem) (b:seqelem) (l:nat{l <= len}) : GTot Type0 =
  (forall (i:nat). {:pattern (Seq.index a i) \/ (Seq.index b i)} i < l ==> v (Seq.index b i) >= v (Seq.index a i))


val fdifference_spec:
  a:seqelem -> b:seqelem ->
  ctr:nat{ctr <= len /\ gte_limbs a b ctr} ->
  Tot seqelem (decreases ctr)
let rec fdifference_spec a b ctr =
  if ctr = 0 then a
  else (
    let i = ctr - 1 in
    let ai = Seq.index a i in
    let bi = Seq.index b i in
    let a' = Seq.upd a i (bi -^ ai) in
    fdifference_spec a' b i
  )
