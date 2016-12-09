module Hacl.Bignum.Fscalar.Spec

open Hacl.Bignum.Parameters
open Hacl.Bignum.Bigint
open Hacl.Bignum.Limb

module U32 = FStar.UInt32

#set-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 20"

val fscalar_spec: output:seqelem_wide -> input:seqelem -> s:limb -> ctr:nat{ctr <= len} -> Tot seqelem_wide (decreases ctr)
let rec fscalar_spec output input s ctr =
  if ctr = 0 then output
  else (
    let i = ctr - 1 in
    let inputi = Seq.index input i in
    let open Hacl.Bignum.Wide in
    let output' = Seq.upd output i (inputi *^ s) in
    fscalar_spec output' input s i
  )
