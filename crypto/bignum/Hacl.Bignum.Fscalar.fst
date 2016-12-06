module Hacl.Bignum.Fscalar

open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Parameters
open Hacl.Bignum.Bigint
open Hacl.Bignum.Limb


module U32 = FStar.UInt32

type seqelem = s:Seq.seq limb{Seq.length s = len}
type seqelem_wide = s:Seq.seq wide{Seq.length s = len}


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


val fscalar_:
  output:felem_wide ->
  input:felem{disjoint input output} ->
  s:limb ->
  i:ctr{U32.v i <= len} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input))
    (ensures (fun h0 _ h1 -> live h0 input /\ live h0 output /\ live h1 output /\ modifies_1 output h0 h1
      /\ as_seq h1 output == fscalar_spec (as_seq h0 output) (as_seq h0 input) s (U32.v i)))
let rec fscalar_ output b s i =
  if U32 (i =^ 0ul) then ()
  else (
    let i = U32 (i -^ 1ul) in
    let bi = b.(i) in
    let open Hacl.Bignum.Wide in
    output.(i) <- (bi *^ s);
    fscalar_ output b s i
  )


val fscalar:
  output:felem_wide ->
  input:felem{disjoint output input} ->
  s:limb ->
  Stack unit
    (requires (fun h -> live h output /\ live h input))
    (ensures  (fun h0 _ h1 -> live h0 output /\ live h0 input /\ live h1 output /\ modifies_1 output h0 h1
      /\ as_seq h1 output == fscalar_spec (as_seq h0 output) (as_seq h0 input) s len))
let fscalar output b s =
  fscalar_ output b s clen
