module Hacl.Bignum.Fscalar

open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Parameters
open Hacl.Bignum.Bigint
open Hacl.Bignum.Limb


module U32 = FStar.UInt32

val fscalar_:
  output:felem_wide ->
  b:felem ->
  s:limb ->
  i:ctr ->
  Stack unit
    (requires (fun h -> true))
    (ensures (fun _ _ _ -> true))
let rec fscalar_ output b s i =
  if U32 (i =^ 0ul) then ()
  else (
    let i = U32 (i -^ 1ul) in
    let bi = b.(i) in
    let open Hacl.Bignum.Wide in
    b.(i) <- (bi *^ s);
    fscalar_ output b s i
  )


val fscalar:
  output:felem_wide ->
  b:felem ->
  s:limb ->
  Stack unit
    (requires (fun h -> true))
    (ensures  (fun h0 _ h1 -> true))
let fscalar output b s =
  fscalar_ output b s clen
