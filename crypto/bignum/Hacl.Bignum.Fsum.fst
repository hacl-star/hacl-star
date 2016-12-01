module Hacl.Bignum.Fsum

open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Parameters
open Hacl.Bignum.Bigint
open Hacl.Bignum.Limb


module U32 = FStar.UInt32

val fsum_:
  felem ->
  felem ->
  ctr ->
  Stack unit
    (requires (fun _ -> True))
    (ensures (fun _ _ _ -> true))
let rec fsum_ a b i =
  if U32 (i =^ 0ul) then ()
  else (
    let i = U32 (i -^ 1ul) in
    let ai = a.(i) in let bi = b.(i) in
    a.(i) <- ai +^ bi;
    fsum_ a b i
  )
