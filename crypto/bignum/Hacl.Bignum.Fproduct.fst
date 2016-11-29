module Hacl.Bignum.Fproduct


open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Parameters
open Hacl.Bignum.Bigint
open Hacl.Bignum.Limb
open Hacl.Bignum.Modulo

module U32 = FStar.UInt32

#set-options "--lax"


val shift_:
  output:felem ->
  tmp:limb ->
  ctr:U32.t ->
  Stack unit
    (requires (fun _ -> true))
    (ensures (fun _ _ _ -> true))
let rec shift_ output tmp ctr =
  let open FStar.UInt32 in
  let tmp = if (ctr =^ clen) then output.(0ul) else tmp in
  if (ctr =^ 1ul) then output.(1ul) <- tmp
  else (
    let z = output.(ctr -^ 1ul) in
    output.((ctr %^ clen)) <- z;
    shift_ output tmp (ctr -^ 1ul)
  )


val sum_scalar_multiplication_:
  output:felem_wide ->
  input:felem ->
  s:limb ->
  ctr:U32.t ->
  Stack unit
    (requires (fun _ -> true))
    (ensures (fun _ _ _ -> true))
let rec sum_scalar_multiplication_ output input s ctr =
  if U32 (ctr =^ 0ul) then ()
  else (
    let i = U32 (ctr -^ 1ul) in
    let oi = output.(i) in let ii = input.(i) in
    let open Hacl.Bignum.Wide in
    output.(i) <- (oi +^ (ii *^ s));
    sum_scalar_multiplication_ output input s i
  )


val mul_shift_reduce_:
  output:felem_wide ->
  input:felem ->
  input2:felem ->
  ctr:U32.t ->
  Stack unit
    (requires (fun _ -> true))
    (ensures (fun _ _ _ -> true))
let rec mul_shift_reduce_ output input input2 ctr =
  let open FStar.UInt32 in
  if (ctr =^ 0ul) then ()
  else (
    let i = ctr -^ 1ul in
    let j = clen -^ 1ul -^ i in
    let input2i = input2.(j) in
    sum_scalar_multiplication_ output input input2i clen;
    if (ctr >^ 1ul) then shift_reduce input (ctemplate j);
    mul_shift_reduce_ output input input2 i
  )

val carry_wide_:
  t:felem_wide ->
  ctr:U32.t ->
  Stack unit
    (requires (fun _ -> true))
    (ensures (fun _ _ _ -> true))
let rec carry_wide_ t ctr =
  if U32 (ctr =^ len -^ 1ul) then ()
  else (
    let tctr = t.(ctr) in
    let tctrp1 = t.(U32 (ctr+^1ul)) in
    let r0 = sint128_to_sint64 (tctr) &^ mask_51 in
    let c  = sint128_to_sint64 (H128 (tctr >>^ limb_size)) in
    t.(ctr) <- sint64_to_sint128 r0;
    t.(U32 (ctr +^ 1ul)) <- H128 (tctrp1 +^ sint64_to_sint128 c);
    carry_wide_ t (U32 (ctr +^ 1ul))
  )
