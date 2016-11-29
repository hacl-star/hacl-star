module Hacl.Bignum


open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Parameters
open Hacl.Bignum.Bigint
open Hacl.Bignum.Limb
open Hacl.Bignum.Modulo
open Hacl.Bignum.Fscalar
open Hacl.Bignum.Fsum
open Hacl.Bignum.Fdifference
open Hacl.Bignum.Fproduct

module U32 = FStar.UInt32
module Wide = Hacl.Bignum.Wide


#set-options "--lax"


val fmul:
  output:felem ->
  input:felem ->
  input2:felem ->
  Stack unit
    (requires (fun _ -> true))
    (ensures (fun _ _ _ -> true))
let fmul output input input2 =
  push_frame();
  let tmp = create Wide.zero len in
  let t   = create Wide.zero len in
  blit input 0ul tmp 0ul len;
  mul_shift_reduce_ t tmp input2 len;
  carry_wide_ t 0ul;
  let tnm1 = t.(U32 (len -^ 1ul)) in
  let t0   = t.(0ul) in  
  let c = sint128_to_sint64 (Wide (tnm1 >>^ limb_size)) in
  t.(U32 (len -^ 1ul)) <- Wide (tnm1 &^ sint64_to_sint128 mask_51);
  t.(0ul) <- Wide (t0 +^ (c *^ nineteen));
  copy_from_wide_ output t len;
  let output0 = output.(0ul) in
  let output1 = output.(1ul) in
  let c = output0 >>^ limb_size in
  output.(0ul) <- output0 &^ mask_51;
  output.(1ul) <- output1 +^ c;
  pop_frame()

(*

val fsquare_times_:
  input:felem ->
  count:U32.t ->
  Stack unit
    (requires (fun _ -> true))
    (ensures (fun _ _ _ -> true))
let rec fsquare_times_ tmp count =
  if U32 (count =^ 0ul) then ()
  else (
    fmul tmp tmp tmp;
    fsquare_times_ tmp (U32 (count -^ 1ul))
  )


val fsquare_times:
  output:felem ->
  input:felem ->
  count:U32.t ->
  Stack unit
    (requires (fun _ -> true))
    (ensures (fun _ _ _ -> true))
let fsquare_times output input count =
  push_frame();
  let tmp = create zero_64 len in
  blit input 0ul tmp 0ul len;
  fsquare_times_ tmp count;
  blit tmp 0ul output 0ul len;
  pop_frame()
