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
open Hacl.Bignum.Crecip

module U32 = FStar.UInt32

#set-options "--lax"

val fsum:
  a:felem ->
  b:felem ->
  Stack unit
    (requires (fun _ -> True))
    (ensures (fun _ _ _ -> true))
let fsum a b =
  fsum_ a b clen


val fdifference:
  a:felem ->
  b:felem ->
  Stack unit
    (requires (fun _ -> True))
    (ensures (fun _ _ _ -> true))
let fdifference a b =
  add_zero b;
  fdifference_ a b clen


val fscalar:
  a:felem ->
  b:felem ->
  s:limb ->
  Stack unit
    (requires (fun _ -> True))
    (ensures (fun _ _ _ -> true))
let fscalar output b s =
  push_frame();
  let tmp = create wide_zero clen in
  fscalar tmp b s;
  carry_wide_ tmp 0ul;
  reduce_wide tmp;
  copy_from_wide_ output tmp clen;
  pop_frame()


val fmul:
  output:felem ->
  a:felem ->
  b:felem ->
  Stack unit
    (requires (fun _ -> True))
    (ensures (fun _ _ _ -> true))
let fmul output a b =
  fmul output a b


val fsquare_times:
  output:felem ->
  input:felem ->
  count:ctr ->
  Stack unit
    (requires (fun _ -> True))
    (ensures (fun _ _ _ -> true))
let fsquare_times output input count =
  fsquare_times output input count


val crecip:
  output:felem ->
  input:felem ->
  Stack unit
    (requires (fun _ -> True))
    (ensures (fun _ _ _ -> true))
let crecip output input =
  crecip output input
