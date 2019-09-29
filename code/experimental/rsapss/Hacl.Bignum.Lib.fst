module Hacl.Bignum.Lib

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum
open Hacl.Bignum.Base

module S = Spec.RSAPSS

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
val eq_u8: a:uint8 -> b:uint8 -> Tot bool
let eq_u8 a b =
  let open Lib.RawIntTypes in
  FStar.UInt8.(u8_to_UInt8 a =^ u8_to_UInt8 b)


(* check if input[ind] is equal to 1 *)
val bn_is_bit_set:
    len:size_t
  -> input:lbignum len
  -> ind:size_t{v ind / 64 < v len}
  -> Stack bool
    (requires fun h -> live h input)
    (ensures  fun h0 r h1 -> h0 == h1)
[@"c_inline"]
let bn_is_bit_set len input ind =
  let i = ind /. 64ul in
  let j = ind %. 64ul in
  let tmp = input.(i) in
  let tmp = (tmp >>. j) &. u64 1 in
  eq_u64 tmp (u64 1)

val bn_set_bit:
    len:size_t
  -> input:lbignum len
  -> ind:size_t{v ind / 64 < v len}
  -> Stack unit
    (requires fun h -> live h input)
    (ensures  fun h0 _ h1 -> modifies (loc input) h0 h1)
[@"c_inline"]
let bn_set_bit len input ind =
  let i = ind /. 64ul in
  let j = ind %. 64ul in
  let tmp = input.(i) in
  input.(i) <- tmp |. (u64 1 <<. j)
