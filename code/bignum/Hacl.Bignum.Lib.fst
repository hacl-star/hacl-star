module Hacl.Bignum.Lib

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum.Base
open Hacl.Bignum.Definitions

module S = Hacl.Spec.Bignum.Lib
module ST = FStar.HyperStack.ST
module Loops = Lib.LoopCombinators

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

///
///  Get and set i-th bit of a bignum
///

inline_for_extraction noextract
val bn_is_bit_set:
    len:size_t
  -> b:lbignum len
  -> i:size_t{v i / 64 < v len} ->
  Stack bool
  (requires fun h -> live h b)
  (ensures  fun h0 r h1 -> h0 == h1 /\
    r == S.bn_is_bit_set (as_seq h0 b) (v i))

let bn_is_bit_set len input ind =
  let i = ind /. 64ul in
  let j = ind %. 64ul in
  let tmp = input.(i) in
  let tmp = (tmp >>. j) &. u64 1 in
  FStar.UInt64.(Lib.RawIntTypes.u64_to_UInt64 tmp =^ 1uL)


inline_for_extraction noextract
val bn_bit_set:
    len:size_t
  -> b:lbignum len
  -> i:size_t{v i / 64 < v len} ->
  Stack unit
  (requires fun h -> live h b)
  (ensures  fun h0 _ h1 -> modifies (loc b) h0 h1 /\
    as_seq h1 b == S.bn_bit_set (as_seq h0 b) (v i))

let bn_bit_set len input ind =
  let i = ind /. 64ul in
  let j = ind %. 64ul in
  input.(i) <- input.(i) |. (u64 1 <<. j)
