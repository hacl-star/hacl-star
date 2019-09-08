module Hacl.Impl.Lib

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.RawIntTypes

module S = Spec.RSAPSS

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
let lbignum len = lbuffer uint64 len

inline_for_extraction noextract
val blocks:
    x:size_t{v x > 0}
  -> m:size_t{v m > 0}
  -> r:size_t{v r == S.blocks (v x) (v m)}
let blocks x m =
  (x -. 1ul) /. m +. 1ul

inline_for_extraction noextract
val eq_u64: a:uint64 -> b:uint64 -> Tot bool
let eq_u64 a b = FStar.UInt64.(u64_to_UInt64 a =^ u64_to_UInt64 b)

inline_for_extraction noextract
val lt_u64: a:uint64 -> b:uint64 -> Tot bool
let lt_u64 a b = FStar.UInt64.(u64_to_UInt64 a <^ u64_to_UInt64 b)

inline_for_extraction noextract
val le_u64: a:uint64 -> b:uint64 -> Tot bool
let le_u64 a b = FStar.UInt64.(u64_to_UInt64 a <=^ u64_to_UInt64 b)

inline_for_extraction noextract
val eq_u8: a:uint8 -> b:uint8 -> Tot (r:bool{r == (uint_to_nat a = uint_to_nat b)})
let eq_u8 a b = FStar.UInt8.(u8_to_UInt8 a =^ u8_to_UInt8 b)

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

inline_for_extraction noextract
val bval:
    len:size_t
  -> b:lbignum len
  -> i:size_t
  -> Stack uint64
    (requires fun h -> live h b)
    (ensures  fun h0 _ h1 -> h0 == h1)
let bval len b i =
  if i <. len then b.(i) else u64 0
