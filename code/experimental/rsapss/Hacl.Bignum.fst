module Hacl.Bignum

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module S = Spec.RSAPSS


#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
val blocks: x:size_t{v x > 0} -> m:size_t{v m > 0} -> r:size_t{v r == S.blocks (v x) (v m)}
let blocks x m =
  (x -. 1ul) /. m +. 1ul


inline_for_extraction noextract
let lbignum len = lbuffer uint64 len

val bn_v: #len:size_t -> h:mem  -> b:lbignum len -> GTot nat
let bn_v #len h b =
  Hacl.Spec.Bignum.bn_v (v len) (as_seq h b)


inline_for_extraction noextract
val bval: len:size_t -> b:lbignum len -> i:size_t ->
  Stack uint64
  (requires fun h -> live h b)
  (ensures  fun h0 _ h1 -> h0 == h1)
let bval len b i =
  if i <. len then b.(i) else u64 0
