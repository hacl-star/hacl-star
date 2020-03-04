module Hacl.Bignum.Definitions

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module S = Hacl.Spec.Bignum.Definitions

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
val blocks: x:size_t{v x > 0} -> m:size_t{v m > 0} -> r:size_t{v r == S.blocks (v x) (v m)}
let blocks x m = (x -. 1ul) /. m +. 1ul

inline_for_extraction noextract
let lbignum len = lbuffer uint64 len

val bn_v: #len:size_t -> h:mem  -> b:lbignum len -> GTot nat
let bn_v #len h b = S.bn_v #(v len) (as_seq h b)
