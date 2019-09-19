module Hacl.Spec.Bignum

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence


#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

val blocks: x: size_pos -> m: size_pos -> Tot (r:size_pos{x <= m * r})
let blocks x m = (x - 1) / m + 1


let lbignum len = lseq uint64 len

val eval_: len:size_nat -> s:lbignum len -> i:nat{i <= len} -> nat
let rec eval_ len s i =
  if i = 0 then 0
  else eval_ len s (i - 1) + uint_to_nat s.[i - 1] * pow2 (64 * (i - 1))

let bn_v (#len:size_nat) (s:lbignum len) = eval_ len s len

val bval: #len:size_nat -> b:lbignum len -> i:size_nat -> uint64
let bval #len b i = if i < len then b.[i] else u64 0
