module Hacl.Spec.Bignum.Base

open FStar.Mul
open Lib.IntTypes

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let carry = x:uint64{uint_v x == 0 \/ uint_v x == 1}

inline_for_extraction noextract
val eq_u64: a:uint64 -> b:uint64 -> Tot bool
let eq_u64 a b =
  let open Lib.RawIntTypes in
  FStar.UInt64.(u64_to_UInt64 a =^ u64_to_UInt64 b)

inline_for_extraction noextract
val lt_u64: a:uint64 -> b:uint64 -> Tot bool
let lt_u64 a b =
  let open Lib.RawIntTypes in
  FStar.UInt64.(u64_to_UInt64 a <^ u64_to_UInt64 b)

inline_for_extraction noextract
val le_u64: a:uint64 -> b:uint64 -> Tot bool
let le_u64 a b =
  let open Lib.RawIntTypes in
  FStar.UInt64.(u64_to_UInt64 a <=^ u64_to_UInt64 b)


inline_for_extraction noextract
val addcarry_u64: c:carry -> a:uint64 -> b:uint64 ->
  Pure (carry & uint64)
  (requires True)
  (ensures  fun (c', r) ->
    uint_v r + uint_v c' * pow2 64 == uint_v a + uint_v b + uint_v c)

let addcarry_u64 c a b =
  let t1 = a +. c in
  let c = if lt_u64 t1 c then u64 1 else u64 0 in
  let res = t1 +. b in
  let c = if lt_u64 res t1 then c +. u64 1 else c in
  c, res


inline_for_extraction noextract
val subborrow_u64: c:carry -> a:uint64 -> b:uint64 ->
  Pure (carry & uint64)
  (requires True)
  (ensures  fun (c', r) ->
    uint_v r - uint_v c' * pow2 64 == uint_v a - uint_v b - uint_v c)

let subborrow_u64 c a b =
  let res = a -. b -. c in
  let c =
    if eq_u64 c (u64 1) then
      (if le_u64 a b then u64 1 else u64 0)
    else
      (if lt_u64 a b then u64 1 else u64 0) in
  c, res
