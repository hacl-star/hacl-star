module Hacl.Bignum.Base

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

include Hacl.Spec.Bignum.Base

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"


(**
unsigned char _addcarry_u64 (unsigned char c_in, unsigned __int64 a, unsigned __int64 b, unsigned __int64 * out)

Description
Add unsigned 64-bit integers a and b with unsigned 8-bit carry-in c_in (carry flag),
and store the unsigned 64-bit result in out, and the carry-out in dst (carry or overflow flag).
*)

val addcarry_u64_st: c_in:carry -> a:uint64 -> b:uint64 -> out:lbuffer uint64 1ul ->
  Stack carry
  (requires fun h -> live h out)
  (ensures  fun h0 c_out h1 -> modifies (loc out) h0 h1 /\
    (c_out, LSeq.index (as_seq h1 out) 0) == addcarry_u64 c_in a b)

[@CInline]
let addcarry_u64_st c_in a b out =
  let t1 = a +. c_in in
  let c = if lt_u64 t1 c_in then u64 1 else u64 0 in
  let res = t1 +. b in
  let c = if lt_u64 res t1 then c +. u64 1 else c in
  out.(0ul) <- res;
  c


(**
unsigned char _subborrow_u64 (unsigned char b_in, unsigned __int64 a, unsigned __int64 b, unsigned __int64 * out)

Description
Add unsigned 8-bit borrow b_in (carry flag) to unsigned 64-bit integer b, and subtract the result from
unsigned 64-bit integer a. Store the unsigned 64-bit result in out, and the carry-out in dst (carry or overflow flag).
*)

val subborrow_u64_st: c_in:carry -> a:uint64 -> b:uint64 -> out:lbuffer uint64 1ul ->
  Stack carry
  (requires fun h -> live h out)
  (ensures  fun h0 c_out h1 -> modifies (loc out) h0 h1 /\
    (c_out, LSeq.index (as_seq h1 out) 0) == subborrow_u64 c_in a b)

[@CInline]
let subborrow_u64_st c_in a b out =
  let res = a -. b -. c_in in
  let c =
    if eq_u64 c_in (u64 1) then
      (if le_u64 a b then u64 1 else u64 0)
    else
      (if lt_u64 a b then u64 1 else u64 0) in
  out.(0ul) <- res;
  c


val mul_carry_add_u64_st: c_in:uint64 -> a:uint64 -> b:uint64 -> out:lbuffer uint64 1ul ->
  Stack uint64
  (requires fun h -> live h out)
  (ensures  fun h0 c_out h1 -> modifies (loc out) h0 h1 /\
    (c_out, LSeq.index (as_seq h1 out) 0) == mul_carry_add_u64 a b c_in (LSeq.index (as_seq h0 out) 0))

[@CInline]
let mul_carry_add_u64_st c_in a b out =
  let d = out.(0ul) in
  lemma_mul_carry_add_64 a b c_in d;
  let res = mul64_wide a b +! to_u128 #U64 c_in +! to_u128 #U64 out.(0ul) in
  out.(0ul) <- to_u64 res;
  to_u64 (res >>. 64ul)
