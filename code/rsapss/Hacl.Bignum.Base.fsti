module Hacl.Bignum.Base

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

include Hacl.Spec.Bignum.Base

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"


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
