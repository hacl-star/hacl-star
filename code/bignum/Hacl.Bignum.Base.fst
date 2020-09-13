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

inline_for_extraction noextract
val addcarry_u64_st: c_in:carry -> a:uint64 -> b:uint64 -> out:lbuffer uint64 1ul ->
  Stack carry
  (requires fun h -> live h out)
  (ensures  fun h0 c_out h1 -> modifies (loc out) h0 h1 /\
    (c_out, LSeq.index (as_seq h1 out) 0) == addcarry_u64 c_in a b)

let addcarry_u64_st c_in a b out =
  Lib.IntTypes.Intrinsics.add_carry_u64 c_in a b out

(**
unsigned char _subborrow_u64 (unsigned char b_in, unsigned __int64 a, unsigned __int64 b, unsigned __int64 * out)

Description
Add unsigned 8-bit borrow b_in (carry flag) to unsigned 64-bit integer b, and subtract the result from
unsigned 64-bit integer a. Store the unsigned 64-bit result in out, and the carry-out in dst (carry or overflow flag).
*)

inline_for_extraction noextract
val subborrow_u64_st: c_in:carry -> a:uint64 -> b:uint64 -> out:lbuffer uint64 1ul ->
  Stack carry
  (requires fun h -> live h out)
  (ensures  fun h0 c_out h1 -> modifies (loc out) h0 h1 /\
    (c_out, LSeq.index (as_seq h1 out) 0) == subborrow_u64 c_in a b)

let subborrow_u64_st c_in a b out =
  Lib.IntTypes.Intrinsics.sub_borrow_u64 c_in a b out


inline_for_extraction noextract
let unsafe_bool_of_u64 (m:uint64{mask_values m}) : b:bool{b <==> v m = v (ones U64 SEC)} =
  if FStar.UInt64.(Lib.RawIntTypes.u64_to_UInt64 m =^ 0uL) then false else true
