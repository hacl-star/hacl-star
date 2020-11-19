module Hacl.Bignum.Base

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Hacl.Bignum.Definitions

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
val addcarry_st: #t:limb_t -> c_in:carry t -> a:limb t -> b:limb t -> out:lbuffer (limb t) 1ul ->
  Stack (carry t)
  (requires fun h -> live h out)
  (ensures  fun h0 c_out h1 -> modifies (loc out) h0 h1 /\
    (c_out, LSeq.index (as_seq h1 out) 0) == addcarry c_in a b)

let addcarry_st #t c_in a b out =
  Lib.IntTypes.Intrinsics.add_carry c_in a b out

(**
unsigned char _subborrow_u64 (unsigned char b_in, unsigned __int64 a, unsigned __int64 b, unsigned __int64 * out)

Description
Add unsigned 8-bit borrow b_in (carry flag) to unsigned 64-bit integer b, and subtract the result from
unsigned 64-bit integer a. Store the unsigned 64-bit result in out, and the carry-out in dst (carry or overflow flag).
*)

inline_for_extraction noextract
val subborrow_st: #t:limb_t -> c_in:carry t -> a:limb t -> b:limb t -> out:lbuffer (limb t) 1ul ->
  Stack (carry t)
  (requires fun h -> live h out)
  (ensures  fun h0 c_out h1 -> modifies (loc out) h0 h1 /\
    (c_out, LSeq.index (as_seq h1 out) 0) == subborrow c_in a b)

let subborrow_st c_in a b out =
  Lib.IntTypes.Intrinsics.sub_borrow c_in a b out


inline_for_extraction noextract
let mul_wide_add_t (t:limb_t) =
    a:limb t
  -> b:limb t
  -> c_in:limb t
  -> out:lbuffer (limb t) 1ul ->
  Stack (limb t)
  (requires fun h -> live h out)
  (ensures  fun h0 c_out h1 -> modifies (loc out) h0 h1 /\
    (c_out, LSeq.index (as_seq h1 out) 0) == mul_wide_add a b c_in)


val mul_wide_add_u32: mul_wide_add_t U32
[@CInline]
let mul_wide_add_u32 a b c_in out =
  lemma_mul_wide_add a b c_in (u32 0);
  let res = to_u64 a *! to_u64 b +! to_u64 c_in in
  out.(0ul) <- to_u32 res;
  to_u32 (res >>. 32ul)


val mul_wide_add_u64: mul_wide_add_t U64
[@CInline]
let mul_wide_add_u64 a b c_in out =
  lemma_mul_wide_add a b c_in (u64 0);
  let res = mul64_wide a b +! to_u128 c_in in
  out.(0ul) <- to_u64 res;
  to_u64 (res >>. 64ul)


inline_for_extraction noextract
val mul_wide_add_st: #t:limb_t -> mul_wide_add_t t
let mul_wide_add_st #t =
  match t with
  | U32 -> mul_wide_add_u32
  | U64 -> mul_wide_add_u64


inline_for_extraction noextract
let mul_wide_add2_t (t:limb_t) =
    a:limb t
  -> b:limb t
  -> c_in:limb t
  -> out:lbuffer (limb t) 1ul ->
  Stack (limb t)
  (requires fun h -> live h out)
  (ensures  fun h0 c_out h1 -> modifies (loc out) h0 h1 /\
    (c_out, LSeq.index (as_seq h1 out) 0) == mul_wide_add2 a b c_in (LSeq.index (as_seq h0 out) 0))


val mul_wide_add2_u32: mul_wide_add2_t U32
[@CInline]
let mul_wide_add2_u32 a b c_in out =
  let h0 = ST.get () in
  lemma_mul_wide_add a b c_in (LSeq.index (as_seq h0 out) 0);
  let res = to_u64 a *! to_u64 b +! to_u64 c_in +! to_u64 out.(0ul) in
  out.(0ul) <- to_u32 res;
  to_u32 (res >>. 32ul)


val mul_wide_add2_u64: mul_wide_add2_t U64
[@CInline]
let mul_wide_add2_u64 a b c_in out =
  let h0 = ST.get () in
  lemma_mul_wide_add a b c_in (LSeq.index (as_seq h0 out) 0);
  let res = mul64_wide a b +! to_u128 c_in +! to_u128 out.(0ul) in
  out.(0ul) <- to_u64 res;
  to_u64 (res >>. 64ul)


inline_for_extraction noextract
val mul_wide_add2_st: #t:limb_t -> mul_wide_add2_t t
let mul_wide_add2_st #t =
  match t with
  | U32 -> mul_wide_add2_u32
  | U64 -> mul_wide_add2_u64
