module Hacl.K256.Field

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence
module S = Spec.K256

module BD = Hacl.Bignum.Definitions


#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(**
  This is a naive implementation of field arithmetic for testing purposes
*)

inline_for_extraction noextract
let nlimb = 4ul

inline_for_extraction noextract
let felem = lbuffer uint64 nlimb

noextract
let as_nat (h:mem) (e:felem) : GTot nat = BD.bn_v #U64 #nlimb h e

noextract
let feval (h:mem) (e:felem) : GTot S.felem = as_nat h e % S.prime

noextract
let fe_lt_prime (h:mem) (e:felem) = as_nat h e < S.prime

inline_for_extraction noextract
let felem4 = uint64 & uint64 & uint64 & uint64

noextract
let as_nat4 (f:felem4) =
  let (f0, f1, f2, f3) = f in
  v f0 + v f1 * pow2 64 + v f2 * pow2 128 + v f3 * pow2 192


inline_for_extraction noextract
val make_u64_4 (out:felem) (f:felem4) : Stack unit
  (requires fun h -> live h out)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_nat h1 out == as_nat4 f)


inline_for_extraction noextract
val make_prime_k256: unit -> Pure felem4
  (requires True)
  (ensures  fun r -> as_nat4 r = S.prime)


inline_for_extraction noextract
val make_order_k256: unit -> Pure felem4
  (requires True)
  (ensures  fun r -> as_nat4 r = S.q)


inline_for_extraction noextract
val make_b_k256: unit -> Pure felem4
  (requires True)
  (ensures  fun r -> as_nat4 r = S.b)


inline_for_extraction noextract
val is_felem_zero_vartime (f:felem) : Stack bool
  (requires fun h -> live h f)
  (ensures  fun h0 m h1 -> modifies0 h0 h1 /\
    m == (as_nat h0 f = 0))


inline_for_extraction noextract
val is_felem_eq_vartime (f1 f2:felem) : Stack bool
  (requires fun h ->
    live h f1 /\ live h f2 /\ fe_lt_prime h f1 /\ fe_lt_prime h f2)
  (ensures  fun h0 m h1 -> modifies0 h0 h1 /\
    m == (as_nat h0 f1 = as_nat h0 f2))


inline_for_extraction noextract
val create_felem: unit -> StackInline felem
  (requires fun h -> True)
  (ensures  fun h0 f h1 ->
    stack_allocated f h0 h1 (LSeq.create (v nlimb) (u64 0)) /\
    as_nat h1 f == 0)


inline_for_extraction noextract
val load_felem: f:felem -> b:lbuffer uint8 32ul -> Stack unit
  (requires fun h ->
    live h f /\ live h b /\ disjoint f b /\
    BSeq.nat_from_bytes_be (as_seq h b) < S.prime)
  (ensures  fun h0 _ h1 -> modifies (loc f) h0 h1 /\
    as_nat h1 f == BSeq.nat_from_bytes_be (as_seq h0 b))


inline_for_extraction noextract
val load_felem_vartime: f:felem -> b:lbuffer uint8 32ul -> Stack bool
  (requires fun h ->
    live h f /\ live h b /\ disjoint f b)
  (ensures  fun h0 m h1 -> modifies (loc f) h0 h1 /\
   (let b_nat = BSeq.nat_from_bytes_be (as_seq h0 b) in
    as_nat h1 f == b_nat /\ m = (0 < b_nat && b_nat < S.prime)))


// not used
inline_for_extraction noextract
val store_felem: b:lbuffer uint8 32ul -> f:felem -> Stack unit
  (requires fun h ->
    live h b /\ live h f /\ disjoint f b /\
    fe_lt_prime h f)
  (ensures  fun h0 _ h1 -> modifies (loc b) h0 h1 /\
    as_seq h1 b == BSeq.nat_to_bytes_be 32 (as_nat h0 f))


inline_for_extraction noextract
val set_zero: f:felem -> Stack unit
  (requires fun h -> live h f)
  (ensures  fun h0 _ h1 -> modifies (loc f) h0 h1 /\
    as_nat h1 f == 0)


inline_for_extraction noextract
val set_one: f:felem -> Stack unit
  (requires fun h -> live h f)
  (ensures  fun h0 _ h1 -> modifies (loc f) h0 h1 /\
    as_nat h1 f == 1)


// not used
inline_for_extraction noextract
val copy_felem (f1 f2:felem) : Stack unit
  (requires fun h ->
    live h f1 /\ live h f2 /\ disjoint f1 f2)
  (ensures  fun h0 _ h1 -> modifies (loc f1) h0 h1 /\
    as_seq h1 f1 == as_seq h0 f2)


// num = 3; 2; 8
val fmul_small_num (out f:felem) (num:uint64) : Stack unit
  (requires fun h -> // v num <= 8 is a maximum value for point addition and doubling
    live h f /\ live h out /\ eq_or_disjoint out f /\
    fe_lt_prime h f)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_nat h1 out = S.fmul (v num) (as_nat h0 f) /\
    fe_lt_prime h1 out)


val fmul_3b (out f:felem) : Stack unit
  (requires fun h ->
    live h f /\ live h out /\ eq_or_disjoint out f /\
    fe_lt_prime h f)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_nat h1 out = S.fmul (S.fmul 3 S.b) (as_nat h0 f) /\
    fe_lt_prime h1 out)


val fmul_24b (out f:felem) : Stack unit
  (requires fun h ->
    live h f /\ live h out /\ eq_or_disjoint out f /\
    fe_lt_prime h f)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_nat h1 out = S.fmul (S.fmul 24 S.b) (as_nat h0 f) /\
    fe_lt_prime h1 out)


val add_vartime (out f1 f2:felem) : Stack bool
  (requires fun h ->
    live h out /\ live h f1 /\ live h f2 /\
    eq_or_disjoint out f1 /\ eq_or_disjoint out f2 /\ eq_or_disjoint f1 f2 /\
    fe_lt_prime h f1 /\ fe_lt_prime h f2)
  (ensures  fun h0 b h1 -> modifies (loc out) h0 h1 /\
    as_nat h1 out == (as_nat h0 f1 + as_nat h0 f2) % pow2 256 /\
    b == (as_nat h0 f1 + as_nat h0 f2 < S.prime))


val fadd (out f1 f2:felem) : Stack unit
  (requires fun h ->
    live h out /\ live h f1 /\ live h f2 /\
    eq_or_disjoint out f1 /\ eq_or_disjoint out f2 /\ eq_or_disjoint f1 f2 /\
    fe_lt_prime h f1 /\ fe_lt_prime h f2)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_nat h1 out == S.fadd (as_nat h0 f1) (as_nat h0 f2) /\
    fe_lt_prime h1 out)


val fsub (out f1 f2: felem) : Stack unit
  (requires fun h ->
    live h out /\ live h f1 /\ live h f2 /\
    eq_or_disjoint out f1 /\ eq_or_disjoint out f2 /\ eq_or_disjoint f1 f2 /\
    fe_lt_prime h f1 /\ fe_lt_prime h f2)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_nat h1 out == S.fsub (as_nat h0 f1) (as_nat h0 f2) /\
    fe_lt_prime h1 out)


val fmul (out f1 f2: felem) : Stack unit
  (requires fun h ->
    live h out /\ live h f1 /\ live h f2 /\
    eq_or_disjoint out f1 /\ eq_or_disjoint out f2 /\ eq_or_disjoint f1 f2 /\
    fe_lt_prime h f1 /\ fe_lt_prime h f2)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_nat h1 out == S.fmul (as_nat h0 f1) (as_nat h0 f2) /\
    fe_lt_prime h1 out)


val fsqr (out f: felem) : Stack unit
  (requires fun h ->
    live h out /\ live h f /\ eq_or_disjoint out f /\
    fe_lt_prime h f)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_nat h1 out == S.fmul (as_nat h0 f) (as_nat h0 f) /\
    fe_lt_prime h1 out)


val finv (out f: felem) : Stack unit
  (requires fun h ->
    live h out /\ live h f /\ disjoint out f /\
    fe_lt_prime h f)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_nat h1 out == S.finv (as_nat h0 f)  /\
    fe_lt_prime h1 out)
