module Hacl.K256.Scalar

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
let qelem = lbuffer uint64 nlimb

noextract
let as_nat (h:mem) (e:qelem) : GTot nat = BD.bn_v #U64 #nlimb h e

noextract
let qeval (h:mem) (e:qelem) : GTot S.qelem = as_nat h e % S.q

noextract
let qe_lt_q (h:mem) (e:qelem) = as_nat h e < S.q


inline_for_extraction noextract
val create_qelem: unit -> StackInline qelem
  (requires fun h -> True)
  (ensures  fun h0 f h1 ->
    stack_allocated f h0 h1 (LSeq.create (v nlimb) (u64 0)) /\
    as_nat h1 f == 0)


val load_qelem: f:qelem -> b:lbuffer uint8 32ul -> Stack unit
  (requires fun h ->
    live h f /\ live h b /\ disjoint f b /\
    BSeq.nat_from_bytes_be (as_seq h b) < S.q)
  (ensures  fun h0 _ h1 -> modifies (loc f) h0 h1 /\
    as_nat h1 f == BSeq.nat_from_bytes_be (as_seq h0 b))


val load_felem_modq (out: qelem) (b:lbuffer uint8 32ul) : Stack unit
  (requires fun h ->
    live h out /\ live h b /\ eq_or_disjoint out b)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_nat h1 out == BSeq.nat_from_bytes_be (as_seq h0 b) % S.q /\
    qe_lt_q h1 out)


val store_qelem: b:lbuffer uint8 32ul -> f:qelem -> Stack unit
  (requires fun h ->
    live h b /\ live h f /\ disjoint f b /\
    qe_lt_q h f)
  (ensures  fun h0 _ h1 -> modifies (loc b) h0 h1 /\
    as_seq h1 b == BSeq.nat_to_bytes_be 32 (as_nat h0 f))


inline_for_extraction noextract
val copy_qelem (f1 f2: qelem) : Stack unit
  (requires fun h ->
    live h f1 /\ live h f2 /\ disjoint f1 f2)
  (ensures  fun h0 _ h1 -> modifies (loc f1) h0 h1 /\
    as_seq h1 f1 == as_seq h0 f2)


val qadd (out f1 f2: qelem) : Stack unit
  (requires fun h ->
    live h out /\ live h f1 /\ live h f2 /\
    eq_or_disjoint out f1 /\ eq_or_disjoint out f2 /\ eq_or_disjoint f1 f2 /\
    qe_lt_q h f1 /\ qe_lt_q h f2)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_nat h1 out == S.qadd (as_nat h0 f1) (as_nat h0 f2) /\
    qe_lt_q h1 out)


val qmul (out f1 f2: qelem) : Stack unit
  (requires fun h ->
    live h out /\ live h f1 /\ live h f2 /\
    eq_or_disjoint out f1 /\ eq_or_disjoint out f2 /\ eq_or_disjoint f1 f2 /\
    qe_lt_q h f1 /\ qe_lt_q h f2)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_nat h1 out == S.qmul (as_nat h0 f1) (as_nat h0 f2) /\
    qe_lt_q h1 out)


val qinv (out f: qelem) : Stack unit
  (requires fun h ->
    live h out /\ live h f /\ eq_or_disjoint out f /\
    qe_lt_q h f)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_nat h1 out == S.qinv (as_nat h0 f)  /\
    qe_lt_q h1 out)
