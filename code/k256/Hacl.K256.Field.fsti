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

include Hacl.Spec.K256.Field52.Definitions
module BI = Hacl.Spec.K256.Field52

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(** Specialized bignum library with a radix-2^{52} *)

inline_for_extraction noextract
let nlimb = 5ul

inline_for_extraction noextract
let felem = lbuffer uint64 nlimb

noextract
let as_felem5 (h:mem) (e:felem) : GTot felem5 =
  let open Lib.Sequence in
  let s = as_seq h e in
  (s.[0], s.[1], s.[2], s.[3], s.[4])

noextract
let as_nat (h:mem) (e:felem) : GTot nat =
  as_nat5 (as_felem5 h e)

noextract
let feval (h:mem) (e:felem) : GTot S.felem = as_nat h e % S.prime

noextract
let inv_fully_reduced5 (f:felem5) =
  felem_fits5 f (1,1,1,1,1) /\
  as_nat5 f < S.prime

noextract
let inv_fully_reduced (h:mem) (e:felem) =
  let f = as_felem5 h e in
  inv_fully_reduced5 f


noextract
let inv_lazy_reduced1_5 (f:felem5) =
  felem_fits5 f (1,1,1,1,1)

noextract
let inv_lazy_reduced1 (h:mem) (e:felem) =
  let f = as_felem5 h e in
  inv_lazy_reduced1_5 f


noextract
let inv_fe_is_fe5 (h:mem) (e:felem) (f:felem5) =
  let (f0,f1,f2,f3,f4) = f in
  let (e0,e1,e2,e3,e4) = as_felem5 h e in
  f0 == e0 /\ f1 == e1 /\ f2 == e2 /\ f3 == e3 /\ f4 == e4


noextract
let as_felem4 (h:mem) (e:lbuffer uint64 4ul) : GTot felem4 =
  let open Lib.Sequence in
  let s = as_seq h e in
  (s.[3], s.[2], s.[1], s.[0])


inline_for_extraction noextract
val make_u64_4 (out:lbuffer uint64 4ul) (f:felem4) : Stack unit
  (requires fun h -> live h out)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_felem4 h1 out == f)


inline_for_extraction noextract
val make_u52_5 (out:felem) (f:felem5) : Stack unit
  (requires fun h -> live h out)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_nat h1 out == as_nat5 f /\ inv_fe_is_fe5 h1 out f)


inline_for_extraction noextract
val make_prime_k256: unit -> Pure felem5
  (requires True)
  (ensures  fun r ->
    as_nat5 r = S.prime /\ inv_lazy_reduced1_5 r)


inline_for_extraction noextract
val make_order_k256: unit -> Pure felem5
  (requires True)
  (ensures  fun r ->
    as_nat5 r = S.q /\ inv_fully_reduced5 r)


inline_for_extraction noextract
val make_b_k256: unit -> Pure felem5
  (requires True)
  (ensures  fun r ->
    as_nat5 r = S.b /\ inv_fully_reduced5 r)


val is_felem_zero_vartime (f:felem) : Stack bool
  (requires fun h -> live h f /\ inv_fully_reduced h f )
  (ensures  fun h0 m h1 -> modifies0 h0 h1 /\
    m == (as_nat h0 f = 0))


val is_felem_eq_vartime (f1 f2:felem) : Stack bool
  (requires fun h ->
    live h f1 /\ live h f2 /\
    inv_fully_reduced h f1 /\ inv_fully_reduced h f2)
  (ensures  fun h0 m h1 -> modifies0 h0 h1 /\
    m == (as_nat h0 f1 = as_nat h0 f2))


// needed for ecdsa-verify when q < p < 2q
val is_felem_lt_prime_minus_order_vartime (f:felem) : Stack bool
  (requires fun h -> live h f /\ inv_fully_reduced h f)
  (ensures  fun h0 m h1 -> modifies0 h0 h1 /\
    m == (as_nat h0 f < S.prime - S.q))


inline_for_extraction noextract
val create_felem: unit -> StackInline felem
  (requires fun h -> True)
  (ensures  fun h0 f h1 ->
    stack_allocated f h0 h1 (LSeq.create (v nlimb) (u64 0)) /\
    as_nat h1 f == 0 /\ inv_fully_reduced h1 f)


//BSeq.nat_from_bytes_be (as_seq h b) < S.prime
val load_felem: f:felem -> b:lbuffer uint8 32ul -> Stack unit
  (requires fun h ->
    live h f /\ live h b /\ disjoint f b)
  (ensures  fun h0 _ h1 -> modifies (loc f) h0 h1 /\
    as_nat h1 f == BSeq.nat_from_bytes_be (as_seq h0 b) /\
    inv_lazy_reduced1 h1 f)


val load_felem_vartime: f:felem -> b:lbuffer uint8 32ul -> Stack bool
  (requires fun h ->
    live h f /\ live h b /\ disjoint f b)
  (ensures  fun h0 m h1 -> modifies (loc f) h0 h1 /\
   (let b_nat = BSeq.nat_from_bytes_be (as_seq h0 b) in
    as_nat h1 f == b_nat /\ m = (0 < b_nat && b_nat < S.prime) /\
    inv_lazy_reduced1 h1 f))


val store_felem: b:lbuffer uint8 32ul -> f:felem -> Stack unit
  (requires fun h ->
    live h b /\ live h f /\ disjoint f b /\
    inv_fully_reduced h f)
  (ensures  fun h0 _ h1 -> modifies (loc b) h0 h1 /\
    as_seq h1 b == BSeq.nat_to_bytes_be 32 (as_nat h0 f))


inline_for_extraction noextract
val set_zero: f:felem -> Stack unit
  (requires fun h -> live h f)
  (ensures  fun h0 _ h1 -> modifies (loc f) h0 h1 /\
    as_nat h1 f == 0 /\ inv_fully_reduced h1 f)


inline_for_extraction noextract
val set_one: f:felem -> Stack unit
  (requires fun h -> live h f)
  (ensures  fun h0 _ h1 -> modifies (loc f) h0 h1 /\
    as_nat h1 f == 1 /\ inv_fully_reduced h1 f)


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
    live h f /\ live h out /\ eq_or_disjoint out f)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    inv_fe_is_fe5 h1 out (BI.mul15 (as_felem5 h0 f) num))


val fadd (out f1 f2:felem) : Stack unit
  (requires fun h ->
    live h out /\ live h f1 /\ live h f2 /\
    eq_or_disjoint out f1 /\ eq_or_disjoint out f2 /\ eq_or_disjoint f1 f2)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    inv_fe_is_fe5 h1 out (BI.add5 (as_felem5 h0 f1) (as_felem5 h0 f2)))


val fsub (out f1 f2: felem) (x:uint64) : Stack unit
  (requires fun h ->
    live h out /\ live h f1 /\ live h f2 /\
    eq_or_disjoint out f1 /\ eq_or_disjoint out f2 /\ eq_or_disjoint f1 f2)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    inv_fe_is_fe5 h1 out (BI.fsub5 (as_felem5 h0 f1) (as_felem5 h0 f2) x))


val fmul (out f1 f2: felem) : Stack unit
  (requires fun h ->
    live h out /\ live h f1 /\ live h f2 /\
    eq_or_disjoint out f1 /\ eq_or_disjoint out f2 /\ eq_or_disjoint f1 f2)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    inv_fe_is_fe5 h1 out (BI.fmul5 (as_felem5 h0 f1) (as_felem5 h0 f2)))


val fsqr (out f: felem) : Stack unit
  (requires fun h ->
    live h out /\ live h f /\ eq_or_disjoint out f)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    inv_fe_is_fe5 h1 out (BI.fsqr5 (as_felem5 h0 f)))
