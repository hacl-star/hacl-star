module Hacl.EC.K256

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module BSeq = Lib.ByteSequence
module LSeq = Lib.Sequence

module S = Spec.K256

module F = Hacl.K256.Field
module Q = Hacl.K256.Scalar
module FI = Hacl.Impl.K256.Finv
module QI = Hacl.Impl.K256.Qinv

module P = Hacl.Impl.K256.Point
module PA = Hacl.Impl.K256.PointAdd
module PD = Hacl.Impl.K256.PointDouble
module PM = Hacl.Impl.K256.PointMul

module BL = Hacl.Spec.K256.Field52.Lemmas

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

[@@ CPrologue
"/*******************************************************************************
  Verified field arithmetic modulo p = 2^256 - 0x1000003D1.

  This is a 64-bit optimized version, where a field element in radix-2^{52} is
  represented as an array of five unsigned 64-bit integers, i.e., uint64_t[5].
*******************************************************************************/\n";

Comment "Write the additive identity in `f`.

  The outparam `f` is meant to be 5 limbs in size, i.e., uint64_t[5]."]
val mk_felem_zero: f:F.felem -> Stack unit
  (requires fun h -> live h f)
  (ensures  fun h0 _ h1 -> modifies (loc f) h0 h1 /\
    F.inv_lazy_reduced2 h1 f /\ F.feval h1 f == S.zero)

let mk_felem_zero f =
  Math.Lemmas.small_mod S.zero S.prime;
  F.set_zero f


[@@ Comment "Write the multiplicative identity in `f`.

  The outparam `f` is meant to be 5 limbs in size, i.e., uint64_t[5]."]
val mk_felem_one: f:F.felem -> Stack unit
  (requires fun h -> live h f)
  (ensures  fun h0 _ h1 -> modifies (loc f) h0 h1 /\
    F.inv_lazy_reduced2 h1 f /\ F.feval h1 f == S.one)

let mk_felem_one f =
  Math.Lemmas.small_mod S.one S.prime;
  F.set_one f


[@@ Comment "Write `a + b mod p` in `out`.

  The arguments `a`, `b`, and the outparam `out` are meant to be 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a`, `b`, and `out` are either pairwise disjoint or equal"]
val felem_add (a b out:F.felem) : Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h out /\
    eq_or_disjoint out a /\ eq_or_disjoint out b /\ eq_or_disjoint a b /\
    F.inv_lazy_reduced2 h a /\ F.inv_lazy_reduced2 h b)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    F.inv_lazy_reduced2 h1 out /\
    F.feval h1 out == S.fadd (F.feval h0 a) (F.feval h0 b))

let felem_add a b out =
  let h0 = ST.get () in
  BL.fadd5_lemma (1,1,1,1,2) (1,1,1,1,2) (F.as_felem5 h0 a) (F.as_felem5 h0 b);
  F.fadd out a b;
  let h1 = ST.get () in
  assert (F.felem_fits5 (F.as_felem5 h1 out) (2,2,2,2,4));
  BL.normalize_weak5_lemma (2,2,2,2,4) (F.as_felem5 h1 out);
  F.fnormalize_weak out out


[@@ Comment "Write `a - b mod p` in `out`.

  The arguments `a`, `b`, and the outparam `out` are meant to be 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a`, `b`, and `out` are either pairwise disjoint or equal"]
val felem_sub (a b out:F.felem) : Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h out /\
    eq_or_disjoint out a /\ eq_or_disjoint out b /\ eq_or_disjoint a b /\
    F.inv_lazy_reduced2 h a /\ F.inv_lazy_reduced2 h b)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    F.inv_lazy_reduced2 h1 out /\
    F.feval h1 out == S.fsub (F.feval h0 a) (F.feval h0 b))

let felem_sub a b out =
  let h0 = ST.get () in
  BL.fsub5_lemma (1,1,1,1,2) (1,1,1,1,2) (F.as_felem5 h0 a) (F.as_felem5 h0 b) (u64 2);
  F.fsub out a b (u64 2);
  let h1 = ST.get () in
  assert (F.felem_fits5 (F.as_felem5 h1 out) (5,5,5,5,6));
  BL.normalize_weak5_lemma (5,5,5,5,6) (F.as_felem5 h1 out);
  F.fnormalize_weak out out


[@@ Comment "Write `a * b mod p` in `out`.

  The arguments `a`, `b`, and the outparam `out` are meant to be 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a`, `b`, and `out` are either pairwise disjoint or equal"]
val felem_mul (a b out:F.felem) : Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h out /\
    eq_or_disjoint out a /\ eq_or_disjoint out b /\ eq_or_disjoint a b /\
    F.inv_lazy_reduced2 h a /\ F.inv_lazy_reduced2 h b)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    F.inv_lazy_reduced2 h1 out /\
    F.feval h1 out == S.fmul (F.feval h0 a) (F.feval h0 b))

let felem_mul a b out =
  F.fmul out a b


[@@ Comment "Write `a * a mod p` in `out`.

  The argument `a`, and the outparam `out` are meant to be 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a` and `out` are either disjoint or equal"]
val felem_sqr (a out:F.felem) : Stack unit
  (requires fun h ->
    live h a /\ live h out /\ eq_or_disjoint out a /\
    F.inv_lazy_reduced2 h a)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    F.inv_lazy_reduced2 h1 out /\
    F.feval h1 out == S.fmul (F.feval h0 a) (F.feval h0 a))

let felem_sqr a out =
  F.fsqr out a


[@@ Comment "Write `a ^ (p - 2) mod p` in `out`.

  The function computes modular multiplicative inverse if `a` <> zero.

  The argument `a`, and the outparam `out` are meant to be 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a` and `out` are disjoint"]
val felem_inv (a out:F.felem) : Stack unit
  (requires fun h ->
    live h a /\ live h out /\ disjoint a out /\
    F.inv_lazy_reduced2 h a)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    F.inv_lazy_reduced2 h1 out /\
    F.feval h1 out == S.finv (F.feval h0 a))

let felem_inv a out =
  FI.finv out a


[@@ Comment "Load a bid-endian field element from memory.

  In addition, the function performs reduction modulo p.

  The argument `b` points to 32 bytes of valid memory, i.e., uint8_t[32].
  The outparam `out` points to a field element of 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `b` and `out` are disjoint"]
val felem_load: b:lbuffer uint8 32ul -> out:F.felem -> Stack unit
  (requires fun h -> live h b /\ live h out /\ disjoint b out)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    F.inv_lazy_reduced2 h1 out /\
    F.feval h1 out == BSeq.nat_from_bytes_be (as_seq h0 b) % S.prime)

let felem_load b out =
  F.load_felem out b


[@@ Comment "Serialize a field element into big-endian memory.

  The argument `a` points to a field element of 5 limbs in size, i.e., uint64_t[5].
  The outparam `out` points to 32 bytes of valid memory, i.e., uint8_t[32].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a` and `out` are disjoint"]
val felem_store: a:F.felem -> out:lbuffer uint8 32ul -> Stack unit
  (requires fun h ->
    live h a /\ live h out /\ disjoint a out /\
    F.inv_lazy_reduced2 h a)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_seq h1 out == BSeq.nat_to_bytes_be 32 (F.feval h0 a))

let felem_store a out =
  push_frame ();
  let tmp = F.create_felem () in
  let h0 = ST.get () in
  BL.normalize5_lemma (1,1,1,1,2) (F.as_felem5 h0 a);
  F.fnormalize tmp a;
  F.store_felem out tmp;
  pop_frame ()


[@@ CPrologue
"/*******************************************************************************
  Verified group operations for the secp256k1 curve of the form y^2 = x^3 + 7.

  This is a 64-bit optimized version, where a group element in projective coordinates
  is represented as an array of 15 unsigned 64-bit integers, i.e., uint64_t[15].
*******************************************************************************/\n";

Comment "Write the point at infinity (additive identity) in `p`.

  The outparam `p` is meant to be 15 limbs in size, i.e., uint64_t[15]."]
val mk_point_at_inf: p:P.point -> Stack unit
  (requires fun h -> live h p)
  (ensures  fun h0 _ h1 -> modifies (loc p) h0 h1 /\
    P.point_inv h1 p /\ P.point_eval h1 p == S.point_at_inf)

let mk_point_at_inf p =
  PM.make_point_at_inf p


[@@ Comment "Write the base point (generator) in `p`.

  The outparam `p` is meant to be 15 limbs in size, i.e., uint64_t[15]."]
val mk_base_point: p:P.point -> Stack unit
  (requires fun h -> live h p)
  (ensures  fun h0 _ h1 -> modifies (loc p) h0 h1 /\
    P.point_inv h1 p /\ P.point_eval h1 p == S.g)

let mk_base_point p =
  PM.make_g p


[@@ Comment "Write `-p` in `out` (point negation).

  The argument `p` and the outparam `out` are meant to be 15 limbs in size, i.e., uint64_t[15].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `p` and `out` are either disjoint or equal"]
val point_negate (p out:P.point) : Stack unit
  (requires fun h ->
    live h out /\ live h p /\ eq_or_disjoint out p /\
    P.point_inv h p)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    P.point_inv h1 out /\
    P.point_eval h1 out == S.point_negate (P.point_eval h0 p))

let point_negate p out =
  P.point_negate out p


[@@ Comment "Write `p + q` in `out` (point addition).

  The arguments `p`, `q` and the outparam `out` are meant to be 15 limbs in size, i.e., uint64_t[15].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `p`, `q`, and `out` are either pairwise disjoint or equal"]
val point_add (p q out:P.point) : Stack unit
  (requires fun h ->
    live h out /\ live h p /\ live h q /\
    eq_or_disjoint p out /\ eq_or_disjoint q out /\ eq_or_disjoint p q /\
    P.point_inv h p /\ P.point_inv h q)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    P.point_inv h1 out /\
    P.point_eval h1 out == S.point_add (P.point_eval h0 p) (P.point_eval h0 q))

let point_add p q out =
  PA.point_add out p q


[@@ Comment "Write `p + p` in `out` (point doubling).

  The argument `p` and the outparam `out` are meant to be 15 limbs in size, i.e., uint64_t[15].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `p` and `out` are either disjoint or equal"]
val point_double (p out:P.point) : Stack unit
  (requires fun h ->
    live h out /\ live h p /\ eq_or_disjoint p out /\
    P.point_inv h p)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    P.point_inv h1 out /\ P.point_eval h1 out == S.point_double (P.point_eval h0 p))

let point_double p out =
  PD.point_double out p


[@@ Comment "Write `[scalar]p` in `out` (point multiplication or scalar multiplication).

  The argument `p` and the outparam `out` are meant to be 15 limbs in size, i.e., uint64_t[15].
  The argument `scalar` is meant to be 32 bytes in size, i.e., uint8_t[32].

  The function first loads a bid-endian scalar element from `scalar` and
  then computes a point multiplication.

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `scalar`, `p`, and `out` are pairwise disjoint"]
val point_mul: scalar:lbuffer uint8 32ul -> p:P.point -> out:P.point -> Stack unit
  (requires fun h ->
    live h scalar /\ live h p /\ live h out /\
    disjoint out p /\ disjoint out scalar /\ disjoint p scalar /\
    P.point_inv h p /\
    BSeq.nat_from_bytes_be (as_seq h scalar) < S.q) // it's still safe to invoke this function with scalar >= S.q
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    P.point_inv h1 out /\
    P.point_eval h1 out == S.point_mul (BSeq.nat_from_bytes_be (as_seq h0 scalar)) (P.point_eval h0 p))

let point_mul scalar p out =
  push_frame ();
  let scalar_q = Q.create_qelem () in
  Q.load_qelem scalar_q scalar;
  PM.point_mul out scalar_q p;
  pop_frame ()


[@@ Comment "Checks whether `p` is equal to `q` (point equality).

  The function returns `true` if `p` is equal to `q` and `false` otherwise.

  The arguments `p` and `q` are meant to be 15 limbs in size, i.e., uint64_t[15].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `p` and `q` are either disjoint or equal"]
val point_eq (p q:P.point) : Stack bool
  (requires fun h ->
    live h p /\ live h q /\ eq_or_disjoint p q /\
    P.point_inv h p /\ P.point_inv h q)
  (ensures  fun h0 z h1 -> modifies0 h0 h1 /\
    (z <==> S.point_equal (P.point_eval h0 p) (P.point_eval h0 q)))

let point_eq p q =
  P.point_eq p q


[@@ Comment "Compress a point in projective coordinates to its compressed form.

  The argument `p` points to a point of 15 limbs in size, i.e., uint64_t[15].
  The outparam `out` points to 33 bytes of valid memory, i.e., uint8_t[33].

  The function first converts a given point `p` from projective to affine coordinates
  and then writes [ 0x02 for even `y` and 0x03 for odd `y`; `x` ] in `out`.

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `p` and `out` are disjoint"]
val point_compress: p:P.point -> out:lbuffer uint8 33ul -> Stack unit
  (requires fun h ->
    live h out /\ live h p /\ disjoint p out /\
    P.point_inv h p)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_seq h1 out == S.point_compress (P.point_eval h0 p))

let point_compress p out =
  P.point_compress_vartime out p


[@@ Comment "Decompress a point in projective coordinates from its compressed form.

  The function returns `true` for successful decompression of a compressed point
  and `false` otherwise.

  The argument `s` points to 33 bytes of valid memory, i.e., uint8_t[33].
  The outparam `out` points to a point of 15 limbs in size, i.e., uint64_t[15].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `s` and `out` are disjoint"]
val point_decompress: s:lbuffer uint8 33ul -> out:P.point -> Stack bool
  (requires fun h ->
    live h out /\ live h s /\ disjoint out s)
  (ensures  fun h0 b h1 -> modifies (loc out) h0 h1 /\
    (b <==> Some? (S.point_decompress (as_seq h0 s))) /\
    (b ==> (P.point_inv h1 out /\ P.point_eval h1 out == Some?.v (S.point_decompress (as_seq h0 s)))))

let point_decompress s out =
  P.point_decompress_vartime out s
