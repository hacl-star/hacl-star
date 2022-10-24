module Hacl.EC.Ed25519

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module F51 = Hacl.Impl.Ed25519.Field51
module SE = Spec.Ed25519
module SC = Spec.Curve25519
module ML = Hacl.Impl.Ed25519.Ladder

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

[@@ CPrologue
"/*******************************************************************************
  Verified field arithmetic modulo p = 2^255 - 19.

  This is a 64-bit optimized version, where a field element in radix-2^{51} is
  represented as an array of five unsigned 64-bit integers, i.e., uint64_t[5].
*******************************************************************************/\n";

Comment "Write the additive identity in `f`.

  The outparam `f` is meant to be 5 limbs in size, i.e., uint64_t[5]."]
val mk_felem_zero: b:F51.felem ->
  Stack unit
  (requires fun h -> live h b)
  (ensures  fun h0 _ h1 -> modifies (loc b) h0 h1 /\
    F51.mul_inv_t h1 b /\
    F51.fevalh h1 b == SC.zero)

let mk_felem_zero b =
  Hacl.Bignum25519.make_zero b


[@@ Comment "Write the multiplicative identity in `f`.

  The outparam `f` is meant to be 5 limbs in size, i.e., uint64_t[5]."]
val mk_felem_one: b:F51.felem ->
  Stack unit
  (requires fun h -> live h b)
  (ensures  fun h0 _ h1 -> modifies (loc b) h0 h1 /\
    F51.mul_inv_t h1 b /\
    F51.fevalh h1 b == SC.one)

let mk_felem_one b =
  Hacl.Bignum25519.make_one b


[@@ Comment "Write `a + b mod p` in `out`.

  The arguments `a`, `b`, and the outparam `out` are meant to be 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a`, `b`, and `out` are either pairwise disjoint or equal"]
val felem_add: a:F51.felem -> b:F51.felem -> out:F51.felem ->
  Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h out /\
    (disjoint out a \/ out == a) /\
    (disjoint out b \/ out == b) /\
    (disjoint a b \/ a == b) /\
    F51.mul_inv_t h a /\
    F51.mul_inv_t h b)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    F51.mul_inv_t h1 out /\
    F51.fevalh h1 out == SC.fadd (F51.fevalh h0 a) (F51.fevalh h0 b))

let felem_add a b out =
  Hacl.Impl.Curve25519.Field51.fadd out a b;
  Hacl.Bignum25519.reduce_513 out


[@@ Comment "Write `a - b mod p` in `out`.

  The arguments `a`, `b`, and the outparam `out` are meant to be 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a`, `b`, and `out` are either pairwise disjoint or equal"]
val felem_sub: a:F51.felem -> b:F51.felem -> out:F51.felem ->
  Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h out /\
    (disjoint out a \/ out == a) /\
    (disjoint out b \/ out == b) /\
    (disjoint a b \/ a == b) /\
    F51.mul_inv_t h a /\
    F51.mul_inv_t h b)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    F51.mul_inv_t h1 out /\
    F51.fevalh h1 out == SC.fsub (F51.fevalh h0 a) (F51.fevalh h0 b))

let felem_sub a b out =
  Hacl.Impl.Curve25519.Field51.fsub out a b;
  Hacl.Bignum25519.reduce_513 out


[@@ Comment "Write `a * b mod p` in `out`.

  The arguments `a`, `b`, and the outparam `out` are meant to be 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a`, `b`, and `out` are either pairwise disjoint or equal"]
val felem_mul: a:F51.felem -> b:F51.felem -> out:F51.felem ->
  Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h out /\
    F51.mul_inv_t h a /\
    F51.mul_inv_t h b)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    F51.mul_inv_t h1 out /\
    F51.fevalh h1 out == SC.fmul (F51.fevalh h0 a) (F51.fevalh h0 b))

let felem_mul a b out =
  push_frame();
  let tmp = create 10ul (u128 0) in
  Hacl.Impl.Curve25519.Field51.fmul out a b tmp;
  pop_frame()


[@@ Comment "Write `a * a mod p` in `out`.

  The argument `a`, and the outparam `out` are meant to be 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a` and `out` are either disjoint or equal"]
val felem_sqr: a:F51.felem -> out:F51.felem ->
  Stack unit
  (requires fun h ->
    live h a /\ live h out /\
    F51.mul_inv_t h a)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    F51.mul_inv_t h1 out /\
    F51.fevalh h1 out == SC.fmul (F51.fevalh h0 a) (F51.fevalh h0 a))

let felem_sqr a out =
  push_frame();
  let tmp = create 5ul (u128 0) in
  Hacl.Impl.Curve25519.Field51.fsqr out a tmp;
  pop_frame()


[@@ Comment "Write `a ^ (p - 2) mod p` in `out`.

  The function computes modular multiplicative inverse if `a` <> zero.

  The argument `a`, and the outparam `out` are meant to be 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a` and `out` are disjoint"]
val felem_inv: a:F51.felem -> out:F51.felem ->
  Stack unit
  (requires fun h ->
    live h a /\ live h out /\ disjoint a out /\
    F51.mul_inv_t h a)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    F51.mul_inv_t h1 out /\
    F51.fevalh h1 out == SC.fpow (F51.fevalh h0 a) (SC.prime - 2))

let felem_inv a out =
  Hacl.Bignum25519.inverse out a;
  Hacl.Bignum25519.reduce_513 out


[@@ Comment "Load a little-endian field element from memory.

  The argument `b` points to 32 bytes of valid memory, i.e., uint8_t[32].
  The outparam `out` points to a field element of 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `b` and `out` are disjoint

  NOTE that the function also performs the reduction modulo 2^255."]
val felem_load: b:lbuffer uint8 32ul -> out:F51.felem ->
  Stack unit
  (requires fun h -> live h b /\ live h out)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    F51.mul_inv_t h1 out /\
    F51.as_nat h1 out == Lib.ByteSequence.nat_from_bytes_le (as_seq h0 b) % pow2 255)

let felem_load b out =
  Hacl.Bignum25519.load_51 out b


[@@ Comment "Serialize a field element into little-endian memory.

  The argument `a` points to a field element of 5 limbs in size, i.e., uint64_t[5].
  The outparam `out` points to 32 bytes of valid memory, i.e., uint8_t[32].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a` and `out` are disjoint"]
val felem_store: a:F51.felem -> out:lbuffer uint8 32ul ->
  Stack unit
  (requires fun h ->
    live h a /\ live h out /\
    F51.mul_inv_t h a)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_seq h1 out == Lib.ByteSequence.nat_to_bytes_le 32 (F51.fevalh h0 a))

let felem_store a out =
  Hacl.Bignum25519.store_51 out a


[@@ CPrologue
"/*******************************************************************************
  Verified group operations for the edwards25519 elliptic curve of the form
  −x^2 + y^2 = 1 − (121665/121666) * x^2 * y^2.

  This is a 64-bit optimized version, where a group element in extended homogeneous
  coordinates (X, Y, Z, T) is represented as an array of 20 unsigned 64-bit
  integers, i.e., uint64_t[20].
*******************************************************************************/\n";

Comment "Write the point at infinity (additive identity) in `p`.

  The outparam `p` is meant to be 20 limbs in size, i.e., uint64_t[20]."]
val mk_point_at_inf: p:F51.point ->
  Stack unit
  (requires fun h -> live h p)
  (ensures  fun h0 _ h1 -> modifies (loc p) h0 h1 /\
    F51.point_inv_t h1 p /\ F51.inv_ext_point (as_seq h1 p) /\
    SE.to_aff_point (F51.point_eval h1 p) == SE.aff_point_at_infinity)

let mk_point_at_inf p =
  Hacl.Impl.Ed25519.PointConstants.make_point_inf p


[@@ Comment "Write the base point (generator) in `p`.

  The outparam `p` is meant to be 20 limbs in size, i.e., uint64_t[20]."]
val mk_base_point: p:F51.point ->
  Stack unit
  (requires fun h -> live h p)
  (ensures  fun h0 _ h1 -> modifies (loc p) h0 h1 /\
    F51.point_inv_t h1 p /\ F51.inv_ext_point (as_seq h1 p) /\
    SE.to_aff_point (F51.point_eval h1 p) == SE.aff_g)

let mk_base_point p =
  Spec.Ed25519.Lemmas.g_is_on_curve ();
  Hacl.Impl.Ed25519.PointConstants.make_g p


[@@ Comment "Write `-p` in `out` (point negation).

  The argument `p` and the outparam `out` are meant to be 20 limbs in size, i.e., uint64_t[20].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `p` and `out` are disjoint"]
val point_negate: p:F51.point -> out:F51.point ->
  Stack unit
  (requires fun h ->
    live h out /\ live h p /\ disjoint out p /\
    F51.point_inv_t h p /\ F51.inv_ext_point (as_seq h p))
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    F51.point_inv_t h1 out /\ F51.inv_ext_point (as_seq h1 out) /\
    F51.point_eval h1 out == Spec.Ed25519.point_negate (F51.point_eval h0 p))

let point_negate p out =
  let h0 = ST.get () in
  Spec.Ed25519.Lemmas.to_aff_point_negate (F51.refl_ext_point (as_seq h0 p));
  Hacl.Impl.Ed25519.PointNegate.point_negate p out


[@@ Comment "Write `p + q` in `out` (point addition).

  The arguments `p`, `q` and the outparam `out` are meant to be 20 limbs in size, i.e., uint64_t[20].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `p`, `q`, and `out` are either pairwise disjoint or equal"]
val point_add: p:F51.point -> q:F51.point -> out:F51.point ->
  Stack unit
  (requires fun h ->
    live h out /\ live h p /\ live h q /\
    eq_or_disjoint p q /\
    eq_or_disjoint p out /\ eq_or_disjoint q out /\
    F51.point_inv_t h p /\ F51.inv_ext_point (as_seq h p) /\
    F51.point_inv_t h q /\ F51.inv_ext_point (as_seq h q))
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    F51.point_inv_t h1 out /\ F51.inv_ext_point (as_seq h1 out) /\
    F51.point_eval h1 out ==
    SE.point_add (F51.point_eval h0 p) (F51.point_eval h0 q))

let point_add p q out =
  let h0 = ST.get () in
  Spec.Ed25519.Lemmas.to_aff_point_add_lemma
    (F51.refl_ext_point (as_seq h0 p))
    (F51.refl_ext_point (as_seq h0 q));
  Hacl.Impl.Ed25519.PointAdd.point_add out p q


[@@ Comment "Write `p + p` in `out` (point doubling).

  The argument `p` and the outparam `out` are meant to be 20 limbs in size, i.e., uint64_t[20].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `p` and `out` are either pairwise disjoint or equal"]
val point_double: p:F51.point -> out:F51.point ->
  Stack unit
  (requires fun h ->
    live h out /\ live h p /\
    eq_or_disjoint p out /\
    F51.point_inv_t h p /\ F51.inv_ext_point (as_seq h p))
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    F51.point_inv_t h1 out /\ F51.inv_ext_point (as_seq h1 out) /\
    F51.point_eval h1 out == SE.point_double (F51.point_eval h0 p))

let point_double p out =
  let h0 = ST.get () in
  Spec.Ed25519.Lemmas.to_aff_point_double_lemma (F51.refl_ext_point (as_seq h0 p));
  Hacl.Impl.Ed25519.PointDouble.point_double out p


[@@ Comment "Write `[scalar]p` in `out` (point multiplication or scalar multiplication).

  The argument `p` and the outparam `out` are meant to be 20 limbs in size, i.e., uint64_t[20].
  The argument `scalar` is meant to be 32 bytes in size, i.e., uint8_t[32].

  The function first loads a little-endian scalar element from `scalar` and
  then computes a point multiplication.

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `scalar`, `p`, and `out` are pairwise disjoint"]
val point_mul: scalar:lbuffer uint8 32ul -> p:F51.point -> out:F51.point ->
  Stack unit
  (requires fun h ->
    live h scalar /\ live h p /\ live h out /\
    disjoint out p /\ disjoint out scalar /\
    disjoint p scalar /\
    F51.point_inv_t h p /\ F51.inv_ext_point (as_seq h p))
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    F51.point_inv_t h1 out /\ F51.inv_ext_point (as_seq h1 out) /\
    SE.to_aff_point (F51.point_eval h1 out) ==
    SE.to_aff_point (SE.point_mul (as_seq h0 scalar) (F51.point_eval h0 p)))

let point_mul scalar p out =
  Hacl.Impl.Ed25519.Ladder.point_mul out scalar p


[@@ Comment "Checks whether `p` is equal to `q` (point equality).

  The function returns `true` if `p` is equal to `q` and `false` otherwise.

  The arguments `p` and `q` are meant to be 20 limbs in size, i.e., uint64_t[20].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `p` and `q` are either disjoint or equal"]
val point_eq: p:F51.point -> q:F51.point ->
  Stack bool
  (requires fun h ->
    live h p /\ live h q /\ eq_or_disjoint p q /\
    F51.point_inv_t h p /\ F51.point_inv_t h q)
  (ensures  fun h0 z h1 -> modifies0 h0 h1 /\
    (z <==> SE.point_equal (F51.point_eval h0 p) (F51.point_eval h0 q)))

let point_eq p q =
  Hacl.Impl.Ed25519.PointEqual.point_equal p q


[@@ Comment "Compress a point in extended homogeneous coordinates to its compressed form.

  The argument `p` points to a point of 20 limbs in size, i.e., uint64_t[20].
  The outparam `out` points to 32 bytes of valid memory, i.e., uint8_t[32].

  The function first converts a given point `p` from extended homogeneous to affine coordinates
  and then writes [ 2^255 * (`x` % 2) + `y` ] in `out`.

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `p` and `out` are disjoint"]
val point_compress: p:F51.point -> out:lbuffer uint8 32ul ->
  Stack unit
  (requires fun h ->
    live h out /\ live h p /\ disjoint p out /\
    F51.point_inv_t h p)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_seq h1 out == SE.point_compress (F51.point_eval h0 p))

let point_compress p out =
  Hacl.Impl.Ed25519.PointCompress.point_compress out p


[@@ Comment "Decompress a point in extended homogeneous coordinates from its compressed form.

  The function returns `true` for successful decompression of a compressed point
  and `false` otherwise.

  The argument `s` points to 32 bytes of valid memory, i.e., uint8_t[32].
  The outparam `out` points to a point of 20 limbs in size, i.e., uint64_t[20].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `s` and `out` are disjoint"]
val point_decompress: s:lbuffer uint8 32ul -> out:F51.point ->
  Stack bool
  (requires fun h ->
    live h out /\ live h s /\ disjoint s out)
  (ensures  fun h0 b h1 -> modifies (loc out) h0 h1 /\
    (b ==> F51.point_inv_t h1 out /\ F51.inv_ext_point (as_seq h1 out)) /\
    (b <==> Some? (SE.point_decompress (as_seq h0 s))) /\
    (b ==> (F51.point_eval h1 out == Some?.v (SE.point_decompress (as_seq h0 s)))))

let point_decompress s out =
  let h0 = ST.get () in
  Spec.Ed25519.Lemmas.point_decompress_lemma (as_seq h0 s);
  Hacl.Impl.Ed25519.PointDecompress.point_decompress out s
