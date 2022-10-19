module Hacl.Impl.BignumQ

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module BSeq = Lib.ByteSequence
module BD = Hacl.Bignum.Definitions
module BN = Hacl.Bignum
module AM = Hacl.Bignum.AlmostMontgomery
module BR = Hacl.Bignum.ModReduction

module SD = Hacl.Spec.Bignum.Definitions
module SN = Hacl.Spec.Bignum

friend Hacl.Bignum256

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
instance km: AM.almost_mont U64 =
  Hacl.Bignum256.almost_mont_inst


inline_for_extraction noextract
val make_u64_4 (out:lbuffer uint64 4ul) (f0 f1 f2 f3:uint64) : Stack unit
  (requires fun h -> live h out)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    BD.bn_v #_ #4ul h1 out == v f0 + v f1 * pow2 64 + v f2 * pow2 128 + v f3 * pow2 192)

let make_u64_4 out f0 f1 f2 f3 =
  out.(0ul) <- f0;
  out.(1ul) <- f1;
  out.(2ul) <- f2;
  out.(3ul) <- f3;
  let h = ST.get () in
  SD.bn_eval_unfold_i (as_seq h out) 4;
  SD.bn_eval_unfold_i (as_seq h out) 3;
  SD.bn_eval_unfold_i (as_seq h out) 2;
  SD.bn_eval_unfold_i (as_seq h out) 1;
  SD.bn_eval0 (as_seq h out)


inline_for_extraction noextract
val make_q: q:lbuffer uint64 4ul -> Stack unit
  (requires fun h -> live h q)
  (ensures  fun h0 _ h1 -> modifies (loc q) h0 h1 /\
    BD.bn_v h1 q == Spec.Ed25519.q)

let make_q q =
  [@inline_let] let (f0, f1, f2, f3) =
   (u64 0x5812631a5cf5d3ed,
    u64 0x14def9dea2f79cd6,
    u64 0x0,
    u64 0x1000000000000000) in

  make_u64_4 q f0 f1 f2 f3;
  assert_norm (Spec.Ed25519.q == v f0 + v f1 * pow2 64 + v f2 * pow2 128 + v f3 * pow2 192)


inline_for_extraction noextract
val make_mu: unit -> mu:uint64{(1 + Spec.Ed25519.q * v mu) % pow2 64 == 0}
let make_mu () =
  [@inline_let] let mu = u64 0xd2b51da312547e1b in
  assert_norm ((1 + Spec.Ed25519.q * v mu) % pow2 64 = 0);
  mu


inline_for_extraction noextract
val make_r2_modq: r2:lbuffer uint64 4ul -> Stack unit
  (requires fun h -> live h r2)
  (ensures  fun h0 _ h1 -> modifies (loc r2) h0 h1 /\
    BD.bn_v h1 r2 == pow2 512 % Spec.Ed25519.q)

let make_r2_modq r2 =
  [@inline_let] let (f0, f1, f2, f3) =
   (u64 0xa40611e3449c0f01,
    u64 0xd00e1ba768859347,
    u64 0xceec73d217f5be65,
    u64 0x399411b7c309a3d) in

  make_u64_4 r2 f0 f1 f2 f3;
  assert_norm (pow2 512 % Spec.Ed25519.q ==
    v f0 + v f1 * pow2 64 + v f2 * pow2 128 + v f3 * pow2 192)


[@CInline]
let modq a res =
  push_frame ();
  let q = create 4ul (u64 0) in
  make_q q;
  assert_norm (Spec.Ed25519.q % 2 = 1);
  assert_norm (pow2 252 < Spec.Ed25519.q);

  [@inline_let] let mu = make_mu () in
  let r2 = create 4ul (u64 0) in
  make_r2_modq r2;
  BR.bn_mod_slow_precomp km q mu r2 a res;
  pop_frame ()


val lemma_mul_lt: a:nat -> b:nat -> c:nat -> d:nat -> Lemma
  (requires a < c /\ b < d)
  (ensures  a * b < c * d)

let lemma_mul_lt a b c d = ()


[@CInline]
let mul_add_modq a b c res =
  push_frame ();
  let tmp = create 8ul (u64 0) in
  // mul4 a b tmp;
  km.AM.bn.BN.mul a b tmp;
  let h0 = ST.get () in
  SN.bn_mul_lemma (as_seq h0 a) (as_seq h0 b);
  assert (BD.bn_v h0 tmp == BD.bn_v h0 a * BD.bn_v h0 b);

  SD.bn_eval_bound (as_seq h0 b) 4;
  lemma_mul_lt (BD.bn_v h0 a) (BD.bn_v h0 b) Spec.Ed25519.q (pow2 256);
  assert_norm (Spec.Ed25519.q + Spec.Ed25519.q * pow2 256 < pow2 512);

  let c1 = BN.bn_add 8ul tmp 4ul c tmp in
  let h1 = ST.get () in
  SN.bn_add_lemma (as_seq h0 tmp) (as_seq h0 c);
  assert (BD.bn_v h1 tmp + v c1 * pow2 512 == BD.bn_v h0 tmp + BD.bn_v h0 c);
  SD.bn_eval_bound (as_seq h1 tmp) 8;
  assert (v c1 = 0);
  modq tmp res;
  Math.Lemmas.lemma_mod_plus_distr_r
    (BD.bn_v h0 c) (BD.bn_v h0 a * BD.bn_v h0 b) Spec.Ed25519.q;
  pop_frame ()


[@CInline]
let gte_q s =
  // TODO: add _vartime version?
  push_frame ();
  let q = create 4ul (u64 0) in
  make_q q;

  let b = BN.bn_lt_mask 4ul s q in
  let h = ST.get () in
  SN.bn_lt_mask_lemma (as_seq h s) (as_seq h q);
  assert (if v b = 0 then BD.bn_v h s >= BD.bn_v h q else BD.bn_v h s < BD.bn_v h q);
  pop_frame ();
  Hacl.Spec.Bignum.Base.unsafe_bool_of_limb0 b


[@CInline]
let load_32_bytes out b =
  let h0 = ST.get () in
  Hacl.Bignum.Convert.mk_bn_from_bytes_le true 32ul b out;
  Hacl.Spec.Bignum.Convert.bn_from_bytes_le_lemma #U64 32 (as_seq h0 b)


[@CInline]
let store_32_bytes out b =
  let h0 = ST.get () in
  Hacl.Bignum.Convert.mk_bn_to_bytes_le true 32ul b out;
  Hacl.Spec.Bignum.Convert.bn_to_bytes_le_lemma 32 (as_seq h0 b)
