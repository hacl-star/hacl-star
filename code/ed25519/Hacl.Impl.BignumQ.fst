module Hacl.Impl.BignumQ

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module BD = Hacl.Bignum.Definitions
module BN = Hacl.Bignum
module BM = Hacl.Bignum.Montgomery
module AM = Hacl.Bignum.AlmostMontgomery
module BR = Hacl.Bignum.ModReduction

module SD = Hacl.Spec.Bignum.Definitions
module SN = Hacl.Spec.Bignum
module SM = Hacl.Spec.Bignum.Montgomery

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val lemma_mul_lt: a:nat -> b:nat -> c:nat -> d:nat -> Lemma
  (requires a < c /\ b < d)
  (ensures  a * b < c * d)
let lemma_mul_lt a b c d = ()


val make_q: q:lbuffer uint64 4ul ->
  Stack unit
  (requires fun h -> live h q)
  (ensures  fun h0 _ h1 -> modifies (loc q) h0 h1 /\
    BD.bn_v h1 q == Spec.Ed25519.q)

[@CInline]
let make_q q =
  q.(0ul) <- u64 0x5812631a5cf5d3ed;
  q.(1ul) <- u64 0x14def9dea2f79cd6;
  q.(2ul) <- u64 0x0;
  q.(3ul) <- u64 0x1000000000000000;
  assert_norm (Spec.Ed25519.q == 0x5812631a5cf5d3ed + 0x14def9dea2f79cd6 * pow2 64 + 0x1000000000000000 * pow2 192);
  let h = ST.get () in
  SD.bn_eval_unfold_i (as_seq h q) 4;
  SD.bn_eval_unfold_i (as_seq h q) 3;
  SD.bn_eval_unfold_i (as_seq h q) 2;
  SD.bn_eval_unfold_i (as_seq h q) 1;
  SD.bn_eval0 (as_seq h q)


inline_for_extraction noextract
val make_mu: unit ->
  Stack uint64
  (requires fun h -> True)
  (ensures  fun h0 mu h1 -> modifies0 h0 h1 /\
    (1 + Spec.Ed25519.q * v mu) % pow2 64 == 0)

let make_mu () =
  let mu = u64 0xd2b51da312547e1b in
  assert_norm ((1 + Spec.Ed25519.q * v mu) % pow2 64 = 0);
  mu


val make_r2_modq: r2:lbuffer uint64 4ul ->
  Stack unit
  (requires fun h -> live h r2)
  (ensures  fun h0 _ h1 -> modifies (loc r2) h0 h1 /\
    BD.bn_v h1 r2 == pow2 512 % Spec.Ed25519.q)

[@CInline]
let make_r2_modq r2 =
  r2.(0ul) <- u64 0xa40611e3449c0f01;
  r2.(1ul) <- u64 0xd00e1ba768859347;
  r2.(2ul) <- u64 0xceec73d217f5be65;
  r2.(3ul) <- u64 0x399411b7c309a3d;
  assert_norm (pow2 512 % Spec.Ed25519.q ==
    0xa40611e3449c0f01 + 0xd00e1ba768859347 * pow2 64 +
    0xceec73d217f5be65 * pow2 128 + 0x399411b7c309a3d * pow2 192);
  let h = ST.get () in
  SD.bn_eval_unfold_i (as_seq h r2) 4;
  SD.bn_eval_unfold_i (as_seq h r2) 3;
  SD.bn_eval_unfold_i (as_seq h r2) 2;
  SD.bn_eval_unfold_i (as_seq h r2) 1;
  SD.bn_eval0 (as_seq h r2)


val modq: a:lbuffer uint64 8ul -> res:lbuffer uint64 4ul ->
  Stack unit
  (requires fun h ->
    live h a /\ live h res /\ disjoint a res)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    BD.bn_v h1 res == BD.bn_v h0 a % Spec.Ed25519.q)

[@CInline]
let modq a res =
  push_frame ();
  let q = create 4ul (u64 0) in
  make_q q;
  assert_norm (Spec.Ed25519.q % 2 = 1);
  assert_norm (pow2 252 < Spec.Ed25519.q);

  let mu = make_mu () in
  let r2 = create 4ul (u64 0) in
  make_r2_modq r2;
  BR.bn_mod_slow_precomp (AM.mk_runtime_almost_mont 4ul) q mu r2 a res;
  pop_frame ()


val mul_add_modq:
    a:lbuffer uint64 4ul
  -> b:lbuffer uint64 4ul
  -> c:lbuffer uint64 4ul
  -> res:lbuffer uint64 4ul ->
  Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h c /\ live h res /\
    eq_or_disjoint a b /\
    disjoint res a /\ disjoint res b /\ disjoint res c /\
    BD.bn_v h a < Spec.Ed25519.q /\ BD.bn_v h c < Spec.Ed25519.q)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    BD.bn_v h1 res ==
    (BD.bn_v h0 c + BD.bn_v h0 a * BD.bn_v h0 b) % Spec.Ed25519.q)

[@CInline]
let mul_add_modq a b c res =
  push_frame ();
  let tmp = create 8ul (u64 0) in
  BN.bn_mul 4ul 4ul a b tmp;
  let h0 = ST.get () in
  SN.bn_mul_lemma (as_seq h0 a) (as_seq h0 b);
  //assert (BD.bn_v h0 tmp == BD.bn_v h0 a * BD.bn_v h0 b);
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
  pop_frame ()
