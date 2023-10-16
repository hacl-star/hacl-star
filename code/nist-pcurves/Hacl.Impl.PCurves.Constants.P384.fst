module Hacl.Impl.PCurves.Constants.P384

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.PCurves.Bignum

module S = Spec.PCurves
module SM = Hacl.Spec.PCurves.Montgomery
module CC = Hacl.Impl.PCurves.Constants


open Spec.P384
open Hacl.Impl.PCurves.Bignum.P384

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"


[@CInline]
val p384_make_prime: n:felem -> Stack unit
  (requires fun h -> live h n)
  (ensures  fun h0 _ h1 -> modifies (loc n) h0 h1 /\
    as_nat h1 n == S.prime)

[@CInline]
let p384_make_prime n =
    // prime = 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff
    [@inline_let] let n0 = u64 0x00000000ffffffff in
    [@inline_let] let n1 = u64 0xffffffff00000000 in
    [@inline_let] let n2 = u64 0xfffffffffffffffe in
    [@inline_let] let n3 = u64 0xffffffffffffffff in
    [@inline_let] let n4 = u64 0xffffffffffffffff in
    [@inline_let] let n5 = u64 0xffffffffffffffff in
    assert_norm (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 + v n3 * pow2 256 + v n3 * pow2 320 = Spec.P384.p384_prime);
    bn_make_u64_6 n n0 n1 n2 n3 n4 n5

[@CInline]
val p384_make_order: n:felem -> Stack unit
  (requires fun h -> live h n)
  (ensures  fun h0 _ h1 -> modifies (loc n) h0 h1 /\
    as_nat h1 n == S.order)

[@CInline]
let p384_make_order n =
    // 0xffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973
    [@inline_let] let n0 = u64 0xecec196accc52973 in
    [@inline_let] let n1 = u64 0x581a0db248b0a77a in
    [@inline_let] let n2 = u64 0xc7634d81f4372ddf in
    [@inline_let] let n3 = u64 0xffffffffffffffff in
    [@inline_let] let n4 = u64 0xffffffffffffffff in
    [@inline_let] let n5 = u64 0xffffffffffffffff in
    assert_norm (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 + v n3 * pow2 256 + v n3 * pow2 320 = Spec.P384.p384_order);
    bn_make_u64_6 n n0 n1 n2 n3 n4 n5

[@CInline]
val p384_make_a_coeff: a:felem -> Stack unit
  (requires fun h -> live h a)
  (ensures fun h0 _ h1 -> modifies (loc a) h0 h1 /\
    as_nat h1 a < S.prime /\
    SM.from_mont (as_nat h1 a) == S.a_coeff)

[@CInline]
let p384_make_a_coeff a =
    // a_coeff      = 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000fffffffc
    // a_coeff_mont = 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffffc00000000 00000003fffffffc
    [@inline_let] let n0 = u64 0x00000003fffffffc in
    [@inline_let] let n1 = u64 0xfffffffc00000000 in
    [@inline_let] let n2 = u64 0xfffffffffffffffb in
    [@inline_let] let n3 = u64 0xffffffffffffffff in
    [@inline_let] let n4 = u64 0xffffffffffffffff in
    [@inline_let] let n5 = u64 0xffffffffffffffff in
    assert_norm (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 + v n4 * pow2 256 + v n5 * pow2 320 < S.prime);
    assert (SM.to_mont #p384_params p384_a_coeff == p384_a_coeff * pow2 (64 * 6) % p384_prime);
    assert_norm (p384_a_coeff * pow2 (64 * 6) % p384_prime == v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 + v n4 * pow2 256 + v n5 * pow2 320);
    SM.lemma_to_from_mont_id S.a_coeff;
    bn_make_u64_6 a n0 n1 n2 n3 n4 n5

[@CInline]
val p384_make_b_coeff: b:felem -> Stack unit
  (requires fun h -> live h b)
  (ensures fun h0 _ h1 -> modifies (loc b) h0 h1 /\
    as_nat h1 b < S.prime /\
    SM.from_mont (as_nat h1 b) == S.b_coeff)

[@CInline]
let p384_make_b_coeff b =
    // b_coeff      =  0xb3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef
    // b_coeff_mont =  0xcd08114b604fbff9b62b21f41f022094e3374bee94938ae277f2209b1920022ef729add87a4c32ec081188719d412dcc
    [@inline_let] let n0 = u64 0x081188719d412dcc in
    [@inline_let] let n1 = u64 0xf729add87a4c32ec in
    [@inline_let] let n2 = u64 0x77f2209b1920022e in
    [@inline_let] let n3 = u64 0xe3374bee94938ae2 in
    [@inline_let] let n4 = u64 0xb62b21f41f022094 in
    [@inline_let] let n5 = u64 0xcd08114b604fbff9 in
    assert_norm (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 + v n4 * pow2 256 + v n5 * pow2 320 < S.prime);
    assert (SM.to_mont #p384_params p384_b_coeff == p384_b_coeff * pow2 (64 * 6) % p384_prime);
    assert_norm (p384_b_coeff * pow2 (64 * 6) % p384_prime == v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 + v n4 * pow2 256 + v n5 * pow2 320);
    SM.lemma_to_from_mont_id S.b_coeff;
    bn_make_u64_6 b n0 n1 n2 n3 n4 n5


[@CInline]
val p384_make_g_x: n:felem -> Stack unit
  (requires fun h -> live h n)
  (ensures  fun h0 _ h1 -> modifies (loc n) h0 h1 /\
    as_nat h1 n < S.prime /\
    SM.from_mont (as_nat h1 n) == S.basepoint_x)

[@CInline]
let p384_make_g_x n =
    // g_x =      0xaa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7
    // mont_g_x = 0x4d3aadc2299e1513812ff723614ede2b6454868459a30eff879c3afc541b4d6e20e378e2a0d6ce383dd0756649c0b528
    [@inline_let] let n0 = u64 0x3dd0756649c0b528 in
    [@inline_let] let n1 = u64 0x20e378e2a0d6ce38 in
    [@inline_let] let n2 = u64 0x879c3afc541b4d6e in
    [@inline_let] let n3 = u64 0x6454868459a30eff in
    [@inline_let] let n4 = u64 0x812ff723614ede2b in
    [@inline_let] let n5 = u64 0x4d3aadc2299e1513 in
    assert_norm (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 + v n4 * pow2 256 + v n5 * pow2 320 < S.prime);
    assert (SM.to_mont #p384_params p384_basepoint_x == p384_basepoint_x * pow2 (64 * 6) % p384_prime);
    assert_norm (p384_basepoint_x * pow2 (64 * 6) % p384_prime == v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 + v n4 * pow2 256 + v n5 * pow2 320);
    SM.lemma_to_from_mont_id S.basepoint_x;
    bn_make_u64_6 n n0 n1 n2 n3 n4 n5

[@CInline]
val p384_make_g_y: n:felem -> Stack unit
  (requires fun h -> live h n)
  (ensures  fun h0 _ h1 -> modifies (loc n) h0 h1 /\
    as_nat h1 n < S.prime /\
    SM.from_mont (as_nat h1 n) == S.basepoint_y)

[@CInline]
let p384_make_g_y n =
    // g_y =      0x3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f
    // mont_g_y = 0x2b78abc25a15c5e9dd8002263969a840c6c3521968f4ffd98bade7562e83b050a1bfa8bf7bb4a9ac23043dad4b03a4fe
    [@inline_let] let n0 = u64 0x23043dad4b03a4fe in
    [@inline_let] let n1 = u64 0xa1bfa8bf7bb4a9ac in
    [@inline_let] let n2 = u64 0x8bade7562e83b050 in
    [@inline_let] let n3 = u64 0xc6c3521968f4ffd9 in
    [@inline_let] let n4 = u64 0xdd8002263969a840 in
    [@inline_let] let n5 = u64 0x2b78abc25a15c5e9 in
    assert_norm (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 + v n4 * pow2 256 + v n5 * pow2 320 < S.prime);
    assert (SM.to_mont #p384_params p384_basepoint_y == p384_basepoint_y * pow2 (64 * 6) % p384_prime);
    assert_norm (p384_basepoint_y * pow2 (64 * 6) % p384_prime == v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 + v n4 * pow2 256 + v n5 * pow2 320);
    SM.lemma_to_from_mont_id S.basepoint_y;
    bn_make_u64_6 n n0 n1 n2 n3 n4 n5

[@CInline]
val p384_make_fmont_R2: n:felem -> Stack unit
  (requires fun h -> live h n)
  (ensures  fun h0 _ h1 -> modifies (loc n) h0 h1 /\
    as_nat h1 n == SM.fmont_R * SM.fmont_R % S.prime)

[@CInline]
let p384_make_fmont_R2 n =
    // 0x0000000000000001 
    [@inline_let] let n0 = u64 0xfffffffe00000001 in
    [@inline_let] let n1 = u64 0x0000000200000000 in
    [@inline_let] let n2 = u64 0xfffffffe00000000 in
    [@inline_let] let n3 = u64 0x0000000200000000 in
    [@inline_let] let n4 = u64 0x0000000000000001 in
    [@inline_let] let n5 = u64 0x0 in
    assert_norm (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 + v n4 * pow2 256 + v n5 * pow2 320 < S.prime);
    assert_norm (pow2 (64 * 6) * pow2 (64 * 6) % p384_prime == v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 + v n4 * pow2 256 + v n5 * pow2 320);
    bn_make_u64_6 n n0 n1 n2 n3 n4 n5

[@CInline]
val p384_make_fzero: n:felem -> Stack unit
  (requires fun h -> live h n)
  (ensures  fun h0 _ h1 -> modifies (loc n) h0 h1 /\
    as_nat h1 n < S.prime /\
    CC.fmont_as_nat h1 n == 0)

[@CInline]
let p384_make_fzero n =
  bn_set_zero n;
  assert_norm (SM.to_mont 0 = 0);
  SM.lemma_to_from_mont_id 0


[@CInline]
val p384_make_fone: n:felem -> Stack unit
  (requires fun h -> live h n)
  (ensures  fun h0 _ h1 -> modifies (loc n) h0 h1 /\
    as_nat h1 n < S.prime /\
    CC.fmont_as_nat h1 n == 1)
[@CInline]
let p384_make_fone n =
  // 0x100000000ffffffffffffffff00000001
    [@inline_let] let n0 = u64 0xffffffff00000001 in
    [@inline_let] let n1 = u64 0x00000000ffffffff in
    [@inline_let] let n2 = u64 0x1 in
    [@inline_let] let n3 = u64 0x0 in
    [@inline_let] let n4 = u64 0x0 in
    [@inline_let] let n5 = u64 0x0 in
    assert_norm (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 + v n4 * pow2 256 + v n5 * pow2 320 < S.prime);
    assert (SM.to_mont #p384_params 1 == pow2 (64 * 6) % p384_prime);
    assert_norm (pow2 (64 * 6) % p384_prime == v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 + v n4 * pow2 256 + v n5 * pow2 320);
    SM.lemma_to_from_mont_id 1;
    bn_make_u64_6 n n0 n1 n2 n3 n4 n5


[@CInline]
val p384_make_qone: f:felem -> Stack unit
  (requires fun h -> live h f)
  (ensures  fun h0 _ h1 -> modifies (loc f) h0 h1 /\
    as_nat h1 f < S.order /\
    CC.qmont_as_nat h1 f == 1)

[@CInline]
let p384_make_qone f =
  // 0x389cb27e0bc8d220a7e5f24db74f58851313e695333ad68d
    [@inline_let] let n0 = u64 0x1313e695333ad68d in
    [@inline_let] let n1 = u64 0xa7e5f24db74f5885 in
    [@inline_let] let n2 = u64 0x389cb27e0bc8d220 in
    [@inline_let] let n3 = u64 0x0 in
    [@inline_let] let n4 = u64 0x0 in
    [@inline_let] let n5 = u64 0x0 in
    assert_norm (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 + v n4 * pow2 256 + v n5 * pow2 320 < S.order);
    assert (SM.to_qmont #p384_params 1 == pow2 (64 * 6) % p384_order);
    assert_norm (pow2 (64 * 6) % p384_order == v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 + v n4 * pow2 256 + v n5 * pow2 320);
    SM.lemma_to_from_qmont_id 1;
    bn_make_u64_6 f n0 n1 n2 n3 n4 n5


[@CInline]
val p384_make_qmont_R2: n:felem -> Stack unit
  (requires fun h -> live h n)
  (ensures  fun h0 _ h1 -> modifies (loc n) h0 h1 /\
    as_nat h1 n == SM.qmont_R * SM.qmont_R % S.order)

[@CInline]
let p384_make_qmont_R2 n =
    // 0xc84ee012b39bf213fb05b7a28266895d40d49174aab1cc5bc3e483afcb82947ff3d81e5df1aa4192d319b2419b409a9
    [@inline_let] let n0 = u64 0x2d319b2419b409a9 in
    [@inline_let] let n1 = u64 0xff3d81e5df1aa419 in
    [@inline_let] let n2 = u64 0xbc3e483afcb82947 in
    [@inline_let] let n3 = u64 0xd40d49174aab1cc5 in
    [@inline_let] let n4 = u64 0x3fb05b7a28266895 in
    [@inline_let] let n5 = u64 0x0c84ee012b39bf21 in
    assert_norm (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 + v n4 * pow2 256 + v n5 * pow2 320 < S.order);
    assert_norm (pow2 (64 * 6) * pow2 (64 * 6) % p384_order == v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 + v n4 * pow2 256 + v n5 * pow2 320);
    bn_make_u64_6 n n0 n1 n2 n3 n4 n5

[@CInline]
val fmont_reduction:
  res:felem -> x:widefelem -> Stack unit
  (requires fun h ->
    live h x /\ live h res /\ disjoint x res /\
    wide_as_nat h x < S.prime * S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res |+| loc x) h0 h1 /\
    as_nat h1 res == wide_as_nat h0 x * SM.fmont_R_inv % S.prime)
let fmont_reduction res x =
  push_frame ();
  let n = create_felem #p384_params in
  p384_make_prime n;
  let h0 = ST.get () in
  bn_mont_reduction p384_mont_mu res x n;
  SM.bn_mont_reduction_lemma (as_seq h0 x) (as_seq h0 n);
  pop_frame ()

[@CInline]
val qmont_reduction:
  res:felem -> x:widefelem -> Stack unit
  (requires fun h ->
    live h x /\ live h res /\ disjoint x res /\
    wide_as_nat h x < S.order * S.order)
  (ensures fun h0 _ h1 -> modifies (loc res |+| loc x) h0 h1 /\
    as_nat h1 res == wide_as_nat h0 x * SM.qmont_R_inv % S.order)
let qmont_reduction res x =
  push_frame ();
  let n = create_felem #p384_params in
  p384_make_order n;
  let h0 = ST.get () in
  bn_mont_reduction p384_mont_q_mu res x n;
  SM.bn_qmont_reduction_lemma (as_seq h0 x) (as_seq h0 n);
  pop_frame ()



inline_for_extraction
instance p384_curve_constants : CC.curve_constants = {
  make_prime = p384_make_prime;
  make_order = p384_make_order;
  make_a_coeff = p384_make_a_coeff;
  make_b_coeff = p384_make_b_coeff;
  make_g_x = p384_make_g_x;
  make_g_y = p384_make_g_y;
  make_fmont_R2 = p384_make_fmont_R2;
  make_qmont_R2 = p384_make_qmont_R2;
  make_fzero = p384_make_fzero;
  make_fone = p384_make_fone;
  make_qone = p384_make_qone;
  fmont_reduction;
  qmont_reduction
}


