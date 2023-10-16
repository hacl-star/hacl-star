module Hacl.Impl.PCurves.Constants.P521

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
module BD = Hacl.Spec.Bignum.Definitions


open Spec.P521
open Hacl.Impl.PCurves.Bignum.P521

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

noextract
val bn_v_is_as_nat9: a:Lib.Sequence.lseq uint64 9 ->
  Lemma (let (s0, s1, s2, s3, s4, s5, s6, s7, s8) =
  Lib.Sequence.(a.[0], a.[1], a.[2], a.[3], a.[4], a.[5], a.[6], a.[7], a.[8]) in
    BD.bn_v a == v s0 + v s1 * pow2 64 + v s2 * pow2 128 +
                 v s3 * pow2 192 + v s4 * pow2 256 + v s5 * pow2 320 +
                 v s6 * pow2 384 + v s7 * pow2 448 + v s8 * pow2 512)

let bn_v_is_as_nat9 a = admit()

inline_for_extraction noextract
val bn_make_u64_9: res:felem -> a0:uint64 -> a1:uint64 -> a2:uint64 -> a3:uint64 ->
                   a4:uint64 -> a5:uint64 -> a6:uint64 -> a7:uint64 -> a8:uint64 -> Stack unit
  (requires fun h -> live h res)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res = v a0 + v a1 * pow2 64 + v a2 * pow2 128 +
                  v a3 * pow2 192 + v a4 * pow2 256 + v a5 * pow2 320 +
                  v a6 * pow2 384 + v a7 * pow2 448 + v a8 * pow2 512)


let bn_make_u64_9 res a0 a1 a2 a3 a4 a5 a6 a7 a8 =
  let h0 = ST.get () in
  upd res 0ul a0;
  let h1 = ST.get () in
  upd res 1ul a1;
  let h2 = ST.get () in
  upd res 2ul a2;
  let h3 = ST.get () in
  upd res 3ul a3;
  let h4 = ST.get () in
  upd res 4ul a4;
  let h5 = ST.get () in
  upd res 5ul a5;
  let h6 = ST.get () in
  upd res 6ul a6;
  let h7 = ST.get () in
  upd res 7ul a7;
  let h8 = ST.get () in
  upd res 8ul a8;
  let h9 = ST.get () in
  BD.bn_upd_eval (as_seq h0 res) a0 0;
  BD.bn_upd_eval (as_seq h1 res) a1 1;
  BD.bn_upd_eval (as_seq h2 res) a2 2;
  BD.bn_upd_eval (as_seq h3 res) a3 3;
  BD.bn_upd_eval (as_seq h4 res) a4 4;
  BD.bn_upd_eval (as_seq h5 res) a5 5;
  BD.bn_upd_eval (as_seq h6 res) a6 6;
  BD.bn_upd_eval (as_seq h7 res) a7 7;
  BD.bn_upd_eval (as_seq h8 res) a8 8;
  bn_v_is_as_nat9 (as_seq h0 res)



[@CInline]
val p521_make_prime: n:felem -> Stack unit
  (requires fun h -> live h n)
  (ensures  fun h0 _ h1 -> modifies (loc n) h0 h1 /\
    as_nat h1 n == S.prime)

[@CInline]
let p521_make_prime n =
    // prime = 0x01ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
    [@inline_let] let n0 = u64 0xffffffffffffffff in
    [@inline_let] let n1 = u64 0xffffffffffffffff in
    [@inline_let] let n2 = u64 0xffffffffffffffff in
    [@inline_let] let n3 = u64 0xffffffffffffffff in
    [@inline_let] let n4 = u64 0xffffffffffffffff in
    [@inline_let] let n5 = u64 0xffffffffffffffff in
    [@inline_let] let n6 = u64 0xffffffffffffffff in
    [@inline_let] let n7 = u64 0xffffffffffffffff in
    [@inline_let] let n8 = u64 0x1ff in
    assert_norm (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 +
                 v n4 * pow2 256 + v n5 * pow2 320 + v n6 * pow2 384 + v n7 * pow2 448 + v n8 * pow2 512 = Spec.P521.p521_prime);
    bn_make_u64_9 n n0 n1 n2 n3 n4 n5 n6 n7 n8

[@CInline]
val p521_make_order: n:felem -> Stack unit
  (requires fun h -> live h n)
  (ensures  fun h0 _ h1 -> modifies (loc n) h0 h1 /\
    as_nat h1 n == S.order)

[@CInline]
let p521_make_order n =
    // 0x01fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa51868783bf2f966b7fcc0148f709a5d03bb5c9b8899c47aebb6fb71e91386409
    [@inline_let] let n0 = u64 0xbb6fb71e91386409 in 
    [@inline_let] let n1 = u64 0x3bb5c9b8899c47ae in
    [@inline_let] let n2 = u64 0x7fcc0148f709a5d0 in
    [@inline_let] let n3 = u64 0x51868783bf2f966b in
    [@inline_let] let n4 = u64 0xfffffffffffffffa in
    [@inline_let] let n5 = u64 0xffffffffffffffff in
    [@inline_let] let n6 = u64 0xffffffffffffffff in
    [@inline_let] let n7 = u64 0xffffffffffffffff in
    [@inline_let] let n8 = u64 0x1ff in
    assert_norm (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 +
                 v n4 * pow2 256 + v n5 * pow2 320 + v n6 * pow2 384 + v n7 * pow2 448 + v n8 * pow2 512
                 = Spec.P521.p521_order);
    bn_make_u64_9 n n0 n1 n2 n3 n4 n5 n6 n7 n8

[@CInline]
val p521_make_a_coeff: a:felem -> Stack unit
  (requires fun h -> live h a)
  (ensures fun h0 _ h1 -> modifies (loc a) h0 h1 /\
    as_nat h1 a < S.prime /\
    SM.from_mont (as_nat h1 a) == S.a_coeff)

[@CInline]
let p521_make_a_coeff a =
    // a_coeff      = 0x01fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc
    // a_coeff_mont = 0x01fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe7fffffffffffff
    [@inline_let] let n0 = u64 0xfe7fffffffffffff in
    [@inline_let] let n1 = u64 0xffffffffffffffff in
    [@inline_let] let n2 = u64 0xffffffffffffffff in
    [@inline_let] let n3 = u64 0xffffffffffffffff in
    [@inline_let] let n4 = u64 0xffffffffffffffff in
    [@inline_let] let n5 = u64 0xffffffffffffffff in
    [@inline_let] let n6 = u64 0xffffffffffffffff in
    [@inline_let] let n7 = u64 0xffffffffffffffff in
    [@inline_let] let n8 = u64 0x01ff in
    assert_norm (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 + v n4 * pow2 256 + v n5 * pow2 320
                 + v n6 * pow2 384 + v n7 * pow2 448 + v n8 * pow2 512 < S.prime);
    assert (SM.to_mont #p521_params p521_a_coeff == p521_a_coeff * pow2 (64 * 9) % p521_prime);
    assert_norm ((p521_a_coeff * pow2 (64 * 9)) % p521_prime = v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 + v n4 * pow2 256 + v n5 * pow2 320 + v n6 * pow2 384 + v n7 * pow2 448 + v n8 * pow2 512); 
    SM.lemma_to_from_mont_id S.a_coeff;
    bn_make_u64_9 a n0 n1 n2 n3 n4 n5 n6 n7 n8

[@CInline]
val p521_make_b_coeff: b:felem -> Stack unit
  (requires fun h -> live h b)
  (ensures fun h0 _ h1 -> modifies (loc b) h0 h1 /\
    as_nat h1 b < S.prime /\
    SM.from_mont (as_nat h1 b) == S.b_coeff)

[@CInline]
let p521_make_b_coeff b =
    // b_coeff      =  0x0051953eb9618e1c9a1f929a21a0b68540eea2da725b99b315f3b8b489918ef109e156193951ec7e937b1652c0bd3bb1bf073573df883d2c34f1ef451fd46b503f00
    // b_coeff_mont =  0x004d0fc94d10d05b42a077516d392dccd98af9dc5a44c8c77884f0ab0c9ca8f63f49bd8b29605e9dd8df839ab9efc41e961a78f7a28fea35a81f8014654fae586387
    [@inline_let] let n0 = u64 0x8014654fae586387 in
    [@inline_let] let n1 = u64 0x78f7a28fea35a81f in
    [@inline_let] let n2 = u64 0x839ab9efc41e961a in
    [@inline_let] let n3 = u64 0xbd8b29605e9dd8df in
    [@inline_let] let n4 = u64 0xf0ab0c9ca8f63f49 in
    [@inline_let] let n5 = u64 0xf9dc5a44c8c77884 in
    [@inline_let] let n6 = u64 0x77516d392dccd98a in
    [@inline_let] let n7 = u64 0x0fc94d10d05b42a0 in
    [@inline_let] let n8 = u64 0x4d in
    assert_norm (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 + v n4 * pow2 256 + v n5 * pow2 320
                 + v n6 * pow2 384 + v n7 * pow2 448 + v n8 * pow2 512 < S.prime);
    assert (SM.to_mont #p521_params p521_b_coeff == p521_b_coeff * pow2 (64 * 9) % p521_prime);
    assert_norm (p521_b_coeff * pow2 (64 * 9) % p521_prime == v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 + v n4 * pow2 256 + v n5 * pow2 320 + v n6 * pow2 384 + v n7 * pow2 448 + v n8 * pow2 512);
    SM.lemma_to_from_mont_id S.b_coeff;
    bn_make_u64_9 b n0 n1 n2 n3 n4 n5 n6 n7 n8


[@CInline]
val p521_make_g_x: n:felem -> Stack unit
  (requires fun h -> live h n)
  (ensures  fun h0 _ h1 -> modifies (loc n) h0 h1 /\
    as_nat h1 n < S.prime /\
    SM.from_mont (as_nat h1 n) == S.basepoint_x)

[@CInline]
let p521_make_g_x n =
    // g_x =      0x00c6858e06b70404e9cd9e3ecb662395b4429c648139053fb521f828af606b4d3dbaa14b5e77efe75928fe1dc127a2ffa8de3348b3c1856a429bf97e7e31c2e5bd66
    // mont_g_x = 0x74e6cf1f65b311cada214e32409c829fda90fc1457b035a69edd50a5af3bf7f3ac947f0ee093d17fd46f19a459e0c2b5214dfcbf3f18e172deb331a16381adc101 
    [@inline_let] let n0 = u64 0xb331a16381adc101 in
    [@inline_let] let n1 = u64 0x4dfcbf3f18e172de in
    [@inline_let] let n2 = u64 0x6f19a459e0c2b521 in
    [@inline_let] let n3 = u64 0x947f0ee093d17fd4 in
    [@inline_let] let n4 = u64 0xdd50a5af3bf7f3ac in
    [@inline_let] let n5 = u64 0x90fc1457b035a69e in
    [@inline_let] let n6 = u64 0x214e32409c829fda in
    [@inline_let] let n7 = u64 0xe6cf1f65b311cada in
    [@inline_let] let n8 = u64 0x74 in
    assert_norm (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 + v n4 * pow2 256 + v n5 * pow2 320
                 + v n6 * pow2 384 + v n7 * pow2 448 + v n8 * pow2 512 < S.prime);
    assert (SM.to_mont #p521_params p521_basepoint_x == p521_basepoint_x * pow2 (64 * 9) % p521_prime);
    assert_norm (p521_basepoint_x * pow2 (64 * 9) % p521_prime == v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 + v n4 * pow2 256 + v n5 * pow2 320 + v n6 * pow2 384 + v n7 * pow2 448 + v n8 * pow2 512);
    SM.lemma_to_from_mont_id S.basepoint_x;
    bn_make_u64_9 n n0 n1 n2 n3 n4 n5 n6 n7 n8

[@CInline]
val p521_make_g_y: n:felem -> Stack unit
  (requires fun h -> live h n)
  (ensures  fun h0 _ h1 -> modifies (loc n) h0 h1 /\
    as_nat h1 n < S.prime /\
    SM.from_mont (as_nat h1 n) == S.basepoint_y)

[@CInline]
let p521_make_g_y n =
    // g_y =      0x011839296a789a3bc0045c8a5fb42c7d1bd998f54449579b446817afbd17273e662c97ee72995ef42640c550b9013fad0761353c7086a272c24088be94769fd16650
    // mont_g_y = 0x1e0022e452fda163e8deccc7aa224abcda2340bd7de8b939f33164bf7394caf7a132062a85c809fd683b09a9e384351396120445f4a3b4fe8b328460e4a5a9e268e
    [@inline_let] let n0 = u64 0x28460e4a5a9e268e in
    [@inline_let] let n1 = u64 0x20445f4a3b4fe8b3 in
    [@inline_let] let n2 = u64 0xb09a9e3843513961 in
    [@inline_let] let n3 = u64 0x2062a85c809fd683 in
    [@inline_let] let n4 = u64 0x164bf7394caf7a13 in
    [@inline_let] let n5 = u64 0x340bd7de8b939f33 in
    [@inline_let] let n6 = u64 0xeccc7aa224abcda2 in
    [@inline_let] let n7 = u64 0x022e452fda163e8d in
    [@inline_let] let n8 = u64 0x1e0 in
    assert_norm (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 + v n4 * pow2 256 + v n5 * pow2 320
                 + v n6 * pow2 384 + v n7 * pow2 448 + v n8 * pow2 512 < S.prime);
    assert (SM.to_mont #p521_params p521_basepoint_y == p521_basepoint_y * pow2 (64 * 9) % p521_prime);
    assert_norm (p521_basepoint_y * pow2 (64 * 9) % p521_prime == v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 + v n4 * pow2 256 + v n5 * pow2 320 + v n6 * pow2 384 + v n7 * pow2 448 + v n8 * pow2 512);
    SM.lemma_to_from_mont_id S.basepoint_y;
    bn_make_u64_9 n n0 n1 n2 n3 n4 n5 n6 n7 n8

    
[@CInline]
val p521_make_fmont_R2: n:felem -> Stack unit
  (requires fun h -> live h n)
  (ensures  fun h0 _ h1 -> modifies (loc n) h0 h1 /\
    as_nat h1 n == SM.fmont_R * SM.fmont_R % S.prime)

[@CInline]
let p521_make_fmont_R2 n =
    // 0x400000000000 0000000000000000
    [@inline_let] let n0 = u64 0x0 in
    [@inline_let] let n1 = u64 0x400000000000 in
    [@inline_let] let n2 = u64 0x0 in
    [@inline_let] let n3 = u64 0x0 in
    [@inline_let] let n4 = u64 0x0 in
    [@inline_let] let n5 = u64 0x0 in
    [@inline_let] let n6 = u64 0x0 in
    [@inline_let] let n7 = u64 0x0 in
    [@inline_let] let n8 = u64 0x0 in
    assert_norm (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 + v n4 * pow2 256 + v n5 * pow2 320
                 + v n6 * pow2 384 + v n7 * pow2 448 + v n8 * pow2 512 < S.prime);
    assert_norm (pow2 (64 * 9) * pow2 (64 * 9) % p521_prime == v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 + v n4 * pow2 256 + v n5 * pow2 320 + v n6 * pow2 384 + v n7 * pow2 448 + v n8 * pow2 512);
    bn_make_u64_9 n n0 n1 n2 n3 n4 n5 n6 n7 n8

[@CInline]
val p521_make_fzero: n:felem -> Stack unit
  (requires fun h -> live h n)
  (ensures  fun h0 _ h1 -> modifies (loc n) h0 h1 /\
    as_nat h1 n < S.prime /\
    CC.fmont_as_nat h1 n == 0)

[@CInline]
let p521_make_fzero n =
  bn_set_zero n;
  assert_norm (SM.to_mont 0 = 0);
  SM.lemma_to_from_mont_id 0


[@CInline]
val p521_make_fone: n:felem -> Stack unit
  (requires fun h -> live h n)
  (ensures  fun h0 _ h1 -> modifies (loc n) h0 h1 /\
    as_nat h1 n < S.prime /\
    CC.fmont_as_nat h1 n == 1)
[@CInline]
let p521_make_fone n =
  // 0x80000000000000
    [@inline_let] let n0 = u64 0x80000000000000 in
    [@inline_let] let n1 = u64 0x0 in
    [@inline_let] let n2 = u64 0x0 in
    [@inline_let] let n3 = u64 0x0 in
    [@inline_let] let n4 = u64 0x0 in
    [@inline_let] let n5 = u64 0x0 in
    [@inline_let] let n6 = u64 0x0 in
    [@inline_let] let n7 = u64 0x0 in
    [@inline_let] let n8 = u64 0x0 in
    assert_norm (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 + v n4 * pow2 256 + v n5 * pow2 320
                 + v n6 * pow2 384 + v n7 * pow2 448 + v n8 * pow2 512 < S.prime);
    assert (SM.to_mont #p521_params 1 == pow2 (64 * 9) % p521_prime);
    assert_norm (pow2 (64 * 9) % p521_prime == v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 + v n4 * pow2 256 + v n5 * pow2 320 + v n6 * pow2 384 + v n7 * pow2 448 + v n8 * pow2 512);
    SM.lemma_to_from_mont_id 1;
    bn_make_u64_9 n n0 n1 n2 n3 n4 n5 n6 n7 n8


[@CInline]
val p521_make_qone: f:felem -> Stack unit
  (requires fun h -> live h f)
  (ensures  fun h0 _ h1 -> modifies (loc f) h0 h1 /\
    as_nat h1 f < S.order /\
    CC.qmont_as_nat h1 f == 1)

[@CInline]
let p521_make_qone f =
  // 0x2d73cbc3e206834ca4019ff5b847b2d17e2251b23bb31dc28a2482470b763cdfb80000000000000
    [@inline_let] let n0 = u64 0xfb80000000000000 in
    [@inline_let] let n1 = u64 0x28a2482470b763cd in
    [@inline_let] let n2 = u64 0x17e2251b23bb31dc in
    [@inline_let] let n3 = u64 0xca4019ff5b847b2d in
    [@inline_let] let n4 = u64 0x2d73cbc3e206834  in
    [@inline_let] let n5 = u64 0x0 in
    [@inline_let] let n6 = u64 0x0 in
    [@inline_let] let n7 = u64 0x0 in
    [@inline_let] let n8 = u64 0x0 in
    assert_norm (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 + v n4 * pow2 256 + v n5 * pow2 320
                 + v n6 * pow2 384 + v n7 * pow2 448 + v n8 * pow2 512 < S.order);
    assert (SM.to_qmont #p521_params 1 == pow2 (64 * 9) % p521_order);
    assert_norm (pow2 (64 * 9) % p521_order == v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 + v n4 * pow2 256 + v n5 * pow2 320 + v n6 * pow2 384 + v n7 * pow2 448 + v n8 * pow2 512);
    SM.lemma_to_from_qmont_id 1;
    bn_make_u64_9 f n0 n1 n2 n3 n4 n5 n6 n7 n8

[@CInline]
val p521_make_qmont_R2: n:felem -> Stack unit
  (requires fun h -> live h n)
  (ensures  fun h0 _ h1 -> modifies (loc n) h0 h1 /\
    as_nat h1 n == SM.qmont_R * SM.qmont_R % S.order)

[@CInline]
let p521_make_qmont_R2 n =
    // 0x3d2d8e03d1492d0d455bcc6d61a8e567bccff3d142b7756e3edd6e23d82e49c7dbd3721ef557f75e0612a78d38794573fff707badce5547ea3137cd04dcf15dd04
    [@inline_let] let n0 = u64 0x137cd04dcf15dd04 in
    [@inline_let] let n1 = u64 0xf707badce5547ea3 in
    [@inline_let] let n2 = u64 0x12a78d38794573ff in
    [@inline_let] let n3 = u64 0xd3721ef557f75e06 in
    [@inline_let] let n4 = u64 0xdd6e23d82e49c7db in
    [@inline_let] let n5 = u64 0xcff3d142b7756e3e in
    [@inline_let] let n6 = u64 0x5bcc6d61a8e567bc in
    [@inline_let] let n7 = u64 0x2d8e03d1492d0d45 in
    [@inline_let] let n8 = u64 0x3d in
    assert_norm (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 + v n4 * pow2 256 + v n5 * pow2 320
                 + v n6 * pow2 384 + v n7 * pow2 448 + v n8 * pow2 512 < S.order);
    assert_norm (pow2 (64 * 9) * pow2 (64 * 9) % p521_order == v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 + v n4 * pow2 256 + v n5 * pow2 320 + v n6 * pow2 384 + v n7 * pow2 448 + v n8 * pow2 512);
    bn_make_u64_9 n n0 n1 n2 n3 n4 n5 n6 n7 n8

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
  let n = create_felem #p521_params in
  p521_make_prime n;
  let h0 = ST.get () in
  bn_mont_reduction p521_mont_mu res x n;
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
  let n = create_felem #p521_params in
  p521_make_order n;
  let h0 = ST.get () in
  bn_mont_reduction p521_mont_q_mu res x n;
  SM.bn_qmont_reduction_lemma (as_seq h0 x) (as_seq h0 n);
  pop_frame ()



inline_for_extraction
instance p521_curve_constants : CC.curve_constants = {
  make_prime = p521_make_prime;
  make_order = p521_make_order;
  make_a_coeff = p521_make_a_coeff;
  make_b_coeff = p521_make_b_coeff;
  make_g_x = p521_make_g_x;
  make_g_y = p521_make_g_y;
  make_fmont_R2 = p521_make_fmont_R2;
  make_qmont_R2 = p521_make_qmont_R2;
  make_fzero = p521_make_fzero;
  make_fone = p521_make_fone;
  make_qone = p521_make_qone;
  fmont_reduction;
  qmont_reduction
}


