module Hacl.Impl.P256.Field

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.P256.Bignum
open Hacl.Impl.P256.Constants

module S = Spec.P256
module SM = Hacl.Spec.P256.Montgomery

module BD = Hacl.Spec.Bignum.Definitions
module BM = Hacl.Bignum.Montgomery

friend Hacl.Bignum256

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

///  Create zero and one

[@CInline]
let make_fzero n =
  bn_set_zero4 n;
  assert_norm (SM.to_mont 0 = 0);
  SM.lemma_to_from_mont_id 0


[@CInline]
let make_fone n =
  // 0xfffffffeffffffffffffffffffffffff000000000000000000000001
  [@inline_let] let n0 = u64 0x1 in
  [@inline_let] let n1 = u64 0xffffffff00000000 in
  [@inline_let] let n2 = u64 0xffffffffffffffff in
  [@inline_let] let n3 = u64 0xfffffffe in
  assert_norm (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 < S.prime);
  assert_norm (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 == SM.to_mont 1);
  SM.lemma_to_from_mont_id 1;
  bn_make_u64_4 n n0 n1 n2 n3


///  Comparison

[@CInline]
let bn_is_lt_prime_mask4 f =
  let h0 = ST.get () in
  push_frame ();
  let tmp = create_felem () in
  make_prime tmp;
  let c = bn_sub4 tmp f tmp in
  assert (if v c = 0 then as_nat h0 f >= S.prime else as_nat h0 f < S.prime);
  pop_frame ();
  u64 0 -. c


[@CInline]
let feq_mask a b =
  let h0 = ST.get () in
  let r = bn_is_eq_mask4 a b in
  let h1 = ST.get () in
  assert (if as_nat h1 a = as_nat h1 b then v r == ones_v U64 else v r = 0);
  SM.lemma_from_to_mont_id (as_nat h0 a);
  SM.lemma_from_to_mont_id (as_nat h0 b);
  assert (if fmont_as_nat h1 a = fmont_as_nat h1 b then v r == ones_v U64 else v r = 0);
  r


///  Field Arithmetic

[@CInline]
let fadd res x y =
  let h0 = ST.get () in
  push_frame ();
  let n = create_felem () in
  make_prime n;
  bn_add_mod4 res n x y;
  let h1 = ST.get () in
  assert (as_nat h1 res == (as_nat h0 x + as_nat h0 y) % S.prime);
  SM.fmont_add_lemma (as_nat h0 x) (as_nat h0 y);
  pop_frame ()


let fdouble out x =
  fadd out x x


[@CInline]
let fsub res x y =
  let h0 = ST.get () in
  push_frame ();
  let n = create_felem () in
  make_prime n;
  bn_sub_mod4 res n x y;
  let h1 = ST.get () in
  assert (as_nat h1 res == (as_nat h0 x - as_nat h0 y) % S.prime);
  SM.fmont_sub_lemma (as_nat h0 x) (as_nat h0 y);
  pop_frame ()


[@CInline]
let fnegate_conditional_vartime f is_negate =
  push_frame ();
  let zero = create_felem () in
  if is_negate then begin
    let h0 = ST.get () in
    fsub f zero f;
    let h1 = ST.get () in
    assert (as_nat h1 f == (0 - as_nat h0 f) % S.prime);
    Math.Lemmas.modulo_addition_lemma (- as_nat h0 f) S.prime 1;
    assert (as_nat h1 f == (S.prime - as_nat h0 f) % S.prime) end;
  pop_frame ()


val mont_reduction: res:felem -> x:widefelem -> Stack unit
  (requires fun h ->
    live h x /\ live h res /\ disjoint x res /\
    wide_as_nat h x < S.prime * S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res |+| loc x) h0 h1 /\
    as_nat h1 res == wide_as_nat h0 x * SM.fmont_R_inv % S.prime)

[@CInline]
let mont_reduction res x =
  push_frame ();
  let n = create_felem () in
  make_prime n;

  let h0 = ST.get () in
  BM.bn_mont_reduction Hacl.Bignum256.bn_inst n (u64 1) x res;
  SM.bn_mont_reduction_lemma (as_seq h0 x) (as_seq h0 n);
  pop_frame ()


[@CInline]
let fmul res x y =
  push_frame ();
  let tmp = create_widefelem () in
  let h0 = ST.get () in
  bn_mul4 tmp x y;
  let h1 = ST.get () in
  Math.Lemmas.lemma_mult_lt_sqr (as_nat h0 x) (as_nat h0 y) S.prime;
  mont_reduction res tmp;
  SM.fmont_mul_lemma (as_nat h0 x) (as_nat h0 y);
  pop_frame ()


[@CInline]
let fsqr res x =
  push_frame ();
  let tmp = create_widefelem () in
  let h0 = ST.get () in
  bn_sqr4 tmp x;
  let h1 = ST.get () in
  Math.Lemmas.lemma_mult_lt_sqr (as_nat h0 x) (as_nat h0 x) S.prime;
  mont_reduction res tmp;
  SM.fmont_mul_lemma (as_nat h0 x) (as_nat h0 x);
  pop_frame ()


[@CInline]
let from_mont res a =
  push_frame ();
  let tmp = create_widefelem () in
  let h0 = ST.get () in
  update_sub tmp 0ul 4ul a;
  BD.bn_eval_update_sub 4 (as_seq h0 a) 8;
  let h1 = ST.get () in
  assert (wide_as_nat h1 tmp = as_nat h0 a);
  assert_norm (S.prime < S.prime * S.prime);
  mont_reduction res tmp;
  pop_frame ()


[@CInline]
let to_mont res a =
  push_frame ();
  let r2modn = create_felem () in
  make_fmont_R2 r2modn;
  let h0 = ST.get () in
  assert (as_nat h0 r2modn == SM.fmont_R * SM.fmont_R % S.prime);
  fmul res a r2modn;
  let h1 = ST.get () in
  assert (as_nat h1 res ==
    (as_nat h0 a * (SM.fmont_R * SM.fmont_R % S.prime) * SM.fmont_R_inv) % S.prime);
  SM.mul_fmont_R_and_R_inv_is_one ();
  assert (SM.fmont_R_inv * SM.fmont_R % S.prime = 1);
  calc (==) {
    (as_nat h0 a * (SM.fmont_R * SM.fmont_R % S.prime) * SM.fmont_R_inv) % S.prime;
    (==) { Math.Lemmas.swap_mul (as_nat h0 a) (SM.fmont_R * SM.fmont_R % S.prime) }
    ((SM.fmont_R * SM.fmont_R % S.prime) * as_nat h0 a * SM.fmont_R_inv) % S.prime;
    (==) { SM.mont_cancel_lemma_gen S.prime SM.fmont_R SM.fmont_R_inv SM.fmont_R (as_nat h0 a) }
    SM.fmont_R * as_nat h0 a % S.prime;
    (==) { Math.Lemmas.swap_mul SM.fmont_R (as_nat h0 a) }
    as_nat h0 a * SM.fmont_R % S.prime;
    };
  pop_frame ()


///  Special cases of the above functions

[@CInline]
let fmul_by_b_coeff res x =
  push_frame ();
  let b_coeff = create_felem () in
  make_b_coeff b_coeff;
  fmul res b_coeff x;
  pop_frame ()


[@CInline]
let fcube res x =
  fsqr res x;
  fmul res res x
