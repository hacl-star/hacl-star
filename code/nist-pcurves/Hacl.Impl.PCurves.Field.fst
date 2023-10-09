module Hacl.Impl.PCurves.Field

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.PCurves.Bignum
open Hacl.Impl.PCurves.Constants

module S = Spec.PCurves
module SM = Hacl.Spec.PCurves.Montgomery

module BD = Hacl.Spec.Bignum.Definitions
module BM = Hacl.Bignum.Montgomery


#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

///  Comparison

[@CInline]
let bn_is_lt_prime_mask {| cp:S.curve_params |} {| CC.curve_constants |} f =
  let h0 = ST.get () in
  push_frame ();
  let tmp = create_felem #cp in
  make_prime tmp;
  let c = bn_sub tmp f tmp in
  assert (if v c = 0 then as_nat h0 f >= S.prime else as_nat h0 f < S.prime);
  pop_frame ();
  u64 0 -. c


[@CInline]
let feq_mask {| cp:S.curve_params |} a b =
  let h0 = ST.get () in
  let r = bn_is_eq_mask a b in
  let h1 = ST.get () in
  assert (if as_nat h1 a = as_nat h1 b then v r == ones_v U64 else v r = 0);
  SM.lemma_from_to_mont_id (as_nat h0 a);
  SM.lemma_from_to_mont_id (as_nat h0 b);
  assert (if fmont_as_nat h1 a = fmont_as_nat h1 b then v r == ones_v U64 else v r = 0);
  r


///  Field Arithmetic

[@CInline]
let fadd {| cp:S.curve_params |} {| CC.curve_constants |} res x y =
  let h0 = ST.get () in
  push_frame ();
  let n = create_felem #cp in
  make_prime n;
  bn_add_mod res n x y;
  let h1 = ST.get () in
  assert (as_nat h1 res == (as_nat h0 x + as_nat h0 y) % S.prime);
  SM.fmont_add_lemma (as_nat h0 x) (as_nat h0 y);
  pop_frame ()


let fdouble {| cp:S.curve_params |} {| CC.curve_constants |} out x =
  fadd out x x


[@CInline]
let fsub {| cp:S.curve_params |} {| CC.curve_constants |} res x y =
  let h0 = ST.get () in
  push_frame ();
  let n = create_felem #cp in
  make_prime n;
  bn_sub_mod res n x y;
  let h1 = ST.get () in
  assert (as_nat h1 res == (as_nat h0 x - as_nat h0 y) % S.prime);
  SM.fmont_sub_lemma (as_nat h0 x) (as_nat h0 y);
  pop_frame ()


[@CInline]
let fnegate_conditional_vartime {| cp:S.curve_params |} {| CC.curve_constants |} f is_negate =
  push_frame ();
  let zero = create_felem #cp in
  if is_negate then begin
    let h0 = ST.get () in
    fsub f zero f;
    let h1 = ST.get () in
    assert (as_nat h1 f == (0 - as_nat h0 f) % S.prime);
    Math.Lemmas.modulo_addition_lemma (- as_nat h0 f) S.prime 1;
    assert (as_nat h1 f == (S.prime - as_nat h0 f) % S.prime) end;
  pop_frame ()


val mont_reduction: {| cp:S.curve_params |} -> {| CC.curve_constants |}  
  -> res:felem -> x:widefelem -> Stack unit
  (requires fun h ->
    live h x /\ live h res /\ disjoint x res /\
    wide_as_nat h x < S.prime * S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res |+| loc x) h0 h1 /\
    as_nat h1 res == wide_as_nat h0 x * SM.fmont_R_inv % S.prime)

[@CInline]
let mont_reduction {| cp:S.curve_params |} {| CC.curve_constants |} res x =
  push_frame ();
  let n = create_felem #cp in
  make_prime n;
  let h0 = ST.get () in
  BM.bn_mont_reduction bn_inst n cp.mont_mu x res;
  SM.bn_mont_reduction_lemma (as_seq h0 x) (as_seq h0 n);
  pop_frame ()


[@CInline]
let fmul {| cp:S.curve_params |} {| CC.curve_constants |} res x y =
  push_frame ();
  let tmp = create_widefelem #cp in
  let h0 = ST.get () in
  bn_mul tmp x y;
  let h1 = ST.get () in
  Math.Lemmas.lemma_mult_lt_sqr (as_nat h0 x) (as_nat h0 y) S.prime;
  mont_reduction res tmp;
  SM.fmont_mul_lemma (as_nat h0 x) (as_nat h0 y);
  pop_frame ()


[@CInline]
let fsqr {| cp:S.curve_params |} {| CC.curve_constants |} res x =
  push_frame ();
  let tmp = create_widefelem #cp in
  let h0 = ST.get () in
  bn_sqr tmp x;
  let h1 = ST.get () in
  Math.Lemmas.lemma_mult_lt_sqr (as_nat h0 x) (as_nat h0 x) S.prime;
  mont_reduction res tmp;
  SM.fmont_mul_lemma (as_nat h0 x) (as_nat h0 x);
  pop_frame ()


[@CInline]
let from_mont {| cp:S.curve_params |} {| CC.curve_constants |} res a =
  push_frame ();
  let tmp = create_widefelem #cp in
  let h0 = ST.get () in
  update_sub tmp 0ul cp.bn_limbs a;
  BD.bn_eval_update_sub (v cp.bn_limbs) (as_seq h0 a) (2 * v cp.bn_limbs);
  let h1 = ST.get () in
  assert (wide_as_nat h1 tmp = as_nat h0 a);
  assert_norm (S.prime < S.prime * S.prime);
  mont_reduction res tmp;
  pop_frame ()


[@CInline]
let to_mont {| cp:S.curve_params |} {| CC.curve_constants |} res a =
  push_frame ();
  let r2modn = create_felem #cp in
  make_fmont_R2 r2modn;
  let h0 = ST.get () in
  assert (as_nat h0 r2modn == SM.fmont_R * SM.fmont_R % S.prime);
  fmul res a r2modn;
  let h1 = ST.get () in
  assert (as_nat h1 res ==
    (as_nat h0 a * (SM.fmont_R * SM.fmont_R % S.prime) * SM.fmont_R_inv) % S.prime);
  SM.mul_fmont_R_and_R_inv_is_one #cp;
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
let fmul_by_b_coeff {| cp:S.curve_params |} {| CC.curve_constants |} res x =
  push_frame ();
  let b_coeff = create_felem #cp in
  make_b_coeff b_coeff;
  fmul res b_coeff x;
  pop_frame ()


[@CInline]
let fcube {| cp:S.curve_params |} {| CC.curve_constants |} res x =
  fsqr res x;
  fmul res res x
