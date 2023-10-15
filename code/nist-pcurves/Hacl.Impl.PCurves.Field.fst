module Hacl.Impl.PCurves.Field

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.PCurves.Constants
open Hacl.Impl.PCurves.Bignum

module S = Spec.PCurves
module BD = Hacl.Spec.Bignum.Definitions


#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

///  Comparison

let bn_is_lt_prime_mask_g {| cp:S.curve_params |}  {| bn_ops |} {| cc:CC.curve_constants |} f =
  let h0 = ST.get () in
  push_frame ();
  let tmp = create_felem #cp in
  cc.make_prime tmp;
  let c = bn_sub tmp f tmp in
  assert (if v c = 0 then as_nat h0 f >= S.prime else as_nat h0 f < S.prime);
  pop_frame ();
  u64 0 -. c

let feq_mask {| cp:S.curve_params |} {| bn_ops |} a b =
  let h0 = ST.get () in
  let r = bn_is_eq_mask a b in
  let h1 = ST.get () in
  assert (if as_nat h1 a = as_nat h1 b then v r == ones_v U64 else v r = 0);
  SM.lemma_from_to_mont_id (as_nat h0 a);
  SM.lemma_from_to_mont_id (as_nat h0 b);
  assert (if fmont_as_nat h1 a = fmont_as_nat h1 b then v r == ones_v U64 else v r = 0);
  r


///  Field Arithmetic


let fadd_g {| cp:S.curve_params |}  {| bn_ops |} {| cc:CC.curve_constants |} res x y =
  let h0 = ST.get () in
  push_frame ();
  let n = create_felem #cp in
  cc.make_prime n;
  bn_add_mod res n x y;
  let h1 = ST.get () in
  assert (as_nat h1 res == (as_nat h0 x + as_nat h0 y) % S.prime);
  SM.fmont_add_lemma (as_nat h0 x) (as_nat h0 y);
  pop_frame ()


let fsub_g {| cp:S.curve_params |}  {| bn_ops |} {| cc:CC.curve_constants |} res x y =
  let h0 = ST.get () in
  push_frame ();
  let n = create_felem #cp in
  cc.make_prime n;
  bn_sub_mod res n x y;
  let h1 = ST.get () in
  assert (as_nat h1 res == (as_nat h0 x - as_nat h0 y) % S.prime);
  SM.fmont_sub_lemma (as_nat h0 x) (as_nat h0 y);
  pop_frame ()

let fmul_g {| cp:S.curve_params |}  {| bn_ops |} {| cc:CC.curve_constants |} res x y =
  push_frame ();
  let tmp = create_widefelem #cp in
  let h0 = ST.get () in
  bn_mul tmp x y;
  let h1 = ST.get () in
  Math.Lemmas.lemma_mult_lt_sqr (as_nat h0 x) (as_nat h0 y) S.prime;
  cc.fmont_reduction res tmp;
  SM.fmont_mul_lemma (as_nat h0 x) (as_nat h0 y);
  pop_frame ()



let fsqr_g {| cp:S.curve_params |} {| bn_ops |} {| cc:CC.curve_constants |} res x =
  push_frame ();
  let tmp = create_widefelem #cp in
  let h0 = ST.get () in
  bn_sqr tmp x;
  let h1 = ST.get () in
  Math.Lemmas.lemma_mult_lt_sqr (as_nat h0 x) (as_nat h0 x) S.prime;
  cc.fmont_reduction res tmp;
  SM.fmont_mul_lemma (as_nat h0 x) (as_nat h0 x);
  pop_frame ()



let from_mont_g {| cp:S.curve_params |} {| bn_ops |} {| cc:CC.curve_constants |} res a =
  push_frame ();
  let tmp = create_widefelem #cp in
  let h0 = ST.get () in
  update_sub tmp 0ul cp.bn_limbs a;
  BD.bn_eval_update_sub (v cp.bn_limbs) (as_seq h0 a) (2 * v cp.bn_limbs);
  let h1 = ST.get () in
  assert (wide_as_nat h1 tmp = as_nat h0 a);
  assert_norm (S.prime < S.prime * S.prime);
  cc.fmont_reduction res tmp;
  pop_frame ()


let to_mont_g {| cp:S.curve_params |} {| bn_ops |} {| cc:CC.curve_constants |} res a =
  push_frame ();
  let r2modn = create_felem #cp in
  cc.make_fmont_R2 r2modn;
  let h0 = ST.get () in
  assert (as_nat h0 r2modn == SM.fmont_R * SM.fmont_R % S.prime);
  fmul_g res a r2modn;
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


let fnegate_conditional_vartime {| cp:S.curve_params |}  {| bn_ops |} {| CC.curve_constants |} {| op:field_ops |} f is_negate =
  push_frame ();
  let zero = create_felem #cp in
  if is_negate then begin
    let h0 = ST.get () in
    op.fsub f zero f;
    let h1 = ST.get () in
    assert (as_nat h1 f == (0 - as_nat h0 f) % S.prime);
    Math.Lemmas.modulo_addition_lemma (- as_nat h0 f) S.prime 1;
    assert (as_nat h1 f == (S.prime - as_nat h0 f) % S.prime) end;
  pop_frame ()


let fdouble {| cp:S.curve_params |}  {| bn_ops |} {| CC.curve_constants |} {| op:field_ops |} out x =
  op.fadd out x x

let fmul_by_b_coeff {| cp:S.curve_params |}  {| bn_ops |} {| cc:CC.curve_constants |} {| op:field_ops |} res x =
  push_frame ();
  let b_coeff = create_felem #cp in
  cc.make_b_coeff b_coeff;
  op.fmul res b_coeff x;
  pop_frame ()

let fcube {| cp:S.curve_params |}  {| bn_ops |} {| cc:CC.curve_constants |} {| op:field_ops |} res x =
  op.fsqr res x;
  op.fmul res res x
