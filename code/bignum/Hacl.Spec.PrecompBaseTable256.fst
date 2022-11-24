module Hacl.Spec.PrecompBaseTable256

open FStar.Mul
open Lib.IntTypes

module LSeq = Lib.Sequence
module Loops = Lib.LoopCombinators
module LE = Lib.Exponentiation
module SE = Spec.Exponentiation
module BD = Hacl.Spec.Bignum.Definitions

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let lemma_mod_pow2_sub x a b =
  calc (==) {
    x / pow2 a % pow2 b * pow2 a;
    (==) { Math.Lemmas.pow2_modulo_division_lemma_1 x a (a + b) }
    x % pow2 (a + b) / pow2 a * pow2 a;
    (==) { Math.Lemmas.euclidean_division_definition (x % pow2 (a + b)) (pow2 a) }
    x % pow2 (a + b) - x % pow2 (a + b) % pow2 a;
    (==) { Math.Lemmas.pow2_modulo_modulo_lemma_1 x a (a + b) }
    x % pow2 (a + b) - x % pow2 a;
  }


let lemma_decompose_nat256_as_four_u64 x =
  let x0 = x % pow2 64 in
  let x1 = x / pow2 64 % pow2 64 in
  let x2 = x / pow2 128 % pow2 64 in
  let x3' = x / pow2 192 % pow2 64 in
  Math.Lemmas.lemma_div_lt x 256 192;
  Math.Lemmas.small_mod (x / pow2 192) (pow2 64);
  let x3 = x / pow2 192 in
  assert (x3 == x3');
  calc (==) {
    x0 + x1 * pow2 64 + x2 * pow2 128 + x3 * pow2 192;
    (==) { }
    x0 + x1 * pow2 64 + (x / pow2 128 % pow2 64) * pow2 128 + x / pow2 192 * pow2 192;
    (==) { lemma_mod_pow2_sub x 128 64 }
    x0 + x1 * pow2 64 + x % pow2 192 - x % pow2 128 + x / pow2 192 * pow2 192;
    (==) { Math.Lemmas.euclidean_division_definition x (pow2 192) }
    x0 + x1 * pow2 64 - x % pow2 128 + x;
    (==) { lemma_mod_pow2_sub x 64 64 }
    x;
  }


let lemma_decompose_nat256_as_two_nat128 x =
  let x0 = x % pow2 128 in
  let x1' = x / pow2 128 % pow2 128 in
  Math.Lemmas.lemma_div_lt x 256 128;
  Math.Lemmas.small_mod (x / pow2 128) (pow2 128);
  let x1 = x / pow2 128 in
  assert (x1 == x1');
  Math.Lemmas.euclidean_division_definition x (pow2 128)


let lemma_point_mul_base_precomp4 #t k a b =
  let (b0, b1, b2, b3) = decompose_nat256_as_four_u64 b in
  let a_pow2_64 = LE.pow k a (pow2 64) in
  let a_pow2_128 = LE.pow k a (pow2 128) in
  let a_pow2_192 = LE.pow k a (pow2 192) in
  let res = LE.exp_four_fw k a 64 b0 a_pow2_64 b1 a_pow2_128 b2 a_pow2_192 b3 4 in

  calc (==) {
    LE.exp_four_fw k a 64 b0 a_pow2_64 b1 a_pow2_128 b2 a_pow2_192 b3 4;
    (==) { LE.exp_four_fw_lemma k a 64 b0 a_pow2_64 b1 a_pow2_128 b2 a_pow2_192 b3 4 }
    k.LE.mul
      (k.LE.mul
        (k.LE.mul (LE.pow k a b0) (LE.pow k (LE.pow k a (pow2 64)) b1))
        (LE.pow k a_pow2_128 b2))
      (LE.pow k a_pow2_192 b3);
    (==) { LE.lemma_pow_mul k a (pow2 64) b1 }
    k.LE.mul
      (k.LE.mul
        (k.LE.mul (LE.pow k a b0) (LE.pow k a (b1 * pow2 64)))
        (LE.pow k a_pow2_128 b2))
      (LE.pow k a_pow2_192 b3);
    (==) { LE.lemma_pow_add k a b0 (b1 * pow2 64) }
    k.LE.mul
      (k.LE.mul
        (LE.pow k a (b0 + b1 * pow2 64))
        (LE.pow k (LE.pow k a (pow2 128)) b2))
      (LE.pow k a_pow2_192 b3);
    (==) { LE.lemma_pow_mul k a (pow2 128) b2 }
    k.LE.mul
      (k.LE.mul (LE.pow k a (b0 + b1 * pow2 64)) (LE.pow k a (b2 * pow2 128)))
      (LE.pow k a_pow2_192 b3);
    (==) { LE.lemma_pow_add k a (b0 + b1 * pow2 64) (b2 * pow2 128) }
    k.LE.mul
      (LE.pow k a (b0 + b1 * pow2 64 + b2 * pow2 128))
      (LE.pow k (LE.pow k a (pow2 192)) b3);
    (==) { LE.lemma_pow_mul k a (pow2 192) b3 }
    k.LE.mul
      (LE.pow k a (b0 + b1 * pow2 64 + b2 * pow2 128))
      (LE.pow k a (b3 * pow2 192));
    (==) { LE.lemma_pow_add k a (b0 + b1 * pow2 64 + b2 * pow2 128) (b3 * pow2 192) }
    LE.pow k a (b0 + b1 * pow2 64 + b2 * pow2 128 + b3 * pow2 192);
    (==) { lemma_decompose_nat256_as_four_u64 b }
    LE.pow k a b;
  }


let lemma_point_mul_base_precomp2 #t k a b =
  let (b0, b1) = decompose_nat256_as_two_nat128 b in
  let a_pow2_128 = LE.pow k a (pow2 128) in
  calc (==) {
    k.LE.mul (LE.pow k a b0) (LE.pow k a_pow2_128 b1);
    (==) { LE.lemma_pow_mul k a (pow2 128) b1 }
    k.LE.mul (LE.pow k a b0) (LE.pow k a (b1 * pow2 128));
    (==) { LE.lemma_pow_add k a b0 (b1 * pow2 128) }
    LE.pow k a (b0 + b1 * pow2 128);
    (==) { lemma_decompose_nat256_as_two_nat128 b }
    LE.pow k a b;
  }

//-----------------------

#push-options "--fuel 2"
let rec exp_pow2_rec_is_exp_pow2 #t k a b =
  if b = 0 then Lib.LoopCombinators.eq_repeat0 k.sqr a
  else begin
    Lib.LoopCombinators.unfold_repeat b k.sqr a (b - 1);
    assert (Loops.repeat b k.sqr a == k.sqr (Loops.repeat (b - 1) k.sqr a));
    exp_pow2_rec_is_exp_pow2 k a (b - 1) end
#pop-options


let a_pow2_64_lemma #t k a =
  SE.exp_pow2_lemma k a 64;
  LE.exp_pow2_lemma k.SE.to.SE.comm_monoid (k.SE.to.SE.refl a) 64


let a_pow2_128_lemma #t k a =
  let cm = k.SE.to.SE.comm_monoid in
  let refl = k.SE.to.SE.refl in
  calc (==) {
    refl (a_pow2_128 k a);
    (==) { }
    refl (SE.exp_pow2 k (a_pow2_64 k a) 64);
    (==) { a_pow2_64_lemma k (a_pow2_64 k a) }
    LE.pow cm (refl (a_pow2_64 k a)) (pow2 64);
    (==) { a_pow2_64_lemma k a }
    LE.pow cm (LE.pow cm (refl a) (pow2 64)) (pow2 64);
    (==) { LE.lemma_pow_mul cm (refl a) (pow2 64) (pow2 64) }
    LE.pow cm (refl a) (pow2 64 * pow2 64);
    (==) { Math.Lemmas.pow2_plus 64 64 }
    LE.pow cm (refl a) (pow2 128);
  }


let a_pow2_192_lemma #t k a =
  let cm = k.SE.to.SE.comm_monoid in
  let refl = k.SE.to.SE.refl in
  calc (==) {
    refl (a_pow2_192 k a);
    (==) { }
    refl (SE.exp_pow2 k (a_pow2_128 k a) 64);
    (==) { a_pow2_64_lemma k (a_pow2_128 k a) }
    LE.pow cm (refl (a_pow2_128 k a)) (pow2 64);
    (==) { a_pow2_128_lemma k a }
    LE.pow cm (LE.pow cm (refl a) (pow2 128)) (pow2 64);
    (==) { LE.lemma_pow_mul cm (refl a) (pow2 128) (pow2 64) }
    LE.pow cm (refl a) (pow2 128 * pow2 64);
    (==) { Math.Lemmas.pow2_plus 128 64 }
    LE.pow cm (refl a) (pow2 192);
  }


let lemma_decompose_nat256_as_four_u64_lbignum x =
  let open Lib.Sequence in
  let bn_x0 = LSeq.sub x 0 1 in
  let bn_x1 = LSeq.sub x 1 1 in
  let bn_x2 = LSeq.sub x 2 1 in
  let bn_x3 = LSeq.sub x 3 1 in
  assert_norm (pow2 0 = 1);
  BD.bn_eval1 bn_x0;
  BD.bn_eval_index x 0;

  BD.bn_eval1 bn_x1;
  BD.bn_eval_index x 1;

  BD.bn_eval1 bn_x2;
  BD.bn_eval_index x 2;

  BD.bn_eval1 bn_x3;
  BD.bn_eval_index x 3


val bn_eval2: b:BD.lbignum U64 2 ->
  Lemma (BD.bn_v b == v (LSeq.index b 0) + v (LSeq.index b 1) * pow2 64)
let bn_eval2 b =
  BD.bn_eval_unfold_i b 2;
  BD.bn_eval_unfold_i b 1;
  BD.bn_eval0 b


val bn_x0_eval: x:BD.lbignum U64 4 -> Lemma (BD.bn_v (LSeq.sub x 0 2) == BD.bn_v x % pow2 128)
let bn_x0_eval x =
  let open Lib.Sequence in
  let bn_x0 = LSeq.sub x 0 2 in
  assert (v x.[0] == v bn_x0.[0]);
  assert (v x.[1] == v bn_x0.[1]);

  calc (==) {
    BD.bn_v bn_x0;
    (==) { bn_eval2 bn_x0 }
    v bn_x0.[0] + v bn_x0.[1] * pow2 64;
    (==) { BD.bn_eval_index x 0; assert_norm (pow2 0 = 1) }
    BD.bn_v x % pow2 64 + v bn_x0.[1] * pow2 64;
    (==) { BD.bn_eval_index x 1 }
    BD.bn_v x % pow2 64 + (BD.bn_v x / pow2 64 % pow2 64) * pow2 64;
    (==) { lemma_mod_pow2_sub (BD.bn_v x) 64 64 }
    BD.bn_v x % pow2 128;
  }


val bn_x1_eval: x:BD.lbignum U64 4 ->
  Lemma (BD.bn_v (LSeq.sub x 2 2) == BD.bn_v x / pow2 128 % pow2 128)
let bn_x1_eval x =
  let open Lib.Sequence in
  let bn_x1 = LSeq.sub x 2 2 in
  assert (v x.[2] == v bn_x1.[0]);
  assert (v x.[3] == v bn_x1.[1]);

  BD.bn_eval_index x 2;
  BD.bn_eval_index x 3;
  assert (v x.[2] == BD.bn_v x / pow2 128 % pow2 64);
  assert (v x.[3] == BD.bn_v x / pow2 192 % pow2 64);

  bn_eval2 bn_x1;
  let x_div_pow128 = BD.bn_v x / pow2 128 in
  calc (==) { // BD.bn_v bn_x1 ==
    x_div_pow128 % pow2 64 + (BD.bn_v x / pow2 192 % pow2 64) * pow2 64;
    (==) { Math.Lemmas.pow2_plus 128 64;
      Math.Lemmas.division_multiplication_lemma (BD.bn_v x) (pow2 128) (pow2 64) }
    x_div_pow128 % pow2 64 + (x_div_pow128 / pow2 64 % pow2 64) * pow2 64;
    (==) { lemma_mod_pow2_sub x_div_pow128 64 64 }
    x_div_pow128 % pow2 128;
  }


// TODO: make bn_xi_eval generic
let lemma_decompose_nat256_as_two_nat128_lbignum x =
  let open Lib.Sequence in
  let bn_x0 = LSeq.sub x 0 2 in
  let bn_x1 = LSeq.sub x 2 2 in
  BD.bn_eval_split_i x 2;
  assert (BD.bn_v x == BD.bn_v bn_x0 + BD.bn_v bn_x1 * pow2 128);
  bn_x0_eval x;
  bn_x1_eval x;
  Math.Lemmas.euclidean_division_definition (BD.bn_v x) (pow2 128)


let lemma_nat_lt_pow2_128_lbignum x =
  let open Lib.Sequence in
  let bn_x0 = LSeq.sub x 0 2 in
  let bn_x1 = LSeq.sub x 2 2 in
  BD.bn_eval_split_i x 2;
  assert (BD.bn_v x == BD.bn_v bn_x0 + BD.bn_v bn_x1 * pow2 128);
  BD.bn_eval_bound bn_x0 2;
  assert (BD.bn_v x == BD.bn_v bn_x0)
