module Hacl.Spec.K256.GLV.Lemmas

open FStar.Mul

module M = Lib.NatMod
module LE = Lib.Exponentiation
module SE = Spec.Exponentiation

module S = Spec.K256
module LS = Spec.K256.Lemmas
module SM = Hacl.Spec.K256.ECSM.Lemmas

open Hacl.Spec.K256.GLV

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

// [lambda](px, py) = (beta * px, py)
assume
val lemma_glv_aff : p:S.aff_point -> Lemma (aff_point_mul lambda p == aff_point_mul_lambda p)

val lemma_glv : p:S.proj_point ->
  Lemma (S.to_aff_point (point_mul_lambda p) == aff_point_mul lambda (S.to_aff_point p))

let lemma_glv p =
  let (pX, pY, pZ) = p in
  let (px, py) = S.to_aff_point p in
  assert (px = S.(pX /% pZ) /\ py = S.(pY /% pZ));
  let (qx, qy) = aff_point_mul lambda (px, py) in
  lemma_glv_aff (px, py);
  assert (qx = S.(beta *% px) /\ qy = py);
  assert (qx = S.(beta *% (pX /% pZ)) /\ qy = S.(pY /% pZ));

  let (rX, rY, rZ) = point_mul_lambda p in
  assert (rX = S.(beta *% pX) /\ rY = pY /\ rZ = pZ);
  let (rx, ry) = S.to_aff_point (rX, rY, rZ) in
  assert (rx = S.(rX /% rZ) /\ ry = S.(rY /% rZ));
  assert (rx = S.(beta *% pX /% pZ) /\ ry = S.(pY /% pZ));
  assert (qy = ry);
  // S.(beta *% pX /% rZ) = S.(beta *% (pX /% pZ))
  assert (S.(beta *% pX /% pZ) = S.(beta *% pX *% S.finv pZ));
  assert (S.(beta *% (pX /% pZ)) = S.(beta *% (pX *% S.finv pZ)));
  M.lemma_mul_mod_assoc #S.prime beta pX (S.finv pZ);
  assert (S.(beta *% pX *% S.finv pZ) = S.(beta *% (pX *% S.finv pZ)))

//--------------------------------------------

val lemma_scalar_split_lambda_eval (k:S.qelem) :
  Lemma (let r1, r2 = scalar_split_lambda k in k == S.(r1 +^ r2 *^ lambda))

let lemma_scalar_split_lambda_eval k =
  assert_norm ((minus_lambda + lambda) % S.q = 0);

  let r1, r2 = scalar_split_lambda k in
  assert (r1 = S.(k +^ r2 *^ minus_lambda));
  calc (==) {
    (r1 + (r2 * lambda % S.q)) % S.q;
    (==) { Math.Lemmas.lemma_mod_plus_distr_r r1 (r2 * lambda) S.q }
    (r1 + r2 * lambda) % S.q;
    (==) { }
    ((k + (r2 * minus_lambda % S.q)) % S.q + r2 * lambda) % S.q;
    (==) { Math.Lemmas.lemma_mod_plus_distr_r k (r2 * minus_lambda) S.q }
    ((k + r2 * minus_lambda) % S.q + r2 * lambda) % S.q;
    (==) { Math.Lemmas.lemma_mod_plus_distr_l (k + r2 * minus_lambda) (r2 * lambda) S.q }
    (k + r2 * minus_lambda + r2 * lambda) % S.q;
    (==) { Math.Lemmas.distributivity_add_right r2 minus_lambda lambda }
    (k + r2 * (minus_lambda + lambda)) % S.q;
    (==) { Math.Lemmas.lemma_mod_plus_distr_r k (r2 * (minus_lambda + lambda)) S.q }
    (k + (r2 * (minus_lambda + lambda) % S.q)) % S.q;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r r2 (minus_lambda + lambda) S.q }
    (k + (r2 * ((minus_lambda + lambda) % S.q) % S.q)) % S.q;
    (==) { }
    k % S.q;
    (==) { Math.Lemmas.small_mod k S.q }
    k;
  }

//--------------------------------------------

(**
 Fast computation of [k]P in affine coordinates
*)

val lemma_aff_point_mul_split_lambda: k:S.qelem -> p:S.aff_point ->
  Lemma (let r1, r2 = scalar_split_lambda k in aff_point_mul k p ==
    S.aff_point_add (aff_point_mul r1 p) (aff_point_mul r2 (aff_point_mul_lambda p)))

let lemma_aff_point_mul_split_lambda k p =
  let r1, r2 = scalar_split_lambda k in
  calc (==) {
    aff_point_mul k p;
    (==) { lemma_scalar_split_lambda_eval k }
    aff_point_mul S.(r1 +^ r2 *^ lambda) p;
    (==) { Math.Lemmas.lemma_mod_plus_distr_r r1 (r2 * lambda) S.q }
    aff_point_mul ((r1 + r2 * lambda) % S.q) p;
    (==) { SM.lemma_aff_point_mul_neg_modq (r1 + r2 * lambda) p }
    aff_point_mul (r1 + r2 * lambda) p;
    (==) { SM.lemma_aff_point_mul_neg_mul_add lambda r2 r1 p }
    S.aff_point_add (aff_point_mul r2 (aff_point_mul lambda p)) (aff_point_mul r1 p);
    (==) { lemma_glv_aff p }
    S.aff_point_add (aff_point_mul r2 (aff_point_mul_lambda p)) (aff_point_mul r1 p);
    (==) { LS.aff_point_add_comm_lemma (aff_point_mul r2 (aff_point_mul_lambda p)) (aff_point_mul r1 p) }
    S.aff_point_add (aff_point_mul r1 p) (aff_point_mul r2 (aff_point_mul_lambda p));
  }


val lemma_aff_point_mul_endo_split: k:S.qelem -> p:S.aff_point ->
  Lemma (aff_point_mul_endo_split k p == aff_point_mul k p)

let lemma_aff_point_mul_endo_split k p =
  let r10, r20 = scalar_split_lambda k in
  let lambda_p = aff_point_mul_lambda p in
  let r1, p1 = aff_negate_point_and_scalar_cond r10 p in
  let r2, p2 = aff_negate_point_and_scalar_cond r20 lambda_p in
  assert ((r1, p1, r2, p2) == aff_ecmult_endo_split k p);
  let is_high1 = S.scalar_is_high r10 in
  let is_high2 = S.scalar_is_high r20 in

  if is_high1 && is_high2 then begin
    SM.lemma_aff_point_mul_neg r10 p;
    SM.lemma_aff_point_mul_neg r20 lambda_p;
    lemma_aff_point_mul_split_lambda k p end
  else begin
    if is_high1 && not is_high2 then begin
      SM.lemma_aff_point_mul_neg r10 p;
      lemma_aff_point_mul_split_lambda k p end
    else begin
      if not is_high1 && is_high2 then begin
      SM.lemma_aff_point_mul_neg r20 lambda_p;
      lemma_aff_point_mul_split_lambda k p end
      else lemma_aff_point_mul_split_lambda k p
    end
  end

//---------------------------------

val lemma_ecmult_endo_split_to_aff: k:S.qelem -> p:S.proj_point -> Lemma
  (let r1, p1, r2, p2 = ecmult_endo_split k p in
   let ar1, ap1, ar2, ap2 = aff_ecmult_endo_split k (S.to_aff_point p) in
   r1 == ar1 /\ S.to_aff_point p1 == ap1 /\ r2 == ar2 /\ S.to_aff_point p2 == ap2)

let lemma_ecmult_endo_split_to_aff k p =
  let r1, p1, r2, p2 = ecmult_endo_split k p in
  let ar1, ap1, ar2, ap2 = aff_ecmult_endo_split k (S.to_aff_point p) in
  assert (r1 == ar1 /\ r2 == ar2);

  let r10, r20 = scalar_split_lambda k in
  let p_aff = S.to_aff_point p in

  let lambda_p = point_mul_lambda p in
  let lambda_p_aff = aff_point_mul_lambda p_aff in
  lemma_glv p; lemma_glv_aff p_aff;
  assert (S.to_aff_point lambda_p == lambda_p_aff);

  let is_high1 = S.scalar_is_high r10 in
  let is_high2 = S.scalar_is_high r20 in
  if not is_high1 && not is_high2 then ()
  else begin
    if not is_high1 && is_high2 then
      LS.to_aff_point_negate_lemma lambda_p
    else begin
      if is_high1 && not is_high2 then
        LS.to_aff_point_negate_lemma p
      else begin
        LS.to_aff_point_negate_lemma p;
        LS.to_aff_point_negate_lemma lambda_p
      end
    end
  end


(**
  Fast computation of [k1]P1 + [k2]P2 in projective coordinates
*)

// [k1]P1 + [k2]P2 = [r11 + r12 * lambda]P1 + [r21 + r22 * lambda]P2
// = [r11]P1 + [r12]([lambda]P1) + [r21]P2 + [r22]([lambda]P2)
// = [r11](p1_x, p1_y) + [r12](beta * p1_x, p1_y) + [r21](p2_x, p2_y) + [r22](beta * p2_x, p2_y)
let aff_proj_point_mul_double_split_lambda
  (k1:S.qelem) (p1:S.proj_point) (k2:S.qelem) (p2:S.proj_point) : S.aff_point =
  let r11, p11, r12, p12 = ecmult_endo_split k1 p1 in
  let r21, p21, r22, p22 = ecmult_endo_split k2 p2 in
  if r11 < pow2 128 && r12 < pow2 128 && r21 < pow2 128 && r22 < pow2 128 then
    LE.exp_four_fw S.mk_k256_comm_monoid
      (S.to_aff_point p11) 128 r11 (S.to_aff_point p12) r12
      (S.to_aff_point p21) r21 (S.to_aff_point p22) r22 5
  else
    S.to_aff_point (S.point_mul_double k1 p1 k2 p2)


val lemma_aff_proj_point_mul_double_split_lambda:
  k1:S.qelem -> p1:S.proj_point -> k2:S.qelem -> p2:S.proj_point ->
  Lemma (aff_proj_point_mul_double_split_lambda k1 p1 k2 p2 ==
    S.aff_point_add (aff_point_mul k1 (S.to_aff_point p1)) (aff_point_mul k2 (S.to_aff_point p2)))

let lemma_aff_proj_point_mul_double_split_lambda k1 p1 k2 p2 =
  let r11, p11, r12, p12 = ecmult_endo_split k1 p1 in
  let r21, p21, r22, p22 = ecmult_endo_split k2 p2 in

  if r11 < pow2 128 && r12 < pow2 128 && r21 < pow2 128 && r22 < pow2 128 then begin
    let p1_aff  = S.to_aff_point p1 in
    let p2_aff  = S.to_aff_point p2 in
    let p11_aff = S.to_aff_point p11 in
    let p12_aff = S.to_aff_point p12 in
    let p21_aff = S.to_aff_point p21 in
    let p22_aff = S.to_aff_point p22 in

    calc (==) {
      aff_proj_point_mul_double_split_lambda k1 p1 k2 p2;
    (==) {
      LE.exp_four_fw_lemma S.mk_k256_comm_monoid
        p11_aff 128 r11 p12_aff r12 p21_aff r21 p22_aff r22 5 }
      S.aff_point_add
        (S.aff_point_add
          (S.aff_point_add (aff_point_mul r11 p11_aff) (aff_point_mul r12 p12_aff))
          (aff_point_mul r21 p21_aff))
        (aff_point_mul r22 p22_aff);
      (==) { lemma_aff_point_mul_endo_split k1 p1_aff; lemma_ecmult_endo_split_to_aff k1 p1 }
      S.aff_point_add
        (S.aff_point_add (aff_point_mul k1 p1_aff) (aff_point_mul r21 p21_aff))
        (aff_point_mul r22 p22_aff);
      (==) { LS.aff_point_add_assoc_lemma
        (aff_point_mul k1 p1_aff) (aff_point_mul r21 p21_aff) (aff_point_mul r22 p22_aff) }
      S.aff_point_add (aff_point_mul k1 p1_aff)
        (S.aff_point_add (aff_point_mul r21 p21_aff) (aff_point_mul r22 p22_aff));
      (==) { lemma_aff_point_mul_endo_split k2 p2_aff; lemma_ecmult_endo_split_to_aff k2 p2 }
      S.aff_point_add (aff_point_mul k1 p1_aff) (aff_point_mul k2 p2_aff);
    } end
  else begin
    SE.exp_double_fw_lemma S.mk_k256_concrete_ops p1 256 k1 p2 k2 5;
    LE.exp_double_fw_lemma S.mk_k256_comm_monoid
      (S.to_aff_point p1) 256 k1 (S.to_aff_point p2) k2 5 end

//-----------------------------------

// [a]P in projective coordinates for a >= 0
let point_mul_def a p = SE.pow S.mk_k256_concrete_ops p a

// [k]P or -[k]P = [k](-P)
val aff_point_negate_cond_pow_lemma: is_negate:bool -> p:S.proj_point -> k:nat -> Lemma
  (aff_point_negate_cond (S.to_aff_point (point_mul_def k p)) is_negate ==
   aff_point_mul k (S.to_aff_point (point_negate_cond p is_negate)))

let aff_point_negate_cond_pow_lemma is_negate p k =
  let p_aff = S.to_aff_point p in
  if is_negate then
    calc (==) {
      S.aff_point_negate (S.to_aff_point (point_mul_def k p));
      (==) { SE.pow_lemma S.mk_k256_concrete_ops p k }
      S.aff_point_negate (aff_point_mul k p_aff);
      (==) { SM.aff_point_mul_neg_lemma k p_aff }
      aff_point_mul k (S.aff_point_negate p_aff);
      (==) { LS.to_aff_point_negate_lemma p }
      aff_point_mul k (S.to_aff_point (S.point_negate p));
    }
  else
    SE.pow_lemma S.mk_k256_concrete_ops p k


// [k]([lambda]P) = [lambda]([k]P) or [k](-[lambda]P) = [lambda](-[k]P)
val aff_point_negate_cond_lambda_pow_lemma: is_negate:bool -> p:S.proj_point -> k:nat -> Lemma
  (aff_point_mul lambda (aff_point_negate_cond (S.to_aff_point (point_mul_def k p)) is_negate) ==
   aff_point_mul k (S.to_aff_point (point_negate_cond (point_mul_lambda p) is_negate)))

let aff_point_negate_cond_lambda_pow_lemma is_negate p k =
  let p_aff = S.to_aff_point p in
  let p_lambda = point_mul_lambda p in

  if is_negate then
    calc (==) {
      aff_point_mul lambda (S.aff_point_negate (S.to_aff_point (point_mul_def k p)));
      (==) { SE.pow_lemma S.mk_k256_concrete_ops p k }
      aff_point_mul lambda (S.aff_point_negate (aff_point_mul k p_aff));
      (==) { SM.aff_point_mul_mul_neg_lemma lambda k p_aff }
      aff_point_mul k (S.aff_point_negate (aff_point_mul lambda p_aff));
      (==) { lemma_glv p }
      aff_point_mul k (S.aff_point_negate (S.to_aff_point p_lambda));
      (==) { LS.to_aff_point_negate_lemma p_lambda }
      aff_point_mul k (S.to_aff_point (S.point_negate p_lambda));
    }
  else
    calc (==) {
      aff_point_mul lambda (S.to_aff_point (point_mul_def k p));
      (==) { SE.pow_lemma S.mk_k256_concrete_ops p k }
      aff_point_mul lambda (aff_point_mul k p_aff);
      (==) { SM.aff_point_mul_mul_lemma lambda k p_aff }
      aff_point_mul k (aff_point_mul lambda p_aff);
      (==) { lemma_glv p }
      aff_point_mul k (S.to_aff_point p_lambda);
    }
