module Spec.ECC.Projective

open FStar.Mul

module SE = Spec.Exponentiation
module LE = Lib.Exponentiation

module EC = Spec.ECC
module EPL = Spec.EC.Projective.Lemmas

include Spec.EC.Projective

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

///  Elliptic curve scalar multiplication

let mk_to_ec_comm_monoid (k:curve) : SE.to_comm_monoid (proj_point k) = {
  SE.a_spec = aff_point k;
  SE.comm_monoid = EC.mk_ec_comm_monoid k;
  SE.refl = to_aff_point k;
}

val point_at_inf_c: k:curve -> SE.one_st (proj_point k) (mk_to_ec_comm_monoid k)
let point_at_inf_c k _ =
  EPL.to_aff_point_at_infinity_lemma k;
  point_at_inf k


let is_point_at_inf_c (k:curve) (p:proj_point k)
  : res:bool{res ==> EC.is_aff_point_at_inf k (to_aff_point k p)}
 =
  EPL.lemma_aff_is_point_at_inf k p;
  is_point_at_inf k p


///  for elliptic curve with coeff_a = (-3) % prime

val point_add_c_a3: k:curve{k.coeff_a = (-3) % k.prime}
  -> SE.mul_st (proj_point k) (mk_to_ec_comm_monoid k)
let point_add_c_a3 k p q =
  EPL.to_aff_point_add_lemma_a3 k p q;
  point_add_a3 k p q

val point_double_c_a3: k:curve{k.coeff_a = (-3) % k.prime}
  -> SE.sqr_st (proj_point k) (mk_to_ec_comm_monoid k)
let point_double_c_a3 k p =
  EPL.to_aff_point_double_lemma_a3 k p;
  point_double_a3 k p

let mk_ec_concrete_ops_a3 (k:curve{k.coeff_a = (-3) % k.prime}) : SE.concrete_ops (proj_point k) =
{
  SE.to = mk_to_ec_comm_monoid k;
  SE.one = point_at_inf_c k;
  SE.mul = point_add_c_a3 k;
  SE.sqr = point_double_c_a3 k;
}


///  for elliptic curve with coeff_a = 0

val point_add_c_a0: k:curve{k.coeff_a = 0} -> SE.mul_st (proj_point k) (mk_to_ec_comm_monoid k)
let point_add_c_a0 k p q =
  EPL.to_aff_point_add_lemma_a0 k p q;
  point_add_a0 k p q

val point_double_c_a0: k:curve{k.coeff_a = 0} -> SE.sqr_st (proj_point k) (mk_to_ec_comm_monoid k)
let point_double_c_a0 k p =
  EPL.to_aff_point_double_lemma_a0 k p;
  point_double_a0 k p

let mk_ec_concrete_ops_a0 (k:curve{k.coeff_a = 0}) : SE.concrete_ops (proj_point k) =
{
  SE.to = mk_to_ec_comm_monoid k;
  SE.one = point_at_inf_c k;
  SE.mul = point_add_c_a0 k;
  SE.sqr = point_double_c_a0 k;
}


///  point_mul and point_mul_double_g

// TODO: add point_add and point_double for any k.coeff_a
let is_supported (k:curve) =
  k.coeff_a = 0 \/ k.coeff_a = (-3) % k.prime


// [a]P
let point_mul (k:curve{is_supported k}) (a:qelem k) (p:proj_point k)
  : res:proj_point k{to_aff_point k res == EC.aff_point_mul k a (to_aff_point k p) }
 =
  let aBits = 8 * k.order_len_bytes in // TODO: add order_bits to `curve`?
  let w = 4 in // TODO: use montgomery ladder for the spec?
  if k.coeff_a = 0 then begin
    SE.exp_fw_lemma (mk_ec_concrete_ops_a0 k) p aBits a w;
    LE.exp_fw_lemma (EC.mk_ec_comm_monoid k) (to_aff_point k p) aBits a w;
    SE.exp_fw (mk_ec_concrete_ops_a0 k) p aBits a w end
  else begin
    SE.exp_fw_lemma (mk_ec_concrete_ops_a3 k) p aBits a w;
    LE.exp_fw_lemma (EC.mk_ec_comm_monoid k) (to_aff_point k p) aBits a w;
    SE.exp_fw (mk_ec_concrete_ops_a3 k) p aBits a w end


// [a1]G + [a2]P
let point_mul_double_g (k:curve{is_supported k}) (a1 a2:qelem k) (p:proj_point k)
  : res:proj_point k{to_aff_point k res ==
      EC.aff_point_add k
        (EC.aff_point_mul k a1 k.base_point) (EC.aff_point_mul k a2 (to_aff_point k p)) }
 =
  let aBits = 8 * k.order_len_bytes in // TODO: add order_bits to `curve`?
  let w = 5 in // TODO: use montgomery ladder for the spec?

  EPL.lemma_proj_aff_id k k.base_point;
  let g_proj = to_proj_point k k.base_point in

  if k.coeff_a = 0 then begin
    SE.exp_double_fw_lemma (mk_ec_concrete_ops_a0 k) g_proj aBits a1 p a2 w;
    LE.exp_double_fw_lemma (EC.mk_ec_comm_monoid k) k.base_point aBits a1 (to_aff_point k p) a2 w;
    SE.exp_double_fw (mk_ec_concrete_ops_a0 k) g_proj aBits a1 p a2 w end
 else begin
    SE.exp_double_fw_lemma (mk_ec_concrete_ops_a3 k) g_proj aBits a1 p a2 w;
    LE.exp_double_fw_lemma (EC.mk_ec_comm_monoid k) k.base_point aBits a1 (to_aff_point k p) a2 w;
    SE.exp_double_fw (mk_ec_concrete_ops_a3 k) g_proj aBits a1 p a2 w end


let ec_concrete_ops_proj (k:curve{is_supported k}) : EC.ec_concrete_ops = {
  EC.ec = k;
  EC.t = proj_point k;
  EC.to_point_t = to_proj_point k;
  EC.to_aff_point = to_aff_point k;
  EC.lemma_to_from_aff_point = EPL.lemma_proj_aff_id k;
  EC.is_point_at_inf = is_point_at_inf_c k;
  EC.point_mul = point_mul k;
  EC.point_mul_double_g = point_mul_double_g k;
}
