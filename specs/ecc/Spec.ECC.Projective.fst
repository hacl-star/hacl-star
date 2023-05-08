module Spec.ECC.Projective

open FStar.Mul

module SE = Spec.Exponentiation
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
