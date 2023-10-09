module Hacl.Spec.PCurves.Qinv

open FStar.Mul

module SE = Spec.Exponentiation
module LE = Lib.Exponentiation
module M = Lib.NatMod
module S = Spec.PCurves

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let nat_mod_comm_monoid {| S.curve_params |} = M.mk_nat_mod_comm_monoid S.order

let mk_to_nat_mod_comm_monoid {| S.curve_params |} : SE.to_comm_monoid S.qelem = {
  SE.a_spec = S.qelem;
  SE.comm_monoid = nat_mod_comm_monoid;
  SE.refl = (fun (x:S.qelem) -> x);
}

val one_mod {| S.curve_params |} : SE.one_st S.qelem mk_to_nat_mod_comm_monoid
let one_mod _ = 1

val mul_mod {| S.curve_params |} : SE.mul_st S.qelem mk_to_nat_mod_comm_monoid
let mul_mod x y = S.qmul x y

val sqr_mod {| S.curve_params |} : SE.sqr_st S.qelem mk_to_nat_mod_comm_monoid
let sqr_mod x = S.qmul x x

let mk_nat_mod_concrete_ops {| S.curve_params |} : SE.concrete_ops S.qelem = {
  SE.to = mk_to_nat_mod_comm_monoid;
  SE.one = one_mod;
  SE.mul = mul_mod;
  SE.sqr = sqr_mod;
}

let qsquare_times {| S.curve_params |} (a:S.qelem) (b:nat) : S.qelem =
  SE.exp_pow2 mk_nat_mod_concrete_ops a b

val qsquare_times_lemma: {| S.curve_params |} -> a:S.qelem -> b:nat ->
  Lemma (qsquare_times a b == M.pow a (pow2 b) % S.order)
let qsquare_times_lemma a b =
  SE.exp_pow2_lemma mk_nat_mod_concrete_ops a b;
  LE.exp_pow2_lemma nat_mod_comm_monoid a b;
  assert (qsquare_times a b == LE.pow nat_mod_comm_monoid a (pow2 b));
  M.lemma_pow_nat_mod_is_pow #S.order a (pow2 b)

