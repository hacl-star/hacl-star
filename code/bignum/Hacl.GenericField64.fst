module Hacl.GenericField64

open FStar.Mul

module BN = Hacl.Bignum
module MA = Hacl.Bignum.MontArithmetic
module BM = Hacl.Bignum.Montgomery

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let km (len:BN.meta_len t_limbs) =
  BM.mk_runtime_mont len

let field_modulus_check len n =
  MA.bn_field_check_modulus (km len) n

let field_init len r n =
  MA.bn_field_init (km len) r n

let field_free k =
  MA.bn_field_free k

let field_get_len k =
  MA.bn_field_get_len k

let to_field k a aM =
  MA.bn_to_field (km k.MA.len) k a aM

let from_field k aM a =
  MA.bn_from_field (km k.MA.len) k aM a

let add k aM bM cM =
  MA.bn_field_add (km k.MA.len) k aM bM cM

let sub k aM bM cM =
  MA.bn_field_sub (km k.MA.len) k aM bM cM

let mul k aM bM cM =
  MA.bn_field_mul (km k.MA.len) k aM bM cM

let sqr k aM cM =
  MA.bn_field_sqr (km k.MA.len) k aM cM

let one k oneM =
  MA.bn_field_one (km k.MA.len) k oneM

let exp_consttime k aM bBits b resM =
  MA.bn_field_exp_consttime (km k.MA.len) k aM bBits b resM

let exp_vartime k aM bBits b resM =
  MA.bn_field_exp_vartime (km k.MA.len) k aM bBits b resM

let inverse k aM aInvM =
  MA.bn_field_inv k (exp_vartime k) aM aInvM
