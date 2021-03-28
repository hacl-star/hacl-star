module Hacl.GenericField32

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

let to_field len k a aM =
  let len = field_get_len k in
  MA.bn_to_field (km len) k a aM

let from_field len k aM a =
  let len = field_get_len k in
  MA.bn_from_field (km len) k aM a

let add len k aM bM cM =
  let len = field_get_len k in
  MA.bn_field_add (km len) k aM bM cM

let sub len k aM bM cM =
  let len = field_get_len k in
  MA.bn_field_sub (km len) k aM bM cM

let mul len k aM bM cM =
  let len = field_get_len k in
  MA.bn_field_mul (km len) k aM bM cM

let sqr len k aM cM =
  let len = field_get_len k in
  MA.bn_field_sqr (km len) k aM cM

let one len k oneM =
  let len = field_get_len k in
  MA.bn_field_one (km len) k oneM

let exp_consttime len k aM bBits b resM =
  let len = field_get_len k in
  MA.bn_field_exp_consttime (km len) k aM bBits b resM

let exp_vartime len k aM bBits b resM =
  let len = field_get_len k in
  MA.bn_field_exp_vartime (km len) k aM bBits b resM

let inverse len k aM aInvM =
  MA.bn_field_inv len (exp_vartime len) k aM aInvM
