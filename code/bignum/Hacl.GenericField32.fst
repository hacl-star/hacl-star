module Hacl.GenericField32

open FStar.Mul

module BN = Hacl.Bignum
module GF = Hacl.Bignum.GenericField
module BM = Hacl.Bignum.Montgomery

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let km (len:BN.meta_len t_limbs) =
  BM.mk_runtime_mont len

let field_init len r nBits n =
  GF.bn_field_init (km len) r nBits n

let field_get_len k =
  GF.bn_field_get_len k

let to_field k a aM =
  GF.bn_to_field (km k.GF.len) k a aM

let from_field k aM a =
  GF.bn_from_field (km k.GF.len) k aM a

let add k aM bM cM =
  GF.bn_field_add (km k.GF.len) k aM bM cM

let sub k aM bM cM =
  GF.bn_field_sub (km k.GF.len) k aM bM cM

let mul k aM bM cM =
  GF.bn_field_mul (km k.GF.len) k aM bM cM

let sqr k aM cM =
  GF.bn_field_sqr (km k.GF.len) k aM cM

let one k oneM =
  GF.bn_field_one (km k.GF.len) k oneM

let inverse k aM aInvM =
  GF.bn_field_inv (km k.GF.len) k aM aInvM
