module Hacl.FFDHE

open Lib.IntTypes

module S = Spec.FFDHE
module DH = Hacl.Impl.FFDHE
module BD = Hacl.Bignum.Definitions
module BE = Hacl.Bignum.Exponentiation

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let t_limbs = U64

inline_for_extraction noextract
let ke (a:S.ffdhe_alg) =
  BE.mk_runtime_exp #t_limbs (BD.blocks (DH.ffdhe_len a) (size (numbytes t_limbs)))

private
[@CInline]
let ffdhe_check_pk (a:S.ffdhe_alg) : DH.ffdhe_check_pk_st t_limbs a (DH.ffdhe_len a) =
  DH.ffdhe_check_pk #t_limbs a (DH.ffdhe_len a)

private
[@CInline]
let ffdhe_compute_exp (a:S.ffdhe_alg) : DH.ffdhe_compute_exp_st t_limbs a (DH.ffdhe_len a) (ke a) =
  DH.ffdhe_compute_exp a (DH.ffdhe_len a) (ke a)


let ffdhe_len (a:S.ffdhe_alg) : DH.size_pos = DH.ffdhe_len a

val ffdhe_secret_to_public: a:S.ffdhe_alg ->
  DH.ffdhe_secret_to_public_st t_limbs a (DH.ffdhe_len a) (ke a)
let ffdhe_secret_to_public a sk pk =
  let len = DH.ffdhe_len a in
  DH.ffdhe_secret_to_public a len (ke a) (ffdhe_compute_exp a) sk pk


val ffdhe_shared_secret: a:S.ffdhe_alg ->
  DH.ffdhe_shared_secret_st t_limbs a (DH.ffdhe_len a) (ke a)
let ffdhe_shared_secret a sk pk ss =
  let len = DH.ffdhe_len a in
  DH.ffdhe_shared_secret a len (ke a) (ffdhe_check_pk a) (ffdhe_compute_exp a) sk pk ss
