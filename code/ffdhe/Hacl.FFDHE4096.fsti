module Hacl.FFDHE4096

open Lib.IntTypes

module S = Spec.FFDHE
module DH = Hacl.Impl.FFDHE
module BE = Hacl.Bignum.Exponentiation

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let t_limbs = U64

inline_for_extraction noextract
let n_limbs = 64ul //=512/8

inline_for_extraction noextract
let a_ffdhe = Spec.FFDHE.FFDHE4096

inline_for_extraction noextract
let len = normalize_term (DH.ffdhe_len a_ffdhe) //=512


//a specialized version of bignum
inline_for_extraction noextract
val ke_4096 : BE.exp t_limbs


val new_ffdhe_precomp_p: DH.new_ffdhe_precomp_p_st t_limbs a_ffdhe len ke_4096

val ffdhe_secret_to_public_precomp: DH.ffdhe_secret_to_public_precomp_st t_limbs a_ffdhe len ke_4096

val ffdhe_secret_to_public: DH.ffdhe_secret_to_public_st t_limbs a_ffdhe len ke_4096

val ffdhe_shared_secret_precomp: DH.ffdhe_shared_secret_precomp_st t_limbs a_ffdhe len ke_4096

val ffdhe_shared_secret: DH.ffdhe_shared_secret_st t_limbs a_ffdhe len ke_4096
