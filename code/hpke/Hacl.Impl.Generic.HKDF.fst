module Hacl.Impl.Generic.HKDF

module S = Spec.Agile.HPKE
module HK = Hacl.HKDF
module Hash = Spec.Agile.Hash

[@ Meta.Attribute.specialize ]
assume val hkdf_extract: #cs:S.ciphersuite -> HK.extract_st (S.hash_of_cs cs)

[@ Meta.Attribute.specialize ]
assume val hkdf_expand: #cs:S.ciphersuite -> HK.expand_st (S.hash_of_cs cs)


(** Instantiations of hkdf **)

inline_for_extraction noextract
let hkdf_extract256 : HK.extract_st Hash.SHA2_256 = Hacl.HKDF.extract_sha2_256
inline_for_extraction noextract
let hkdf_expand256 : HK.expand_st Hash.SHA2_256 = Hacl.HKDF.expand_sha2_256

inline_for_extraction noextract
let hkdf_extract512 : HK.extract_st Hash.SHA2_512 = Hacl.HKDF.extract_sha2_512
inline_for_extraction noextract
let hkdf_expand512 : HK.expand_st Hash.SHA2_512 = Hacl.HKDF.expand_sha2_512
