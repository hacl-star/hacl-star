module Hacl.Impl.Generic.HKDF

module S = Spec.Agile.HPKE
module HK = Hacl.HKDF

[@ Meta.Attribute.specialize ]
assume val hkdf_extract: #cs:S.ciphersuite -> HK.extract_st (S.hash_of_cs cs)

[@ Meta.Attribute.specialize ]
assume val hkdf_expand: #cs:S.ciphersuite -> HK.expand_st (S.hash_of_cs cs)
