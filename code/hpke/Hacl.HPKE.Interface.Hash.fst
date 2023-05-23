module Hacl.HPKE.Interface.Hash

module S = Spec.Agile.HPKE
module Hash = Hacl.Hash.Definitions

[@ Meta.Attribute.specialize ]
noextract
assume val hash: #cs:S.ciphersuite -> Hash.hash_st (S.hash_of_cs cs)

(** Instantiations of hash **)

inline_for_extraction noextract
let hash_sha256 : Hash.hash_st Spec.Agile.Hash.SHA2_256 =
  Hacl.Streaming.SHA2.hash_256
inline_for_extraction noextract
let hash_sha512 : Hash.hash_st Spec.Agile.Hash.SHA2_512 =
  Hacl.Streaming.SHA2.hash_512
