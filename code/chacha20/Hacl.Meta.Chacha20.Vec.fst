module Hacl.Meta.Chacha20.Vec

#set-options "--z3rlimit 250 --fuel 0 --ifuel 0"

// Somehow miraculously, this works.
%splice[
  vec_chacha20_core_higher;
  vec_chacha20_encrypt_higher;
  vec_chacha20_decrypt_higher
] (Meta.Interface.specialize (`Hacl.Impl.Chacha20.Core32xN.lanes) [
  `Hacl.Impl.Chacha20.Vec.chacha20_encrypt;
  `Hacl.Impl.Chacha20.Vec.chacha20_decrypt
])
