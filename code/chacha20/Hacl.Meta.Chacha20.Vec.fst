module Hacl.Meta.Chacha20.Vec

#set-options "--z3rlimit 250 --max_fuel 0 --max_ifuel 0"

// Somehow miraculously, this works.
%splice[
  chacha20_core_higher;
  chacha20_encrypt_higher;
  chacha20_decrypt_higher
] (Meta.Interface.specialize [
  `Hacl.Impl.Chacha20.Vec.chacha20_encrypt;
  `Hacl.Impl.Chacha20.Vec.chacha20_decrypt
])
