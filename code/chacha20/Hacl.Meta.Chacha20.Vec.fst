module Hacl.Meta.Chacha20.Vec

#set-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0"

// Somehow miraculously, this works.
%splice[
  double_round_inline;
  chacha20_core_inline;
  chacha20_init_inline;
  chacha20_encrypt_inline;
  chacha20_decrypt_inline
] (Meta.Interface.specialize [
  `Hacl.Impl.Chacha20.Vec.chacha20_encrypt;
  `Hacl.Impl.Chacha20.Vec.chacha20_decrypt
])
