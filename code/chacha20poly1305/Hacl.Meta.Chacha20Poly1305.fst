module Hacl.Meta.Chacha20Poly1305

#set-options "--z3rlimit 250 --max_fuel 0 --max_ifuel 1"

%splice[
  poly1305_padded_higher;
  poly1305_do_higher;
  aead_encrypt_higher;
  aead_decrypt_higher
] (Meta.Interface.specialize [
    `Hacl.Impl.Chacha20Poly1305.aead_encrypt;
    `Hacl.Impl.Chacha20Poly1305.aead_decrypt
])
