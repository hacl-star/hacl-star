module Hacl.Meta.Chacha20Poly1305

#set-options "--z3rlimit 350 --max_fuel 0 --max_ifuel 1"

%splice[
  chacha20poly1305_poly1305_do_higher;
  chacha20poly1305_aead_encrypt_higher;
  chacha20poly1305_aead_decrypt_higher
] (Meta.Interface.specialize (`Hacl.Impl.Poly1305.Fields.field_spec) [
    `Hacl.Impl.Chacha20Poly1305.aead_encrypt;
    `Hacl.Impl.Chacha20Poly1305.aead_decrypt
])
