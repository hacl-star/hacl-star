open Utils
open Shared

module Hacl_Chacha20Poly1305_32 = Hacl_Chacha20Poly1305_32_bindings.Bindings(Hacl_Chacha20Poly1305_32_stubs)
module Hacl_Chacha20Poly1305_128 = Hacl_Chacha20Poly1305_128_bindings.Bindings(Hacl_Chacha20Poly1305_128_stubs)
module Hacl_Chacha20Poly1305_256 = Hacl_Chacha20Poly1305_256_bindings.Bindings(Hacl_Chacha20Poly1305_256_stubs)
module Hacl_Curve25519_51 = Hacl_Curve25519_51_bindings.Bindings(Hacl_Curve25519_51_stubs)
module Hacl_Curve25519_64 = Hacl_Curve25519_64_bindings.Bindings(Hacl_Curve25519_64_stubs)
module Hacl_Curve25519_64_Slow = Hacl_Curve25519_64_Slow_bindings.Bindings(Hacl_Curve25519_64_Slow_stubs)


module Chacha20_Poly1305_32 : Chacha20_Poly1305 =
  Make_Chacha20_Poly1305 (struct
    let encrypt = Hacl_Chacha20Poly1305_32.hacl_Chacha20Poly1305_32_aead_encrypt
    let decrypt = Hacl_Chacha20Poly1305_32.hacl_Chacha20Poly1305_32_aead_decrypt
  end)

module Chacha20_Poly1305_128 : Chacha20_Poly1305 =
  Make_Chacha20_Poly1305 (struct
    let encrypt = Hacl_Chacha20Poly1305_128.hacl_Chacha20Poly1305_128_aead_encrypt
    let decrypt = Hacl_Chacha20Poly1305_128.hacl_Chacha20Poly1305_128_aead_decrypt
  end)

module Chacha20_Poly1305_256 : Chacha20_Poly1305 =
  Make_Chacha20_Poly1305 (struct
    let encrypt = Hacl_Chacha20Poly1305_256.hacl_Chacha20Poly1305_256_aead_encrypt
    let decrypt = Hacl_Chacha20Poly1305_256.hacl_Chacha20Poly1305_256_aead_decrypt
  end)

module Curve25519_51 : Curve25519 =
  Make_Curve25519 (struct
    let secret_to_public = Hacl_Curve25519_51.hacl_Curve25519_51_secret_to_public
    let scalarmult = Hacl_Curve25519_51.hacl_Curve25519_51_scalarmult
    let ecdh = Hacl_Curve25519_51.hacl_Curve25519_51_ecdh
  end)

module Curve25519_64 : Curve25519 =
  Make_Curve25519 (struct
    let secret_to_public = Hacl_Curve25519_64.hacl_Curve25519_64_secret_to_public
    let scalarmult = Hacl_Curve25519_64.hacl_Curve25519_64_scalarmult
    let ecdh = Hacl_Curve25519_64.hacl_Curve25519_64_ecdh
  end)

module Curve25519_64_Slow : Curve25519 =
  Make_Curve25519 (struct
    let secret_to_public = Hacl_Curve25519_64_Slow.hacl_Curve25519_64_Slow_secret_to_public
    let scalarmult = Hacl_Curve25519_64_Slow.hacl_Curve25519_64_Slow_scalarmult
    let ecdh = Hacl_Curve25519_64_Slow.hacl_Curve25519_64_Slow_ecdh
  end)

module Curve25519_51_Internal = struct
  include Curve25519_51
  let fadd out f1 f2 = Hacl_Curve25519_51.hacl_Impl_Curve25519_Field51_fadd (uint64_ptr out) (uint64_ptr f1) (uint64_ptr f2)
  let fsub out f1 f2 = Hacl_Curve25519_51.hacl_Impl_Curve25519_Field51_fsub (uint64_ptr out) (uint64_ptr f1) (uint64_ptr f2)
  let fmul1 out f1 f2 = Hacl_Curve25519_51.hacl_Impl_Curve25519_Field51_fmul1 (uint64_ptr out) (uint64_ptr f1) f2
end
