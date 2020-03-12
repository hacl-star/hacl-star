open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let everCrypt_Ed25519_sign =
      foreign "EverCrypt_Ed25519_sign"
        (ocaml_bytes @->
           (ocaml_bytes @-> (uint32_t @-> (ocaml_bytes @-> (returning void)))))
    let everCrypt_Ed25519_verify =
      foreign "EverCrypt_Ed25519_verify"
        (ocaml_bytes @->
           (uint32_t @-> (ocaml_bytes @-> (ocaml_bytes @-> (returning bool)))))
    let everCrypt_Ed25519_secret_to_public =
      foreign "EverCrypt_Ed25519_secret_to_public"
        (ocaml_bytes @-> (ocaml_bytes @-> (returning void)))
    let everCrypt_Ed25519_expand_keys =
      foreign "EverCrypt_Ed25519_expand_keys"
        (ocaml_bytes @-> (ocaml_bytes @-> (returning void)))
    let everCrypt_Ed25519_sign_expanded =
      foreign "EverCrypt_Ed25519_sign_expanded"
        (ocaml_bytes @->
           (ocaml_bytes @-> (uint32_t @-> (ocaml_bytes @-> (returning void)))))
  end