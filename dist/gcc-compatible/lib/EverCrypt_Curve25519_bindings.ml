open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let everCrypt_Curve25519_secret_to_public =
      foreign "EverCrypt_Curve25519_secret_to_public"
        (ocaml_bytes @-> (ocaml_bytes @-> (returning void)))
    let everCrypt_Curve25519_scalarmult =
      foreign "EverCrypt_Curve25519_scalarmult"
        (ocaml_bytes @-> (ocaml_bytes @-> (ocaml_bytes @-> (returning void))))
    let everCrypt_Curve25519_ecdh =
      foreign "EverCrypt_Curve25519_ecdh"
        (ocaml_bytes @-> (ocaml_bytes @-> (ocaml_bytes @-> (returning bool))))
  end