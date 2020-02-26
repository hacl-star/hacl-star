open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Curve25519_64_scalarmult =
      foreign "Hacl_Curve25519_64_scalarmult"
        (ocaml_bytes @-> (ocaml_bytes @-> (ocaml_bytes @-> (returning void))))
    let hacl_Curve25519_64_secret_to_public =
      foreign "Hacl_Curve25519_64_secret_to_public"
        (ocaml_bytes @-> (ocaml_bytes @-> (returning void)))
    let hacl_Curve25519_64_ecdh =
      foreign "Hacl_Curve25519_64_ecdh"
        (ocaml_bytes @-> (ocaml_bytes @-> (ocaml_bytes @-> (returning bool))))
  end