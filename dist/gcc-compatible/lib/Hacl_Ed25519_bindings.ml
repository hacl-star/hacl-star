open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Ed25519_sign =
      foreign "Hacl_Ed25519_sign"
        (ocaml_bytes @->
           (ocaml_bytes @-> (uint32_t @-> (ocaml_bytes @-> (returning void)))))
      
    let hacl_Ed25519_verify =
      foreign "Hacl_Ed25519_verify"
        (ocaml_bytes @->
           (uint32_t @-> (ocaml_bytes @-> (ocaml_bytes @-> (returning bool)))))
      
    let hacl_Ed25519_secret_to_public =
      foreign "Hacl_Ed25519_secret_to_public"
        (ocaml_bytes @-> (ocaml_bytes @-> (returning void)))
      
    let hacl_Ed25519_expand_keys =
      foreign "Hacl_Ed25519_expand_keys"
        (ocaml_bytes @-> (ocaml_bytes @-> (returning void)))
      
    let hacl_Ed25519_sign_expanded =
      foreign "Hacl_Ed25519_sign_expanded"
        (ocaml_bytes @->
           (ocaml_bytes @-> (uint32_t @-> (ocaml_bytes @-> (returning void)))))
      
  end