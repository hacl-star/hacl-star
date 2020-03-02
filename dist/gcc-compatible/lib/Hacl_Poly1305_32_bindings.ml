open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Poly1305_32_blocklen =
      foreign_value "Hacl_Poly1305_32_blocklen" uint32_t
    let hacl_Poly1305_32_poly1305_init =
      foreign "Hacl_Poly1305_32_poly1305_init"
        ((ptr uint64_t) @-> (ocaml_bytes @-> (returning void)))
    let hacl_Poly1305_32_poly1305_update1 =
      foreign "Hacl_Poly1305_32_poly1305_update1"
        ((ptr uint64_t) @-> (ocaml_bytes @-> (returning void)))
    let hacl_Poly1305_32_poly1305_update =
      foreign "Hacl_Poly1305_32_poly1305_update"
        ((ptr uint64_t) @-> (uint32_t @-> (ocaml_bytes @-> (returning void))))
    let hacl_Poly1305_32_poly1305_finish =
      foreign "Hacl_Poly1305_32_poly1305_finish"
        (ocaml_bytes @->
           (ocaml_bytes @-> ((ptr uint64_t) @-> (returning void))))
    let hacl_Poly1305_32_poly1305_mac =
      foreign "Hacl_Poly1305_32_poly1305_mac"
        (ocaml_bytes @->
           (uint32_t @-> (ocaml_bytes @-> (ocaml_bytes @-> (returning void)))))
  end