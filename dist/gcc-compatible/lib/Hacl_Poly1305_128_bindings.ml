open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Poly1305_128_blocklen =
      foreign_value "Hacl_Poly1305_128_blocklen" uint32_t
    let hacl_Poly1305_128_poly1305_mac =
      foreign "Hacl_Poly1305_128_poly1305_mac"
        (ocaml_bytes @->
           (uint32_t @-> (ocaml_bytes @-> (ocaml_bytes @-> (returning void)))))
  end