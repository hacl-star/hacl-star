open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_MAC_Poly1305_Simd128_mac =
      foreign "Hacl_MAC_Poly1305_Simd128_mac"
        (ocaml_bytes @->
           (ocaml_bytes @-> (uint32_t @-> (ocaml_bytes @-> (returning void)))))
  end