open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Gf128_NI_ghash =
      foreign "Hacl_Gf128_NI_ghash"
        (ocaml_bytes @->
           (uint32_t @-> (ocaml_bytes @-> (ocaml_bytes @-> (returning void)))))
  end