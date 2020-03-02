open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let everCrypt_Poly1305_poly1305 =
      foreign "EverCrypt_Poly1305_poly1305"
        (ocaml_bytes @->
           (ocaml_bytes @-> (uint32_t @-> (ocaml_bytes @-> (returning void)))))
  end