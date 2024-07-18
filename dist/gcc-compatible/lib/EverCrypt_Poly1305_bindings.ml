open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let everCrypt_Poly1305_mac =
      foreign "EverCrypt_Poly1305_mac"
        (ocaml_bytes @->
           (ocaml_bytes @-> (uint32_t @-> (ocaml_bytes @-> (returning void)))))
  end