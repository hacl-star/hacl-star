open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Blake2bUnkeyed_blake2b_32_u =
      foreign "Hacl_Blake2bUnkeyed_blake2b_32_u"
        (ocaml_bytes @-> (uint32_t @-> (ocaml_bytes @-> (returning void))))
      
  end