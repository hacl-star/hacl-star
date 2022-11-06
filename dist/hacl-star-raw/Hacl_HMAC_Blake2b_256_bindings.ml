open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_HMAC_Blake2b_256_compute_blake2b_256 =
      foreign "Hacl_HMAC_Blake2b_256_compute_blake2b_256"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))))
  end