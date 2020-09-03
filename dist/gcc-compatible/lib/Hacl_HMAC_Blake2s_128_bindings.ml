open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_HMAC_Blake2s_128_compute_blake2s_128 =
      foreign "Hacl_HMAC_Blake2s_128_compute_blake2s_128"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))))
  end