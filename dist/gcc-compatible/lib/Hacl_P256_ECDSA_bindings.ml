open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_P256_ECDSA_ecp256dh_i =
      foreign "Hacl_P256_ECDSA_ecp256dh_i"
        (ocaml_bytes @-> (ocaml_bytes @-> (returning uint64_t)))
      
    let hacl_P256_ECDSA_ecp256dh_r =
      foreign "Hacl_P256_ECDSA_ecp256dh_r"
        (ocaml_bytes @->
           (ocaml_bytes @-> (ocaml_bytes @-> (returning uint64_t))))
      
  end