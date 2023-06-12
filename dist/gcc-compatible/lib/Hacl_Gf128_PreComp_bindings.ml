open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Gf128_PreComp_gcm_init =
      foreign "Hacl_Gf128_PreComp_gcm_init"
        ((ptr uint64_t) @-> (ocaml_bytes @-> (returning void)))
    let hacl_Gf128_PreComp_gcm_update_blocks =
      foreign "Hacl_Gf128_PreComp_gcm_update_blocks"
        ((ptr uint64_t) @-> (uint32_t @-> (ocaml_bytes @-> (returning void))))
    let hacl_Gf128_PreComp_gcm_update_blocks_padded =
      foreign "Hacl_Gf128_PreComp_gcm_update_blocks_padded"
        ((ptr uint64_t) @-> (uint32_t @-> (ocaml_bytes @-> (returning void))))
    let hacl_Gf128_PreComp_gcm_emit =
      foreign "Hacl_Gf128_PreComp_gcm_emit"
        (ocaml_bytes @-> ((ptr uint64_t) @-> (returning void)))
    let hacl_Gf128_PreComp_ghash =
      foreign "Hacl_Gf128_PreComp_ghash"
        (ocaml_bytes @->
           (uint32_t @-> (ocaml_bytes @-> (ocaml_bytes @-> (returning void)))))
  end