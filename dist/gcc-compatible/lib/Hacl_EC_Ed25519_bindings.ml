open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_EC_Ed25519_mk_felem_zero =
      foreign "Hacl_EC_Ed25519_mk_felem_zero"
        ((ptr uint64_t) @-> (returning void))
    let hacl_EC_Ed25519_mk_felem_one =
      foreign "Hacl_EC_Ed25519_mk_felem_one"
        ((ptr uint64_t) @-> (returning void))
    let hacl_EC_Ed25519_felem_add =
      foreign "Hacl_EC_Ed25519_felem_add"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))
    let hacl_EC_Ed25519_felem_sub =
      foreign "Hacl_EC_Ed25519_felem_sub"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))
    let hacl_EC_Ed25519_felem_mul =
      foreign "Hacl_EC_Ed25519_felem_mul"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))
    let hacl_EC_Ed25519_felem_inv =
      foreign "Hacl_EC_Ed25519_felem_inv"
        ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void)))
    let hacl_EC_Ed25519_felem_load =
      foreign "Hacl_EC_Ed25519_felem_load"
        (ocaml_bytes @-> ((ptr uint64_t) @-> (returning void)))
    let hacl_EC_Ed25519_felem_store =
      foreign "Hacl_EC_Ed25519_felem_store"
        ((ptr uint64_t) @-> (ocaml_bytes @-> (returning void)))
    let hacl_EC_Ed25519_mk_point_at_inf =
      foreign "Hacl_EC_Ed25519_mk_point_at_inf"
        ((ptr uint64_t) @-> (returning void))
    let hacl_EC_Ed25519_mk_base_point =
      foreign "Hacl_EC_Ed25519_mk_base_point"
        ((ptr uint64_t) @-> (returning void))
    let hacl_EC_Ed25519_point_negate =
      foreign "Hacl_EC_Ed25519_point_negate"
        ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void)))
    let hacl_EC_Ed25519_point_add =
      foreign "Hacl_EC_Ed25519_point_add"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))
    let hacl_EC_Ed25519_point_mul =
      foreign "Hacl_EC_Ed25519_point_mul"
        (ocaml_bytes @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))
    let hacl_EC_Ed25519_point_eq =
      foreign "Hacl_EC_Ed25519_point_eq"
        ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning bool)))
    let hacl_EC_Ed25519_point_compress =
      foreign "Hacl_EC_Ed25519_point_compress"
        ((ptr uint64_t) @-> (ocaml_bytes @-> (returning void)))
    let hacl_EC_Ed25519_point_decompress =
      foreign "Hacl_EC_Ed25519_point_decompress"
        (ocaml_bytes @-> ((ptr uint64_t) @-> (returning bool)))
  end