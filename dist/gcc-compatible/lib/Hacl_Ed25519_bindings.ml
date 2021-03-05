open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Bignum25519_reduce_513 =
      foreign "Hacl_Bignum25519_reduce_513"
        ((ptr uint64_t) @-> (returning void))
    let hacl_Bignum25519_inverse =
      foreign "Hacl_Bignum25519_inverse"
        ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void)))
    let hacl_Bignum25519_load_51 =
      foreign "Hacl_Bignum25519_load_51"
        ((ptr uint64_t) @-> (ocaml_bytes @-> (returning void)))
    let hacl_Bignum25519_store_51 =
      foreign "Hacl_Bignum25519_store_51"
        (ocaml_bytes @-> ((ptr uint64_t) @-> (returning void)))
    let hacl_Impl_Ed25519_PointAdd_point_add =
      foreign "Hacl_Impl_Ed25519_PointAdd_point_add"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))
    let hacl_Impl_Ed25519_Ladder_point_mul =
      foreign "Hacl_Impl_Ed25519_Ladder_point_mul"
        ((ptr uint64_t) @->
           (ocaml_bytes @-> ((ptr uint64_t) @-> (returning void))))
    let hacl_Impl_Ed25519_PointCompress_point_compress =
      foreign "Hacl_Impl_Ed25519_PointCompress_point_compress"
        (ocaml_bytes @-> ((ptr uint64_t) @-> (returning void)))
    let hacl_Impl_Ed25519_PointDecompress_point_decompress =
      foreign "Hacl_Impl_Ed25519_PointDecompress_point_decompress"
        ((ptr uint64_t) @-> (ocaml_bytes @-> (returning bool)))
    let hacl_Impl_Ed25519_PointEqual_point_equal =
      foreign "Hacl_Impl_Ed25519_PointEqual_point_equal"
        ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning bool)))
    let hacl_Impl_Ed25519_PointNegate_point_negate =
      foreign "Hacl_Impl_Ed25519_PointNegate_point_negate"
        ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void)))
    let hacl_Ed25519_sign =
      foreign "Hacl_Ed25519_sign"
        (ocaml_bytes @->
           (ocaml_bytes @-> (uint32_t @-> (ocaml_bytes @-> (returning void)))))
    let hacl_Ed25519_verify =
      foreign "Hacl_Ed25519_verify"
        (ocaml_bytes @->
           (uint32_t @-> (ocaml_bytes @-> (ocaml_bytes @-> (returning bool)))))
    let hacl_Ed25519_secret_to_public =
      foreign "Hacl_Ed25519_secret_to_public"
        (ocaml_bytes @-> (ocaml_bytes @-> (returning void)))
    let hacl_Ed25519_expand_keys =
      foreign "Hacl_Ed25519_expand_keys"
        (ocaml_bytes @-> (ocaml_bytes @-> (returning void)))
    let hacl_Ed25519_sign_expanded =
      foreign "Hacl_Ed25519_sign_expanded"
        (ocaml_bytes @->
           (ocaml_bytes @-> (uint32_t @-> (ocaml_bytes @-> (returning void)))))
  end