open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    type hacl_Impl_Blake2_Core_blake2s_params =
      [ `hacl_Impl_Blake2_Core_blake2s_params ] structure
    let (hacl_Impl_Blake2_Core_blake2s_params :
      [ `hacl_Impl_Blake2_Core_blake2s_params ] structure typ) =
      structure "Hacl_Impl_Blake2_Core_blake2s_params_s"
    let hacl_Impl_Blake2_Core_blake2s_params_digest_length =
      field hacl_Impl_Blake2_Core_blake2s_params "digest_length" uint8_t
    let hacl_Impl_Blake2_Core_blake2s_params_key_length =
      field hacl_Impl_Blake2_Core_blake2s_params "key_length" uint8_t
    let hacl_Impl_Blake2_Core_blake2s_params_fanout =
      field hacl_Impl_Blake2_Core_blake2s_params "fanout" uint8_t
    let hacl_Impl_Blake2_Core_blake2s_params_depth =
      field hacl_Impl_Blake2_Core_blake2s_params "depth" uint8_t
    let hacl_Impl_Blake2_Core_blake2s_params_leaf_length =
      field hacl_Impl_Blake2_Core_blake2s_params "leaf_length" uint32_t
    let hacl_Impl_Blake2_Core_blake2s_params_node_offset =
      field hacl_Impl_Blake2_Core_blake2s_params "node_offset" uint32_t
    let hacl_Impl_Blake2_Core_blake2s_params_xof_length =
      field hacl_Impl_Blake2_Core_blake2s_params "xof_length" uint16_t
    let hacl_Impl_Blake2_Core_blake2s_params_node_depth =
      field hacl_Impl_Blake2_Core_blake2s_params "node_depth" uint8_t
    let hacl_Impl_Blake2_Core_blake2s_params_inner_length =
      field hacl_Impl_Blake2_Core_blake2s_params "inner_length" uint8_t
    let hacl_Impl_Blake2_Core_blake2s_params_salt =
      field hacl_Impl_Blake2_Core_blake2s_params "salt" (ptr uint8_t)
    let hacl_Impl_Blake2_Core_blake2s_params_personal =
      field hacl_Impl_Blake2_Core_blake2s_params "personal" (ptr uint8_t)
    let _ = seal hacl_Impl_Blake2_Core_blake2s_params
    type hacl_Impl_Blake2_Core_blake2b_params =
      [ `hacl_Impl_Blake2_Core_blake2b_params ] structure
    let (hacl_Impl_Blake2_Core_blake2b_params :
      [ `hacl_Impl_Blake2_Core_blake2b_params ] structure typ) =
      structure "Hacl_Impl_Blake2_Core_blake2b_params_s"
    let hacl_Impl_Blake2_Core_blake2b_params_digest_length1 =
      field hacl_Impl_Blake2_Core_blake2b_params "digest_length1" uint8_t
    let hacl_Impl_Blake2_Core_blake2b_params_key_length1 =
      field hacl_Impl_Blake2_Core_blake2b_params "key_length1" uint8_t
    let hacl_Impl_Blake2_Core_blake2b_params_fanout1 =
      field hacl_Impl_Blake2_Core_blake2b_params "fanout1" uint8_t
    let hacl_Impl_Blake2_Core_blake2b_params_depth1 =
      field hacl_Impl_Blake2_Core_blake2b_params "depth1" uint8_t
    let hacl_Impl_Blake2_Core_blake2b_params_leaf_length1 =
      field hacl_Impl_Blake2_Core_blake2b_params "leaf_length1" uint32_t
    let hacl_Impl_Blake2_Core_blake2b_params_node_offset1 =
      field hacl_Impl_Blake2_Core_blake2b_params "node_offset1" uint32_t
    let hacl_Impl_Blake2_Core_blake2b_params_xof_length1 =
      field hacl_Impl_Blake2_Core_blake2b_params "xof_length1" uint32_t
    let hacl_Impl_Blake2_Core_blake2b_params_node_depth1 =
      field hacl_Impl_Blake2_Core_blake2b_params "node_depth1" uint8_t
    let hacl_Impl_Blake2_Core_blake2b_params_inner_length1 =
      field hacl_Impl_Blake2_Core_blake2b_params "inner_length1" uint8_t
    let hacl_Impl_Blake2_Core_blake2b_params_salt1 =
      field hacl_Impl_Blake2_Core_blake2b_params "salt1" (ptr uint8_t)
    let hacl_Impl_Blake2_Core_blake2b_params_personal1 =
      field hacl_Impl_Blake2_Core_blake2b_params "personal1" (ptr uint8_t)
    let _ = seal hacl_Impl_Blake2_Core_blake2b_params
    let hacl_Blake2b_32_blake2b_init =
      foreign "Hacl_Blake2b_32_blake2b_init"
        ((ptr uint64_t) @-> (uint32_t @-> (uint32_t @-> (returning void))))
    let hacl_Blake2b_32_blake2b_update_key =
      foreign "Hacl_Blake2b_32_blake2b_update_key"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @->
              (uint32_t @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))))
    let hacl_Blake2b_32_blake2b_finish =
      foreign "Hacl_Blake2b_32_blake2b_finish"
        (uint32_t @-> (ocaml_bytes @-> ((ptr uint64_t) @-> (returning void))))
    let hacl_Blake2b_32_blake2b =
      foreign "Hacl_Blake2b_32_blake2b"
        (uint32_t @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (uint32_t @-> (ocaml_bytes @-> (returning void)))))))
    let hacl_Blake2b_32_blake2b_malloc =
      foreign "Hacl_Blake2b_32_blake2b_malloc"
        (void @-> (returning (ptr uint64_t)))
    let hacl_Blake2s_32_blake2s_init =
      foreign "Hacl_Blake2s_32_blake2s_init"
        ((ptr uint32_t) @-> (uint32_t @-> (uint32_t @-> (returning void))))
    let hacl_Blake2s_32_blake2s_update_key =
      foreign "Hacl_Blake2s_32_blake2s_update_key"
        ((ptr uint32_t) @->
           ((ptr uint32_t) @->
              (uint32_t @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))))
    let hacl_Blake2s_32_blake2s_update_multi =
      foreign "Hacl_Blake2s_32_blake2s_update_multi"
        (uint32_t @->
           ((ptr uint32_t) @->
              ((ptr uint32_t) @->
                 (uint64_t @->
                    (ocaml_bytes @-> (uint32_t @-> (returning void)))))))
    let hacl_Blake2s_32_blake2s_update_last =
      foreign "Hacl_Blake2s_32_blake2s_update_last"
        (uint32_t @->
           ((ptr uint32_t) @->
              ((ptr uint32_t) @->
                 (uint64_t @->
                    (uint32_t @-> (ocaml_bytes @-> (returning void)))))))
    let hacl_Blake2s_32_blake2s_finish =
      foreign "Hacl_Blake2s_32_blake2s_finish"
        (uint32_t @-> (ocaml_bytes @-> ((ptr uint32_t) @-> (returning void))))
    let hacl_Blake2s_32_blake2s =
      foreign "Hacl_Blake2s_32_blake2s"
        (uint32_t @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (uint32_t @-> (ocaml_bytes @-> (returning void)))))))
    let hacl_Blake2s_32_blake2s_malloc =
      foreign "Hacl_Blake2s_32_blake2s_malloc"
        (void @-> (returning (ptr uint32_t)))
  end