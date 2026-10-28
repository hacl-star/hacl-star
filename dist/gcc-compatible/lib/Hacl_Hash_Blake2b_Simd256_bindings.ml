open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    module Hacl_Streaming_Types_applied =
      (Hacl_Streaming_Types_bindings.Bindings)(Hacl_Streaming_Types_stubs)
    open Hacl_Streaming_Types_applied
    module Hacl_Hash_Blake2b_applied =
      (Hacl_Hash_Blake2b_bindings.Bindings)(Hacl_Hash_Blake2b_stubs)
    open Hacl_Hash_Blake2b_applied
    type hacl_Hash_Blake2b_Simd256_state_t =
      [ `hacl_Hash_Blake2b_Simd256_state_t ] structure
    let (hacl_Hash_Blake2b_Simd256_state_t :
      [ `hacl_Hash_Blake2b_Simd256_state_t ] structure typ) =
      structure "Hacl_Hash_Blake2b_Simd256_state_t_s"
    let hacl_Hash_Blake2b_Simd256_malloc_with_params_and_key =
      foreign "Hacl_Hash_Blake2b_Simd256_malloc_with_params_and_key"
        ((ptr hacl_Hash_Blake2b_blake2_params) @->
           (bool @->
              (ocaml_bytes @->
                 (returning (ptr hacl_Hash_Blake2b_Simd256_state_t)))))
    let hacl_Hash_Blake2b_Simd256_malloc_with_key =
      foreign "Hacl_Hash_Blake2b_Simd256_malloc_with_key"
        (ocaml_bytes @->
           (uint8_t @-> (returning (ptr hacl_Hash_Blake2b_Simd256_state_t))))
    let hacl_Hash_Blake2b_Simd256_malloc =
      foreign "Hacl_Hash_Blake2b_Simd256_malloc"
        (void @-> (returning (ptr hacl_Hash_Blake2b_Simd256_state_t)))
    let hacl_Hash_Blake2b_Simd256_reset_with_key_and_params =
      foreign "Hacl_Hash_Blake2b_Simd256_reset_with_key_and_params"
        ((ptr hacl_Hash_Blake2b_Simd256_state_t) @->
           ((ptr hacl_Hash_Blake2b_blake2_params) @->
              (ocaml_bytes @-> (returning void))))
    let hacl_Hash_Blake2b_Simd256_reset_with_key =
      foreign "Hacl_Hash_Blake2b_Simd256_reset_with_key"
        ((ptr hacl_Hash_Blake2b_Simd256_state_t) @->
           (ocaml_bytes @-> (returning void)))
    let hacl_Hash_Blake2b_Simd256_reset =
      foreign "Hacl_Hash_Blake2b_Simd256_reset"
        ((ptr hacl_Hash_Blake2b_Simd256_state_t) @-> (returning void))
    let hacl_Hash_Blake2b_Simd256_update =
      foreign "Hacl_Hash_Blake2b_Simd256_update"
        ((ptr hacl_Hash_Blake2b_Simd256_state_t) @->
           (ocaml_bytes @->
              (uint32_t @-> (returning hacl_Streaming_Types_error_code))))
    let hacl_Hash_Blake2b_Simd256_digest =
      foreign "Hacl_Hash_Blake2b_Simd256_digest"
        ((ptr hacl_Hash_Blake2b_Simd256_state_t) @->
           (ocaml_bytes @-> (returning uint8_t)))
    let hacl_Hash_Blake2b_Simd256_info =
      foreign "Hacl_Hash_Blake2b_Simd256_info"
        ((ptr hacl_Hash_Blake2b_Simd256_state_t) @->
           (returning hacl_Hash_Blake2b_index))
    let hacl_Hash_Blake2b_Simd256_free =
      foreign "Hacl_Hash_Blake2b_Simd256_free"
        ((ptr hacl_Hash_Blake2b_Simd256_state_t) @-> (returning void))
    let hacl_Hash_Blake2b_Simd256_copy =
      foreign "Hacl_Hash_Blake2b_Simd256_copy"
        ((ptr hacl_Hash_Blake2b_Simd256_state_t) @->
           (returning (ptr hacl_Hash_Blake2b_Simd256_state_t)))
    let hacl_Hash_Blake2b_Simd256_hash_with_key =
      foreign "Hacl_Hash_Blake2b_Simd256_hash_with_key"
        (ocaml_bytes @->
           (uint32_t @->
              (ocaml_bytes @->
                 (uint32_t @->
                    (ocaml_bytes @-> (uint32_t @-> (returning void)))))))
    let hacl_Hash_Blake2b_Simd256_hash_with_key_and_params =
      foreign "Hacl_Hash_Blake2b_Simd256_hash_with_key_and_params"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @->
                 (hacl_Hash_Blake2b_blake2_params @->
                    (ocaml_bytes @-> (returning void))))))
  end