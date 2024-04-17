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
    let hacl_Hash_Blake2b_Simd256_hash_with_key =
      foreign "Hacl_Hash_Blake2b_Simd256_hash_with_key"
        (ocaml_bytes @->
           (uint32_t @->
              (ocaml_bytes @->
                 (uint32_t @->
                    (ocaml_bytes @-> (uint32_t @-> (returning void)))))))
    let hacl_Hash_Blake2b_Simd256_hash_with_key_and_paramas =
      foreign "Hacl_Hash_Blake2b_Simd256_hash_with_key_and_paramas"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @->
                 (hacl_Hash_Blake2b_blake2_params @->
                    (ocaml_bytes @-> (returning void))))))
  end