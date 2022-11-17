open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    module Hacl_Spec_applied = (Hacl_Spec_bindings.Bindings)(Hacl_Spec_stubs)
    open Hacl_Spec_applied
    let hacl_Hash_Core_Blake2_init_blake2s_32 =
      foreign "Hacl_Hash_Core_Blake2_init_blake2s_32"
        ((ptr uint32_t) @-> (returning uint64_t))
    let hacl_Hash_Core_Blake2_update_blake2s_32 =
      foreign "Hacl_Hash_Core_Blake2_update_blake2s_32"
        ((ptr uint32_t) @->
           (uint64_t @-> (ocaml_bytes @-> (returning uint64_t))))
    let hacl_Hash_Core_Blake2_finish_blake2s_32 =
      foreign "Hacl_Hash_Core_Blake2_finish_blake2s_32"
        ((ptr uint32_t) @-> (uint64_t @-> (ocaml_bytes @-> (returning void))))
    let hacl_Hash_Blake2_update_multi_blake2s_32 =
      foreign "Hacl_Hash_Blake2_update_multi_blake2s_32"
        ((ptr uint32_t) @->
           (uint64_t @->
              (ocaml_bytes @-> (uint32_t @-> (returning uint64_t)))))
    let hacl_Hash_Blake2_update_last_blake2s_32 =
      foreign "Hacl_Hash_Blake2_update_last_blake2s_32"
        ((ptr uint32_t) @->
           (uint64_t @->
              (uint64_t @->
                 (ocaml_bytes @-> (uint32_t @-> (returning uint64_t))))))
    let hacl_Hash_Blake2_hash_blake2s_32 =
      foreign "Hacl_Hash_Blake2_hash_blake2s_32"
        (ocaml_bytes @-> (uint32_t @-> (ocaml_bytes @-> (returning void))))
    let hacl_Hash_Blake2_hash_blake2b_32 =
      foreign "Hacl_Hash_Blake2_hash_blake2b_32"
        (ocaml_bytes @-> (uint32_t @-> (ocaml_bytes @-> (returning void))))
    let hacl_Hash_Definitions_word_len =
      foreign "Hacl_Hash_Definitions_word_len"
        (spec_Hash_Definitions_hash_alg @-> (returning uint32_t))
    let hacl_Hash_Definitions_block_len =
      foreign "Hacl_Hash_Definitions_block_len"
        (spec_Hash_Definitions_hash_alg @-> (returning uint32_t))
    let hacl_Hash_Definitions_hash_word_len =
      foreign "Hacl_Hash_Definitions_hash_word_len"
        (spec_Hash_Definitions_hash_alg @-> (returning uint32_t))
    let hacl_Hash_Definitions_hash_len =
      foreign "Hacl_Hash_Definitions_hash_len"
        (spec_Hash_Definitions_hash_alg @-> (returning uint32_t))
  end