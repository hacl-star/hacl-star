open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    module Hacl_Spec_applied = (Hacl_Spec_bindings.Bindings)(Hacl_Spec_stubs)
    open Hacl_Spec_applied
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
    let hacl_Hash_MD5_legacy_update_multi =
      foreign "Hacl_Hash_MD5_legacy_update_multi"
        ((ptr uint32_t) @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let hacl_Hash_MD5_legacy_update_last =
      foreign "Hacl_Hash_MD5_legacy_update_last"
        ((ptr uint32_t) @->
           (uint64_t @-> (ocaml_bytes @-> (uint32_t @-> (returning void)))))
    let hacl_Hash_MD5_legacy_hash =
      foreign "Hacl_Hash_MD5_legacy_hash"
        (ocaml_bytes @-> (uint32_t @-> (ocaml_bytes @-> (returning void))))
    let hacl_Hash_Core_MD5_legacy_init =
      foreign "Hacl_Hash_Core_MD5_legacy_init"
        ((ptr uint32_t) @-> (returning void))
    let hacl_Hash_Core_MD5_legacy_update =
      foreign "Hacl_Hash_Core_MD5_legacy_update"
        ((ptr uint32_t) @-> (ocaml_bytes @-> (returning void)))
    let hacl_Hash_Core_MD5_legacy_pad =
      foreign "Hacl_Hash_Core_MD5_legacy_pad"
        (uint64_t @-> (ocaml_bytes @-> (returning void)))
    let hacl_Hash_Core_MD5_legacy_finish =
      foreign "Hacl_Hash_Core_MD5_legacy_finish"
        ((ptr uint32_t) @-> (ocaml_bytes @-> (returning void)))
    let hacl_Hash_SHA1_legacy_update_multi =
      foreign "Hacl_Hash_SHA1_legacy_update_multi"
        ((ptr uint32_t) @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let hacl_Hash_SHA1_legacy_update_last =
      foreign "Hacl_Hash_SHA1_legacy_update_last"
        ((ptr uint32_t) @->
           (uint64_t @-> (ocaml_bytes @-> (uint32_t @-> (returning void)))))
    let hacl_Hash_SHA1_legacy_hash =
      foreign "Hacl_Hash_SHA1_legacy_hash"
        (ocaml_bytes @-> (uint32_t @-> (ocaml_bytes @-> (returning void))))
    let hacl_Hash_Core_SHA1_legacy_init =
      foreign "Hacl_Hash_Core_SHA1_legacy_init"
        ((ptr uint32_t) @-> (returning void))
    let hacl_Hash_Core_SHA1_legacy_update =
      foreign "Hacl_Hash_Core_SHA1_legacy_update"
        ((ptr uint32_t) @-> (ocaml_bytes @-> (returning void)))
    let hacl_Hash_Core_SHA1_legacy_pad =
      foreign "Hacl_Hash_Core_SHA1_legacy_pad"
        (uint64_t @-> (ocaml_bytes @-> (returning void)))
    let hacl_Hash_Core_SHA1_legacy_finish =
      foreign "Hacl_Hash_Core_SHA1_legacy_finish"
        ((ptr uint32_t) @-> (ocaml_bytes @-> (returning void)))
    let hacl_Hash_SHA2_update_multi_224 =
      foreign "Hacl_Hash_SHA2_update_multi_224"
        ((ptr uint32_t) @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let hacl_Hash_SHA2_update_multi_256 =
      foreign "Hacl_Hash_SHA2_update_multi_256"
        ((ptr uint32_t) @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let hacl_Hash_SHA2_update_multi_384 =
      foreign "Hacl_Hash_SHA2_update_multi_384"
        ((ptr uint64_t) @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let hacl_Hash_SHA2_update_multi_512 =
      foreign "Hacl_Hash_SHA2_update_multi_512"
        ((ptr uint64_t) @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let hacl_Hash_SHA2_update_last_224 =
      foreign "Hacl_Hash_SHA2_update_last_224"
        ((ptr uint32_t) @->
           (uint64_t @-> (ocaml_bytes @-> (uint32_t @-> (returning void)))))
    let hacl_Hash_SHA2_update_last_256 =
      foreign "Hacl_Hash_SHA2_update_last_256"
        ((ptr uint32_t) @->
           (uint64_t @-> (ocaml_bytes @-> (uint32_t @-> (returning void)))))
    let hacl_Hash_SHA2_hash_224 =
      foreign "Hacl_Hash_SHA2_hash_224"
        (ocaml_bytes @-> (uint32_t @-> (ocaml_bytes @-> (returning void))))
    let hacl_Hash_SHA2_hash_256 =
      foreign "Hacl_Hash_SHA2_hash_256"
        (ocaml_bytes @-> (uint32_t @-> (ocaml_bytes @-> (returning void))))
    let hacl_Hash_SHA2_hash_384 =
      foreign "Hacl_Hash_SHA2_hash_384"
        (ocaml_bytes @-> (uint32_t @-> (ocaml_bytes @-> (returning void))))
    let hacl_Hash_SHA2_hash_512 =
      foreign "Hacl_Hash_SHA2_hash_512"
        (ocaml_bytes @-> (uint32_t @-> (ocaml_bytes @-> (returning void))))
    let hacl_Hash_Core_SHA2_init_224 =
      foreign "Hacl_Hash_Core_SHA2_init_224"
        ((ptr uint32_t) @-> (returning void))
    let hacl_Hash_Core_SHA2_init_256 =
      foreign "Hacl_Hash_Core_SHA2_init_256"
        ((ptr uint32_t) @-> (returning void))
    let hacl_Hash_Core_SHA2_init_384 =
      foreign "Hacl_Hash_Core_SHA2_init_384"
        ((ptr uint64_t) @-> (returning void))
    let hacl_Hash_Core_SHA2_init_512 =
      foreign "Hacl_Hash_Core_SHA2_init_512"
        ((ptr uint64_t) @-> (returning void))
    let hacl_Hash_Core_SHA2_update_224 =
      foreign "Hacl_Hash_Core_SHA2_update_224"
        ((ptr uint32_t) @-> (ocaml_bytes @-> (returning void)))
    let hacl_Hash_Core_SHA2_update_256 =
      foreign "Hacl_Hash_Core_SHA2_update_256"
        ((ptr uint32_t) @-> (ocaml_bytes @-> (returning void)))
    let hacl_Hash_Core_SHA2_update_384 =
      foreign "Hacl_Hash_Core_SHA2_update_384"
        ((ptr uint64_t) @-> (ocaml_bytes @-> (returning void)))
    let hacl_Hash_Core_SHA2_update_512 =
      foreign "Hacl_Hash_Core_SHA2_update_512"
        ((ptr uint64_t) @-> (ocaml_bytes @-> (returning void)))
    let hacl_Hash_Core_SHA2_pad_224 =
      foreign "Hacl_Hash_Core_SHA2_pad_224"
        (uint64_t @-> (ocaml_bytes @-> (returning void)))
    let hacl_Hash_Core_SHA2_pad_256 =
      foreign "Hacl_Hash_Core_SHA2_pad_256"
        (uint64_t @-> (ocaml_bytes @-> (returning void)))
    let hacl_Hash_Core_SHA2_finish_224 =
      foreign "Hacl_Hash_Core_SHA2_finish_224"
        ((ptr uint32_t) @-> (ocaml_bytes @-> (returning void)))
    let hacl_Hash_Core_SHA2_finish_256 =
      foreign "Hacl_Hash_Core_SHA2_finish_256"
        ((ptr uint32_t) @-> (ocaml_bytes @-> (returning void)))
    let hacl_Hash_Core_SHA2_finish_384 =
      foreign "Hacl_Hash_Core_SHA2_finish_384"
        ((ptr uint64_t) @-> (ocaml_bytes @-> (returning void)))
    let hacl_Hash_Core_SHA2_finish_512 =
      foreign "Hacl_Hash_Core_SHA2_finish_512"
        ((ptr uint64_t) @-> (ocaml_bytes @-> (returning void)))
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