open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    module Hacl_Spec_applied = (Hacl_Spec_bindings.Bindings)(Hacl_Spec_stubs)
    open Hacl_Spec_applied
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
      
    let hacl_P256_update_multi_224 =
      foreign "Hacl_P256_update_multi_224"
        ((ptr uint32_t) @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))
      
    let hacl_P256_update_multi_256 =
      foreign "Hacl_P256_update_multi_256"
        ((ptr uint32_t) @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))
      
    let hacl_P256_update_multi_384 =
      foreign "Hacl_P256_update_multi_384"
        ((ptr uint64_t) @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))
      
    let hacl_P256_update_multi_512 =
      foreign "Hacl_P256_update_multi_512"
        ((ptr uint64_t) @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))
      
    let hacl_P256_update_last_224 =
      foreign "Hacl_P256_update_last_224"
        ((ptr uint32_t) @->
           (uint64_t @-> (ocaml_bytes @-> (uint32_t @-> (returning void)))))
      
    let hacl_P256_update_last_256 =
      foreign "Hacl_P256_update_last_256"
        ((ptr uint32_t) @->
           (uint64_t @-> (ocaml_bytes @-> (uint32_t @-> (returning void)))))
      
    let hacl_P256_hash_224 =
      foreign "Hacl_P256_hash_224"
        (ocaml_bytes @-> (uint32_t @-> (ocaml_bytes @-> (returning void))))
      
    let hacl_P256_hash_256 =
      foreign "Hacl_P256_hash_256"
        (ocaml_bytes @-> (uint32_t @-> (ocaml_bytes @-> (returning void))))
      
    let hacl_P256_hash_384 =
      foreign "Hacl_P256_hash_384"
        (ocaml_bytes @-> (uint32_t @-> (ocaml_bytes @-> (returning void))))
      
    let hacl_P256_hash_512 =
      foreign "Hacl_P256_hash_512"
        (ocaml_bytes @-> (uint32_t @-> (ocaml_bytes @-> (returning void))))
      
    let hacl_P256_init_224 =
      foreign "Hacl_P256_init_224" ((ptr uint32_t) @-> (returning void)) 
    let hacl_P256_init_256 =
      foreign "Hacl_P256_init_256" ((ptr uint32_t) @-> (returning void)) 
    let hacl_P256_init_384 =
      foreign "Hacl_P256_init_384" ((ptr uint64_t) @-> (returning void)) 
    let hacl_P256_init_512 =
      foreign "Hacl_P256_init_512" ((ptr uint64_t) @-> (returning void)) 
    let hacl_P256_update_224 =
      foreign "Hacl_P256_update_224"
        ((ptr uint32_t) @-> (ocaml_bytes @-> (returning void)))
      
    let hacl_P256_update_256 =
      foreign "Hacl_P256_update_256"
        ((ptr uint32_t) @-> (ocaml_bytes @-> (returning void)))
      
    let hacl_P256_update_384 =
      foreign "Hacl_P256_update_384"
        ((ptr uint64_t) @-> (ocaml_bytes @-> (returning void)))
      
    let hacl_P256_update_512 =
      foreign "Hacl_P256_update_512"
        ((ptr uint64_t) @-> (ocaml_bytes @-> (returning void)))
      
    let hacl_P256_pad_224 =
      foreign "Hacl_P256_pad_224"
        (uint64_t @-> (ocaml_bytes @-> (returning void)))
      
    let hacl_P256_pad_256 =
      foreign "Hacl_P256_pad_256"
        (uint64_t @-> (ocaml_bytes @-> (returning void)))
      
    let hacl_P256_finish_224 =
      foreign "Hacl_P256_finish_224"
        ((ptr uint32_t) @-> (ocaml_bytes @-> (returning void)))
      
    let hacl_P256_finish_256 =
      foreign "Hacl_P256_finish_256"
        ((ptr uint32_t) @-> (ocaml_bytes @-> (returning void)))
      
    let hacl_P256_finish_384 =
      foreign "Hacl_P256_finish_384"
        ((ptr uint64_t) @-> (ocaml_bytes @-> (returning void)))
      
    let hacl_P256_finish_512 =
      foreign "Hacl_P256_finish_512"
        ((ptr uint64_t) @-> (ocaml_bytes @-> (returning void)))
      
    let hacl_P256_word_len =
      foreign "Hacl_P256_word_len"
        (spec_Hash_Definitions_hash_alg @-> (returning uint32_t))
      
    let hacl_P256_block_len =
      foreign "Hacl_P256_block_len"
        (spec_Hash_Definitions_hash_alg @-> (returning uint32_t))
      
    let hacl_P256_hash_word_len =
      foreign "Hacl_P256_hash_word_len"
        (spec_Hash_Definitions_hash_alg @-> (returning uint32_t))
      
    let hacl_P256_hash_len =
      foreign "Hacl_P256_hash_len"
        (spec_Hash_Definitions_hash_alg @-> (returning uint32_t))
      
  end