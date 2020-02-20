open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Hash_MD5_legacy_update_multi =
      foreign "Hacl_Hash_MD5_legacy_update_multi"
        ((ptr uint32_t) @->
           ((ptr uint8_t) @-> (uint32_t @-> (returning void))))
      
    let hacl_Hash_MD5_legacy_update_last =
      foreign "Hacl_Hash_MD5_legacy_update_last"
        ((ptr uint32_t) @->
           (uint64_t @-> ((ptr uint8_t) @-> (uint32_t @-> (returning void)))))
      
    let hacl_Hash_MD5_legacy_hash =
      foreign "Hacl_Hash_MD5_legacy_hash"
        ((ptr uint8_t) @->
           (uint32_t @-> ((ptr uint8_t) @-> (returning void))))
      
    let hacl_Hash_Core_MD5_legacy_init =
      foreign "Hacl_Hash_Core_MD5_legacy_init"
        ((ptr uint32_t) @-> (returning void))
      
    let hacl_Hash_Core_MD5_legacy_update =
      foreign "Hacl_Hash_Core_MD5_legacy_update"
        ((ptr uint32_t) @-> ((ptr uint8_t) @-> (returning void)))
      
    let hacl_Hash_Core_MD5_legacy_pad =
      foreign "Hacl_Hash_Core_MD5_legacy_pad"
        (uint64_t @-> ((ptr uint8_t) @-> (returning void)))
      
    let hacl_Hash_Core_MD5_legacy_finish =
      foreign "Hacl_Hash_Core_MD5_legacy_finish"
        ((ptr uint32_t) @-> ((ptr uint8_t) @-> (returning void)))
      
    let hacl_Hash_SHA1_legacy_update_multi =
      foreign "Hacl_Hash_SHA1_legacy_update_multi"
        ((ptr uint32_t) @->
           ((ptr uint8_t) @-> (uint32_t @-> (returning void))))
      
    let hacl_Hash_SHA1_legacy_update_last =
      foreign "Hacl_Hash_SHA1_legacy_update_last"
        ((ptr uint32_t) @->
           (uint64_t @-> ((ptr uint8_t) @-> (uint32_t @-> (returning void)))))
      
    let hacl_Hash_SHA1_legacy_hash =
      foreign "Hacl_Hash_SHA1_legacy_hash"
        ((ptr uint8_t) @->
           (uint32_t @-> ((ptr uint8_t) @-> (returning void))))
      
    let hacl_Hash_Core_SHA1_legacy_init =
      foreign "Hacl_Hash_Core_SHA1_legacy_init"
        ((ptr uint32_t) @-> (returning void))
      
    let hacl_Hash_Core_SHA1_legacy_update =
      foreign "Hacl_Hash_Core_SHA1_legacy_update"
        ((ptr uint32_t) @-> ((ptr uint8_t) @-> (returning void)))
      
    let hacl_Hash_Core_SHA1_legacy_pad =
      foreign "Hacl_Hash_Core_SHA1_legacy_pad"
        (uint64_t @-> ((ptr uint8_t) @-> (returning void)))
      
    let hacl_Hash_Core_SHA1_legacy_finish =
      foreign "Hacl_Hash_Core_SHA1_legacy_finish"
        ((ptr uint32_t) @-> ((ptr uint8_t) @-> (returning void)))
      
    let hacl_Hash_SHA2_update_multi_224 =
      foreign "Hacl_Hash_SHA2_update_multi_224"
        ((ptr uint32_t) @->
           ((ptr uint8_t) @-> (uint32_t @-> (returning void))))
      
    let hacl_Hash_SHA2_update_multi_256 =
      foreign "Hacl_Hash_SHA2_update_multi_256"
        ((ptr uint32_t) @->
           ((ptr uint8_t) @-> (uint32_t @-> (returning void))))
      
    let hacl_Hash_SHA2_update_multi_384 =
      foreign "Hacl_Hash_SHA2_update_multi_384"
        ((ptr uint64_t) @->
           ((ptr uint8_t) @-> (uint32_t @-> (returning void))))
      
    let hacl_Hash_SHA2_update_multi_512 =
      foreign "Hacl_Hash_SHA2_update_multi_512"
        ((ptr uint64_t) @->
           ((ptr uint8_t) @-> (uint32_t @-> (returning void))))
      
    let hacl_Hash_SHA2_update_last_224 =
      foreign "Hacl_Hash_SHA2_update_last_224"
        ((ptr uint32_t) @->
           (uint64_t @-> ((ptr uint8_t) @-> (uint32_t @-> (returning void)))))
      
    let hacl_Hash_SHA2_update_last_256 =
      foreign "Hacl_Hash_SHA2_update_last_256"
        ((ptr uint32_t) @->
           (uint64_t @-> ((ptr uint8_t) @-> (uint32_t @-> (returning void)))))
      
    let hacl_Hash_SHA2_hash_224 =
      foreign "Hacl_Hash_SHA2_hash_224"
        ((ptr uint8_t) @->
           (uint32_t @-> ((ptr uint8_t) @-> (returning void))))
      
    let hacl_Hash_SHA2_hash_256 =
      foreign "Hacl_Hash_SHA2_hash_256"
        ((ptr uint8_t) @->
           (uint32_t @-> ((ptr uint8_t) @-> (returning void))))
      
    let hacl_Hash_SHA2_hash_384 =
      foreign "Hacl_Hash_SHA2_hash_384"
        ((ptr uint8_t) @->
           (uint32_t @-> ((ptr uint8_t) @-> (returning void))))
      
    let hacl_Hash_SHA2_hash_512 =
      foreign "Hacl_Hash_SHA2_hash_512"
        ((ptr uint8_t) @->
           (uint32_t @-> ((ptr uint8_t) @-> (returning void))))
      
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
        ((ptr uint32_t) @-> ((ptr uint8_t) @-> (returning void)))
      
    let hacl_Hash_Core_SHA2_update_256 =
      foreign "Hacl_Hash_Core_SHA2_update_256"
        ((ptr uint32_t) @-> ((ptr uint8_t) @-> (returning void)))
      
    let hacl_Hash_Core_SHA2_update_384 =
      foreign "Hacl_Hash_Core_SHA2_update_384"
        ((ptr uint64_t) @-> ((ptr uint8_t) @-> (returning void)))
      
    let hacl_Hash_Core_SHA2_update_512 =
      foreign "Hacl_Hash_Core_SHA2_update_512"
        ((ptr uint64_t) @-> ((ptr uint8_t) @-> (returning void)))
      
    let hacl_Hash_Core_SHA2_pad_224 =
      foreign "Hacl_Hash_Core_SHA2_pad_224"
        (uint64_t @-> ((ptr uint8_t) @-> (returning void)))
      
    let hacl_Hash_Core_SHA2_pad_256 =
      foreign "Hacl_Hash_Core_SHA2_pad_256"
        (uint64_t @-> ((ptr uint8_t) @-> (returning void)))
      
    let hacl_Hash_Core_SHA2_finish_224 =
      foreign "Hacl_Hash_Core_SHA2_finish_224"
        ((ptr uint32_t) @-> ((ptr uint8_t) @-> (returning void)))
      
    let hacl_Hash_Core_SHA2_finish_256 =
      foreign "Hacl_Hash_Core_SHA2_finish_256"
        ((ptr uint32_t) @-> ((ptr uint8_t) @-> (returning void)))
      
    let hacl_Hash_Core_SHA2_finish_384 =
      foreign "Hacl_Hash_Core_SHA2_finish_384"
        ((ptr uint64_t) @-> ((ptr uint8_t) @-> (returning void)))
      
    let hacl_Hash_Core_SHA2_finish_512 =
      foreign "Hacl_Hash_Core_SHA2_finish_512"
        ((ptr uint64_t) @-> ((ptr uint8_t) @-> (returning void)))
      
  end