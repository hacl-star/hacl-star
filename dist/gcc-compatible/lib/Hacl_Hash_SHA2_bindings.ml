open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    module Hacl_Streaming_Types_applied =
      (Hacl_Streaming_Types_bindings.Bindings)(Hacl_Streaming_Types_stubs)
    open Hacl_Streaming_Types_applied
    let hacl_Hash_SHA2_sha256_init =
      foreign "Hacl_Hash_SHA2_sha256_init"
        ((ptr uint32_t) @-> (returning void))
    let hacl_Hash_SHA2_sha256_update_nblocks =
      foreign "Hacl_Hash_SHA2_sha256_update_nblocks"
        (uint32_t @-> (ocaml_bytes @-> ((ptr uint32_t) @-> (returning void))))
    let hacl_Hash_SHA2_sha256_update_last =
      foreign "Hacl_Hash_SHA2_sha256_update_last"
        (uint64_t @->
           (uint32_t @->
              (ocaml_bytes @-> ((ptr uint32_t) @-> (returning void)))))
    let hacl_Hash_SHA2_sha256_finish =
      foreign "Hacl_Hash_SHA2_sha256_finish"
        ((ptr uint32_t) @-> (ocaml_bytes @-> (returning void)))
    let hacl_Hash_SHA2_sha224_init =
      foreign "Hacl_Hash_SHA2_sha224_init"
        ((ptr uint32_t) @-> (returning void))
    let hacl_Hash_SHA2_sha224_update_last =
      foreign "Hacl_Hash_SHA2_sha224_update_last"
        (uint64_t @->
           (uint32_t @->
              (ocaml_bytes @-> ((ptr uint32_t) @-> (returning void)))))
    let hacl_Hash_SHA2_sha224_finish =
      foreign "Hacl_Hash_SHA2_sha224_finish"
        ((ptr uint32_t) @-> (ocaml_bytes @-> (returning void)))
    let hacl_Hash_SHA2_sha512_init =
      foreign "Hacl_Hash_SHA2_sha512_init"
        ((ptr uint64_t) @-> (returning void))
    let hacl_Hash_SHA2_sha512_update_nblocks =
      foreign "Hacl_Hash_SHA2_sha512_update_nblocks"
        (uint32_t @-> (ocaml_bytes @-> ((ptr uint64_t) @-> (returning void))))
    let hacl_Hash_SHA2_sha512_finish =
      foreign "Hacl_Hash_SHA2_sha512_finish"
        ((ptr uint64_t) @-> (ocaml_bytes @-> (returning void)))
    let hacl_Hash_SHA2_sha384_init =
      foreign "Hacl_Hash_SHA2_sha384_init"
        ((ptr uint64_t) @-> (returning void))
    let hacl_Hash_SHA2_sha384_update_nblocks =
      foreign "Hacl_Hash_SHA2_sha384_update_nblocks"
        (uint32_t @-> (ocaml_bytes @-> ((ptr uint64_t) @-> (returning void))))
    let hacl_Hash_SHA2_sha384_finish =
      foreign "Hacl_Hash_SHA2_sha384_finish"
        ((ptr uint64_t) @-> (ocaml_bytes @-> (returning void)))
    type hacl_Hash_SHA2_state_sha2_224 = hacl_Streaming_MD_state_32
    let hacl_Hash_SHA2_state_sha2_224 =
      typedef hacl_Streaming_MD_state_32 "Hacl_Hash_SHA2_state_sha2_224"
    type hacl_Hash_SHA2_state_sha2_256 = hacl_Streaming_MD_state_32
    let hacl_Hash_SHA2_state_sha2_256 =
      typedef hacl_Streaming_MD_state_32 "Hacl_Hash_SHA2_state_sha2_256"
    type hacl_Hash_SHA2_state_sha2_384 = hacl_Streaming_MD_state_64
    let hacl_Hash_SHA2_state_sha2_384 =
      typedef hacl_Streaming_MD_state_64 "Hacl_Hash_SHA2_state_sha2_384"
    type hacl_Hash_SHA2_state_sha2_512 = hacl_Streaming_MD_state_64
    let hacl_Hash_SHA2_state_sha2_512 =
      typedef hacl_Streaming_MD_state_64 "Hacl_Hash_SHA2_state_sha2_512"
    let hacl_Hash_SHA2_malloc_256 =
      foreign "Hacl_Hash_SHA2_malloc_256"
        (void @-> (returning (ptr hacl_Streaming_MD_state_32)))
    let hacl_Hash_SHA2_copy_256 =
      foreign "Hacl_Hash_SHA2_copy_256"
        ((ptr hacl_Streaming_MD_state_32) @->
           (returning (ptr hacl_Streaming_MD_state_32)))
    let hacl_Hash_SHA2_reset_256 =
      foreign "Hacl_Hash_SHA2_reset_256"
        ((ptr hacl_Streaming_MD_state_32) @-> (returning void))
    let hacl_Hash_SHA2_update_256 =
      foreign "Hacl_Hash_SHA2_update_256"
        ((ptr hacl_Streaming_MD_state_32) @->
           (ocaml_bytes @->
              (uint32_t @-> (returning hacl_Streaming_Types_error_code))))
    let hacl_Hash_SHA2_digest_256 =
      foreign "Hacl_Hash_SHA2_digest_256"
        ((ptr hacl_Streaming_MD_state_32) @->
           (ocaml_bytes @-> (returning void)))
    let hacl_Hash_SHA2_free_256 =
      foreign "Hacl_Hash_SHA2_free_256"
        ((ptr hacl_Streaming_MD_state_32) @-> (returning void))
    let hacl_Hash_SHA2_hash_256 =
      foreign "Hacl_Hash_SHA2_hash_256"
        (ocaml_bytes @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let hacl_Hash_SHA2_malloc_224 =
      foreign "Hacl_Hash_SHA2_malloc_224"
        (void @-> (returning (ptr hacl_Streaming_MD_state_32)))
    let hacl_Hash_SHA2_reset_224 =
      foreign "Hacl_Hash_SHA2_reset_224"
        ((ptr hacl_Streaming_MD_state_32) @-> (returning void))
    let hacl_Hash_SHA2_update_224 =
      foreign "Hacl_Hash_SHA2_update_224"
        ((ptr hacl_Streaming_MD_state_32) @->
           (ocaml_bytes @->
              (uint32_t @-> (returning hacl_Streaming_Types_error_code))))
    let hacl_Hash_SHA2_digest_224 =
      foreign "Hacl_Hash_SHA2_digest_224"
        ((ptr hacl_Streaming_MD_state_32) @->
           (ocaml_bytes @-> (returning void)))
    let hacl_Hash_SHA2_free_224 =
      foreign "Hacl_Hash_SHA2_free_224"
        ((ptr hacl_Streaming_MD_state_32) @-> (returning void))
    let hacl_Hash_SHA2_hash_224 =
      foreign "Hacl_Hash_SHA2_hash_224"
        (ocaml_bytes @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let hacl_Hash_SHA2_malloc_512 =
      foreign "Hacl_Hash_SHA2_malloc_512"
        (void @-> (returning (ptr hacl_Streaming_MD_state_64)))
    let hacl_Hash_SHA2_copy_512 =
      foreign "Hacl_Hash_SHA2_copy_512"
        ((ptr hacl_Streaming_MD_state_64) @->
           (returning (ptr hacl_Streaming_MD_state_64)))
    let hacl_Hash_SHA2_reset_512 =
      foreign "Hacl_Hash_SHA2_reset_512"
        ((ptr hacl_Streaming_MD_state_64) @-> (returning void))
    let hacl_Hash_SHA2_update_512 =
      foreign "Hacl_Hash_SHA2_update_512"
        ((ptr hacl_Streaming_MD_state_64) @->
           (ocaml_bytes @->
              (uint32_t @-> (returning hacl_Streaming_Types_error_code))))
    let hacl_Hash_SHA2_digest_512 =
      foreign "Hacl_Hash_SHA2_digest_512"
        ((ptr hacl_Streaming_MD_state_64) @->
           (ocaml_bytes @-> (returning void)))
    let hacl_Hash_SHA2_free_512 =
      foreign "Hacl_Hash_SHA2_free_512"
        ((ptr hacl_Streaming_MD_state_64) @-> (returning void))
    let hacl_Hash_SHA2_hash_512 =
      foreign "Hacl_Hash_SHA2_hash_512"
        (ocaml_bytes @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let hacl_Hash_SHA2_malloc_384 =
      foreign "Hacl_Hash_SHA2_malloc_384"
        (void @-> (returning (ptr hacl_Streaming_MD_state_64)))
    let hacl_Hash_SHA2_reset_384 =
      foreign "Hacl_Hash_SHA2_reset_384"
        ((ptr hacl_Streaming_MD_state_64) @-> (returning void))
    let hacl_Hash_SHA2_update_384 =
      foreign "Hacl_Hash_SHA2_update_384"
        ((ptr hacl_Streaming_MD_state_64) @->
           (ocaml_bytes @->
              (uint32_t @-> (returning hacl_Streaming_Types_error_code))))
    let hacl_Hash_SHA2_digest_384 =
      foreign "Hacl_Hash_SHA2_digest_384"
        ((ptr hacl_Streaming_MD_state_64) @->
           (ocaml_bytes @-> (returning void)))
    let hacl_Hash_SHA2_free_384 =
      foreign "Hacl_Hash_SHA2_free_384"
        ((ptr hacl_Streaming_MD_state_64) @-> (returning void))
    let hacl_Hash_SHA2_hash_384 =
      foreign "Hacl_Hash_SHA2_hash_384"
        (ocaml_bytes @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))
  end