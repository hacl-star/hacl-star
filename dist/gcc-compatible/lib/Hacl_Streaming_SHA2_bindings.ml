open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    module Hacl_Streaming_Types_applied =
      (Hacl_Streaming_Types_bindings.Bindings)(Hacl_Streaming_Types_stubs)
    open Hacl_Streaming_Types_applied
    let hacl_SHA2_Scalar32_sha512_init =
      foreign "Hacl_SHA2_Scalar32_sha512_init"
        ((ptr uint64_t) @-> (returning void))
    type hacl_Streaming_SHA2_state_sha2_224 = hacl_Streaming_MD_state_32
    let hacl_Streaming_SHA2_state_sha2_224 =
      typedef hacl_Streaming_MD_state_32 "Hacl_Streaming_SHA2_state_sha2_224"
    type hacl_Streaming_SHA2_state_sha2_256 = hacl_Streaming_MD_state_32
    let hacl_Streaming_SHA2_state_sha2_256 =
      typedef hacl_Streaming_MD_state_32 "Hacl_Streaming_SHA2_state_sha2_256"
    type hacl_Streaming_SHA2_state_sha2_384 = hacl_Streaming_MD_state_64
    let hacl_Streaming_SHA2_state_sha2_384 =
      typedef hacl_Streaming_MD_state_64 "Hacl_Streaming_SHA2_state_sha2_384"
    type hacl_Streaming_SHA2_state_sha2_512 = hacl_Streaming_MD_state_64
    let hacl_Streaming_SHA2_state_sha2_512 =
      typedef hacl_Streaming_MD_state_64 "Hacl_Streaming_SHA2_state_sha2_512"
    let hacl_Streaming_SHA2_create_in_256 =
      foreign "Hacl_Streaming_SHA2_create_in_256"
        (void @-> (returning (ptr hacl_Streaming_MD_state_32)))
    let hacl_Streaming_SHA2_copy_256 =
      foreign "Hacl_Streaming_SHA2_copy_256"
        ((ptr hacl_Streaming_MD_state_32) @->
           (returning (ptr hacl_Streaming_MD_state_32)))
    let hacl_Streaming_SHA2_init_256 =
      foreign "Hacl_Streaming_SHA2_init_256"
        ((ptr hacl_Streaming_MD_state_32) @-> (returning void))
    let hacl_Streaming_SHA2_update_256 =
      foreign "Hacl_Streaming_SHA2_update_256"
        ((ptr hacl_Streaming_MD_state_32) @->
           (ocaml_bytes @-> (uint32_t @-> (returning uint32_t))))
    let hacl_Streaming_SHA2_finish_256 =
      foreign "Hacl_Streaming_SHA2_finish_256"
        ((ptr hacl_Streaming_MD_state_32) @->
           (ocaml_bytes @-> (returning void)))
    let hacl_Streaming_SHA2_free_256 =
      foreign "Hacl_Streaming_SHA2_free_256"
        ((ptr hacl_Streaming_MD_state_32) @-> (returning void))
    let hacl_Streaming_SHA2_sha256 =
      foreign "Hacl_Streaming_SHA2_sha256"
        (ocaml_bytes @-> (uint32_t @-> (ocaml_bytes @-> (returning void))))
    let hacl_Streaming_SHA2_create_in_224 =
      foreign "Hacl_Streaming_SHA2_create_in_224"
        (void @-> (returning (ptr hacl_Streaming_MD_state_32)))
    let hacl_Streaming_SHA2_init_224 =
      foreign "Hacl_Streaming_SHA2_init_224"
        ((ptr hacl_Streaming_MD_state_32) @-> (returning void))
    let hacl_Streaming_SHA2_update_224 =
      foreign "Hacl_Streaming_SHA2_update_224"
        ((ptr hacl_Streaming_MD_state_32) @->
           (ocaml_bytes @-> (uint32_t @-> (returning uint32_t))))
    let hacl_Streaming_SHA2_finish_224 =
      foreign "Hacl_Streaming_SHA2_finish_224"
        ((ptr hacl_Streaming_MD_state_32) @->
           (ocaml_bytes @-> (returning void)))
    let hacl_Streaming_SHA2_free_224 =
      foreign "Hacl_Streaming_SHA2_free_224"
        ((ptr hacl_Streaming_MD_state_32) @-> (returning void))
    let hacl_Streaming_SHA2_sha224 =
      foreign "Hacl_Streaming_SHA2_sha224"
        (ocaml_bytes @-> (uint32_t @-> (ocaml_bytes @-> (returning void))))
    let hacl_Streaming_SHA2_create_in_512 =
      foreign "Hacl_Streaming_SHA2_create_in_512"
        (void @-> (returning (ptr hacl_Streaming_MD_state_64)))
    let hacl_Streaming_SHA2_copy_512 =
      foreign "Hacl_Streaming_SHA2_copy_512"
        ((ptr hacl_Streaming_MD_state_64) @->
           (returning (ptr hacl_Streaming_MD_state_64)))
    let hacl_Streaming_SHA2_init_512 =
      foreign "Hacl_Streaming_SHA2_init_512"
        ((ptr hacl_Streaming_MD_state_64) @-> (returning void))
    let hacl_Streaming_SHA2_update_512 =
      foreign "Hacl_Streaming_SHA2_update_512"
        ((ptr hacl_Streaming_MD_state_64) @->
           (ocaml_bytes @-> (uint32_t @-> (returning uint32_t))))
    let hacl_Streaming_SHA2_finish_512 =
      foreign "Hacl_Streaming_SHA2_finish_512"
        ((ptr hacl_Streaming_MD_state_64) @->
           (ocaml_bytes @-> (returning void)))
    let hacl_Streaming_SHA2_free_512 =
      foreign "Hacl_Streaming_SHA2_free_512"
        ((ptr hacl_Streaming_MD_state_64) @-> (returning void))
    let hacl_Streaming_SHA2_sha512 =
      foreign "Hacl_Streaming_SHA2_sha512"
        (ocaml_bytes @-> (uint32_t @-> (ocaml_bytes @-> (returning void))))
    let hacl_Streaming_SHA2_create_in_384 =
      foreign "Hacl_Streaming_SHA2_create_in_384"
        (void @-> (returning (ptr hacl_Streaming_MD_state_64)))
    let hacl_Streaming_SHA2_init_384 =
      foreign "Hacl_Streaming_SHA2_init_384"
        ((ptr hacl_Streaming_MD_state_64) @-> (returning void))
    let hacl_Streaming_SHA2_update_384 =
      foreign "Hacl_Streaming_SHA2_update_384"
        ((ptr hacl_Streaming_MD_state_64) @->
           (ocaml_bytes @-> (uint32_t @-> (returning uint32_t))))
    let hacl_Streaming_SHA2_finish_384 =
      foreign "Hacl_Streaming_SHA2_finish_384"
        ((ptr hacl_Streaming_MD_state_64) @->
           (ocaml_bytes @-> (returning void)))
    let hacl_Streaming_SHA2_free_384 =
      foreign "Hacl_Streaming_SHA2_free_384"
        ((ptr hacl_Streaming_MD_state_64) @-> (returning void))
    let hacl_Streaming_SHA2_sha384 =
      foreign "Hacl_Streaming_SHA2_sha384"
        (ocaml_bytes @-> (uint32_t @-> (ocaml_bytes @-> (returning void))))
  end