open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    type hacl_Streaming_SHA2_state_sha2_224 =
      [ `hacl_Streaming_SHA2_state_sha2_224 ] structure
    let (hacl_Streaming_SHA2_state_sha2_224 :
      [ `hacl_Streaming_SHA2_state_sha2_224 ] structure typ) =
      structure "Hacl_Streaming_SHA2_state_sha2_224_s"
    let hacl_Streaming_SHA2_state_sha2_224_block_state =
      field hacl_Streaming_SHA2_state_sha2_224 "block_state" (ptr uint32_t)
    let hacl_Streaming_SHA2_state_sha2_224_buf =
      field hacl_Streaming_SHA2_state_sha2_224 "buf" (ptr uint8_t)
    let hacl_Streaming_SHA2_state_sha2_224_total_len =
      field hacl_Streaming_SHA2_state_sha2_224 "total_len" uint64_t
    let _ = seal hacl_Streaming_SHA2_state_sha2_224
    type hacl_Streaming_SHA2_state_sha2_256 =
      hacl_Streaming_SHA2_state_sha2_224
    let hacl_Streaming_SHA2_state_sha2_256 =
      typedef hacl_Streaming_SHA2_state_sha2_224
        "Hacl_Streaming_SHA2_state_sha2_256"
    type hacl_Streaming_SHA2_state_sha2_384 =
      [ `hacl_Streaming_SHA2_state_sha2_384 ] structure
    let (hacl_Streaming_SHA2_state_sha2_384 :
      [ `hacl_Streaming_SHA2_state_sha2_384 ] structure typ) =
      structure "Hacl_Streaming_SHA2_state_sha2_384_s"
    let hacl_Streaming_SHA2_state_sha2_384_block_state =
      field hacl_Streaming_SHA2_state_sha2_384 "block_state" (ptr uint64_t)
    let hacl_Streaming_SHA2_state_sha2_384_buf =
      field hacl_Streaming_SHA2_state_sha2_384 "buf" (ptr uint8_t)
    let hacl_Streaming_SHA2_state_sha2_384_total_len =
      field hacl_Streaming_SHA2_state_sha2_384 "total_len" uint64_t
    let _ = seal hacl_Streaming_SHA2_state_sha2_384
    type hacl_Streaming_SHA2_state_sha2_512 =
      hacl_Streaming_SHA2_state_sha2_384
    let hacl_Streaming_SHA2_state_sha2_512 =
      typedef hacl_Streaming_SHA2_state_sha2_384
        "Hacl_Streaming_SHA2_state_sha2_512"
    let hacl_Streaming_SHA2_create_in_224 =
      foreign "Hacl_Streaming_SHA2_create_in_224"
        (void @-> (returning (ptr hacl_Streaming_SHA2_state_sha2_224)))
    let hacl_Streaming_SHA2_init_224 =
      foreign "Hacl_Streaming_SHA2_init_224"
        ((ptr hacl_Streaming_SHA2_state_sha2_224) @-> (returning void))
    let hacl_Streaming_SHA2_update_224 =
      foreign "Hacl_Streaming_SHA2_update_224"
        ((ptr hacl_Streaming_SHA2_state_sha2_224) @->
           (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let hacl_Streaming_SHA2_finish_224 =
      foreign "Hacl_Streaming_SHA2_finish_224"
        ((ptr hacl_Streaming_SHA2_state_sha2_224) @->
           (ocaml_bytes @-> (returning void)))
    let hacl_Streaming_SHA2_free_224 =
      foreign "Hacl_Streaming_SHA2_free_224"
        ((ptr hacl_Streaming_SHA2_state_sha2_224) @-> (returning void))
    let hacl_Streaming_SHA2_create_in_256 =
      foreign "Hacl_Streaming_SHA2_create_in_256"
        (void @-> (returning (ptr hacl_Streaming_SHA2_state_sha2_224)))
    let hacl_Streaming_SHA2_init_256 =
      foreign "Hacl_Streaming_SHA2_init_256"
        ((ptr hacl_Streaming_SHA2_state_sha2_224) @-> (returning void))
    let hacl_Streaming_SHA2_update_256 =
      foreign "Hacl_Streaming_SHA2_update_256"
        ((ptr hacl_Streaming_SHA2_state_sha2_224) @->
           (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let hacl_Streaming_SHA2_finish_256 =
      foreign "Hacl_Streaming_SHA2_finish_256"
        ((ptr hacl_Streaming_SHA2_state_sha2_224) @->
           (ocaml_bytes @-> (returning void)))
    let hacl_Streaming_SHA2_free_256 =
      foreign "Hacl_Streaming_SHA2_free_256"
        ((ptr hacl_Streaming_SHA2_state_sha2_224) @-> (returning void))
    let hacl_Streaming_SHA2_create_in_384 =
      foreign "Hacl_Streaming_SHA2_create_in_384"
        (void @-> (returning (ptr hacl_Streaming_SHA2_state_sha2_384)))
    let hacl_Streaming_SHA2_init_384 =
      foreign "Hacl_Streaming_SHA2_init_384"
        ((ptr hacl_Streaming_SHA2_state_sha2_384) @-> (returning void))
    let hacl_Streaming_SHA2_update_384 =
      foreign "Hacl_Streaming_SHA2_update_384"
        ((ptr hacl_Streaming_SHA2_state_sha2_384) @->
           (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let hacl_Streaming_SHA2_finish_384 =
      foreign "Hacl_Streaming_SHA2_finish_384"
        ((ptr hacl_Streaming_SHA2_state_sha2_384) @->
           (ocaml_bytes @-> (returning void)))
    let hacl_Streaming_SHA2_free_384 =
      foreign "Hacl_Streaming_SHA2_free_384"
        ((ptr hacl_Streaming_SHA2_state_sha2_384) @-> (returning void))
    let hacl_Streaming_SHA2_create_in_512 =
      foreign "Hacl_Streaming_SHA2_create_in_512"
        (void @-> (returning (ptr hacl_Streaming_SHA2_state_sha2_384)))
    let hacl_Streaming_SHA2_init_512 =
      foreign "Hacl_Streaming_SHA2_init_512"
        ((ptr hacl_Streaming_SHA2_state_sha2_384) @-> (returning void))
    let hacl_Streaming_SHA2_update_512 =
      foreign "Hacl_Streaming_SHA2_update_512"
        ((ptr hacl_Streaming_SHA2_state_sha2_384) @->
           (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let hacl_Streaming_SHA2_finish_512 =
      foreign "Hacl_Streaming_SHA2_finish_512"
        ((ptr hacl_Streaming_SHA2_state_sha2_384) @->
           (ocaml_bytes @-> (returning void)))
    let hacl_Streaming_SHA2_free_512 =
      foreign "Hacl_Streaming_SHA2_free_512"
        ((ptr hacl_Streaming_SHA2_state_sha2_384) @-> (returning void))
  end