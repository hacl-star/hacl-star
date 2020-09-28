open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    type hacl_Streaming_Functor_state_s___uint32_t____ =
      [ `hacl_Streaming_Functor_state_s___uint32_t____ ] structure
    let (hacl_Streaming_Functor_state_s___uint32_t____ :
      [ `hacl_Streaming_Functor_state_s___uint32_t____ ] structure typ) =
      structure "Hacl_Streaming_Functor_state_s___uint32_t_____s"
    let hacl_Streaming_Functor_state_s___uint32_t_____block_state =
      field hacl_Streaming_Functor_state_s___uint32_t____ "block_state"
        (ptr uint32_t)
    let hacl_Streaming_Functor_state_s___uint32_t_____buf =
      field hacl_Streaming_Functor_state_s___uint32_t____ "buf" (ptr uint8_t)
    let hacl_Streaming_Functor_state_s___uint32_t_____total_len =
      field hacl_Streaming_Functor_state_s___uint32_t____ "total_len"
        uint64_t
    let _ = seal hacl_Streaming_Functor_state_s___uint32_t____
    let hacl_Streaming_SHA2_create_in_224 =
      foreign "Hacl_Streaming_SHA2_create_in_224"
        (void @->
           (returning (ptr hacl_Streaming_Functor_state_s___uint32_t____)))
    let hacl_Streaming_SHA2_init_224 =
      foreign "Hacl_Streaming_SHA2_init_224"
        ((ptr hacl_Streaming_Functor_state_s___uint32_t____) @->
           (returning void))
    let hacl_Streaming_SHA2_update_224 =
      foreign "Hacl_Streaming_SHA2_update_224"
        ((ptr hacl_Streaming_Functor_state_s___uint32_t____) @->
           (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let hacl_Streaming_SHA2_finish_224 =
      foreign "Hacl_Streaming_SHA2_finish_224"
        ((ptr hacl_Streaming_Functor_state_s___uint32_t____) @->
           (ocaml_bytes @-> (returning void)))
    let hacl_Streaming_SHA2_free_224 =
      foreign "Hacl_Streaming_SHA2_free_224"
        ((ptr hacl_Streaming_Functor_state_s___uint32_t____) @->
           (returning void))
    let hacl_Streaming_SHA2_create_in_256 =
      foreign "Hacl_Streaming_SHA2_create_in_256"
        (void @->
           (returning (ptr hacl_Streaming_Functor_state_s___uint32_t____)))
    let hacl_Streaming_SHA2_init_256 =
      foreign "Hacl_Streaming_SHA2_init_256"
        ((ptr hacl_Streaming_Functor_state_s___uint32_t____) @->
           (returning void))
    let hacl_Streaming_SHA2_update_256 =
      foreign "Hacl_Streaming_SHA2_update_256"
        ((ptr hacl_Streaming_Functor_state_s___uint32_t____) @->
           (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let hacl_Streaming_SHA2_finish_256 =
      foreign "Hacl_Streaming_SHA2_finish_256"
        ((ptr hacl_Streaming_Functor_state_s___uint32_t____) @->
           (ocaml_bytes @-> (returning void)))
    let hacl_Streaming_SHA2_free_256 =
      foreign "Hacl_Streaming_SHA2_free_256"
        ((ptr hacl_Streaming_Functor_state_s___uint32_t____) @->
           (returning void))
    type hacl_Streaming_Functor_state_s___uint64_t____ =
      [ `hacl_Streaming_Functor_state_s___uint64_t____ ] structure
    let (hacl_Streaming_Functor_state_s___uint64_t____ :
      [ `hacl_Streaming_Functor_state_s___uint64_t____ ] structure typ) =
      structure "Hacl_Streaming_Functor_state_s___uint64_t_____s"
    let hacl_Streaming_Functor_state_s___uint64_t_____block_state =
      field hacl_Streaming_Functor_state_s___uint64_t____ "block_state"
        (ptr uint64_t)
    let hacl_Streaming_Functor_state_s___uint64_t_____buf =
      field hacl_Streaming_Functor_state_s___uint64_t____ "buf" (ptr uint8_t)
    let hacl_Streaming_Functor_state_s___uint64_t_____total_len =
      field hacl_Streaming_Functor_state_s___uint64_t____ "total_len"
        uint64_t
    let _ = seal hacl_Streaming_Functor_state_s___uint64_t____
    let hacl_Streaming_SHA2_create_in_384 =
      foreign "Hacl_Streaming_SHA2_create_in_384"
        (void @->
           (returning (ptr hacl_Streaming_Functor_state_s___uint64_t____)))
    let hacl_Streaming_SHA2_init_384 =
      foreign "Hacl_Streaming_SHA2_init_384"
        ((ptr hacl_Streaming_Functor_state_s___uint64_t____) @->
           (returning void))
    let hacl_Streaming_SHA2_update_384 =
      foreign "Hacl_Streaming_SHA2_update_384"
        ((ptr hacl_Streaming_Functor_state_s___uint64_t____) @->
           (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let hacl_Streaming_SHA2_finish_384 =
      foreign "Hacl_Streaming_SHA2_finish_384"
        ((ptr hacl_Streaming_Functor_state_s___uint64_t____) @->
           (ocaml_bytes @-> (returning void)))
    let hacl_Streaming_SHA2_free_384 =
      foreign "Hacl_Streaming_SHA2_free_384"
        ((ptr hacl_Streaming_Functor_state_s___uint64_t____) @->
           (returning void))
    let hacl_Streaming_SHA2_create_in_512 =
      foreign "Hacl_Streaming_SHA2_create_in_512"
        (void @->
           (returning (ptr hacl_Streaming_Functor_state_s___uint64_t____)))
    let hacl_Streaming_SHA2_init_512 =
      foreign "Hacl_Streaming_SHA2_init_512"
        ((ptr hacl_Streaming_Functor_state_s___uint64_t____) @->
           (returning void))
    let hacl_Streaming_SHA2_update_512 =
      foreign "Hacl_Streaming_SHA2_update_512"
        ((ptr hacl_Streaming_Functor_state_s___uint64_t____) @->
           (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let hacl_Streaming_SHA2_finish_512 =
      foreign "Hacl_Streaming_SHA2_finish_512"
        ((ptr hacl_Streaming_Functor_state_s___uint64_t____) @->
           (ocaml_bytes @-> (returning void)))
    let hacl_Streaming_SHA2_free_512 =
      foreign "Hacl_Streaming_SHA2_free_512"
        ((ptr hacl_Streaming_Functor_state_s___uint64_t____) @->
           (returning void))
  end