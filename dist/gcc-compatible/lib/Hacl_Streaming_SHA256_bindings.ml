open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    type hacl_Streaming_Functor_state_s___uint32_t_ =
      [ `hacl_Streaming_Functor_state_s___uint32_t_ ] structure
    let (hacl_Streaming_Functor_state_s___uint32_t_ :
      [ `hacl_Streaming_Functor_state_s___uint32_t_ ] structure typ) =
      structure "Hacl_Streaming_Functor_state_s___uint32_t__s"
    let hacl_Streaming_Functor_state_s___uint32_t__block_state =
      field hacl_Streaming_Functor_state_s___uint32_t_ "block_state"
        (ptr uint32_t)
    let hacl_Streaming_Functor_state_s___uint32_t__buf =
      field hacl_Streaming_Functor_state_s___uint32_t_ "buf" (ptr uint8_t)
    let hacl_Streaming_Functor_state_s___uint32_t__total_len =
      field hacl_Streaming_Functor_state_s___uint32_t_ "total_len" uint64_t
    let _ = seal hacl_Streaming_Functor_state_s___uint32_t_
    let hacl_Streaming_SHA256_create_in =
      foreign "Hacl_Streaming_SHA256_create_in"
        (void @->
           (returning (ptr hacl_Streaming_Functor_state_s___uint32_t_)))
    let hacl_Streaming_SHA256_init =
      foreign "Hacl_Streaming_SHA256_init"
        ((ptr hacl_Streaming_Functor_state_s___uint32_t_) @->
           (returning void))
    let hacl_Streaming_SHA256_update =
      foreign "Hacl_Streaming_SHA256_update"
        ((ptr hacl_Streaming_Functor_state_s___uint32_t_) @->
           (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let hacl_Streaming_SHA256_finish =
      foreign "Hacl_Streaming_SHA256_finish"
        ((ptr hacl_Streaming_Functor_state_s___uint32_t_) @->
           (ocaml_bytes @-> (returning void)))
    let hacl_Streaming_SHA256_free =
      foreign "Hacl_Streaming_SHA256_free"
        ((ptr hacl_Streaming_Functor_state_s___uint32_t_) @->
           (returning void))
  end