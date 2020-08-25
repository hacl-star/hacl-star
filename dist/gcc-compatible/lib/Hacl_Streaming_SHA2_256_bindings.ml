open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    type hacl_Streaming_Functor_state_s___uint32_t____ =
      [ `hacl_Streaming_Functor_state_s___uint32_t____ ] structure
    let (hacl_Streaming_Functor_state_s___uint32_t____ :
      [ `hacl_Streaming_Functor_state_s___uint32_t____ ] structure typ) =
      structure "Hacl_Streaming_Functor_state_s___uint32_t_____s"
    let hacl_Streaming_SHA2_256_create_in =
      foreign "Hacl_Streaming_SHA2_256_create_in"
        (void @->
           (returning (ptr hacl_Streaming_Functor_state_s___uint32_t____)))
    let hacl_Streaming_SHA2_256_init =
      foreign "Hacl_Streaming_SHA2_256_init"
        ((ptr hacl_Streaming_Functor_state_s___uint32_t____) @->
           (returning void))
    let hacl_Streaming_SHA2_256_update =
      foreign "Hacl_Streaming_SHA2_256_update"
        ((ptr hacl_Streaming_Functor_state_s___uint32_t____) @->
           (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let hacl_Streaming_SHA2_256_finish =
      foreign "Hacl_Streaming_SHA2_256_finish"
        ((ptr hacl_Streaming_Functor_state_s___uint32_t____) @->
           (ocaml_bytes @-> (returning void)))
    let hacl_Streaming_SHA2_256_free =
      foreign "Hacl_Streaming_SHA2_256_free"
        ((ptr hacl_Streaming_Functor_state_s___uint32_t____) @->
           (returning void))
  end