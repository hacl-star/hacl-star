open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    type hacl_Streaming_Functor_state_s___uint64_t___uint8_t_ =
      [ `hacl_Streaming_Functor_state_s___uint64_t___uint8_t_ ] structure
    let (hacl_Streaming_Functor_state_s___uint64_t___uint8_t_ :
      [ `hacl_Streaming_Functor_state_s___uint64_t___uint8_t_ ] structure typ)
      = structure "Hacl_Streaming_Functor_state_s___uint64_t___uint8_t__s"
    let hacl_Streaming_Poly1305_32_create_in =
      foreign "Hacl_Streaming_Poly1305_32_create_in"
        (ocaml_bytes @->
           (returning
              (ptr hacl_Streaming_Functor_state_s___uint64_t___uint8_t_)))
    let hacl_Streaming_Poly1305_32_init =
      foreign "Hacl_Streaming_Poly1305_32_init"
        (ocaml_bytes @->
           ((ptr hacl_Streaming_Functor_state_s___uint64_t___uint8_t_) @->
              (returning void)))
    let hacl_Streaming_Poly1305_32_update =
      foreign "Hacl_Streaming_Poly1305_32_update"
        ((ptr hacl_Streaming_Functor_state_s___uint64_t___uint8_t_) @->
           (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let hacl_Streaming_Poly1305_32_finish =
      foreign "Hacl_Streaming_Poly1305_32_finish"
        ((ptr hacl_Streaming_Functor_state_s___uint64_t___uint8_t_) @->
           (ocaml_bytes @-> (returning void)))
    let hacl_Streaming_Poly1305_32_free =
      foreign "Hacl_Streaming_Poly1305_32_free"
        ((ptr hacl_Streaming_Functor_state_s___uint64_t___uint8_t_) @->
           (returning void))
  end