open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    type hacl_Streaming_Poly1305_32_state_t =
      [ `hacl_Streaming_Poly1305_32_state_t ] structure
    let (hacl_Streaming_Poly1305_32_state_t :
      [ `hacl_Streaming_Poly1305_32_state_t ] structure typ) =
      structure "Hacl_Streaming_Poly1305_32_state_t_s"
    let hacl_Streaming_Poly1305_32_state_t_block_state =
      field hacl_Streaming_Poly1305_32_state_t "block_state" (ptr uint64_t)
    let hacl_Streaming_Poly1305_32_state_t_buf =
      field hacl_Streaming_Poly1305_32_state_t "buf" (ptr uint8_t)
    let hacl_Streaming_Poly1305_32_state_t_total_len =
      field hacl_Streaming_Poly1305_32_state_t "total_len" uint64_t
    let hacl_Streaming_Poly1305_32_state_t_p_key =
      field hacl_Streaming_Poly1305_32_state_t "p_key" (ptr uint8_t)
    let _ = seal hacl_Streaming_Poly1305_32_state_t
    let hacl_Streaming_Poly1305_32_malloc =
      foreign "Hacl_Streaming_Poly1305_32_malloc"
        (ocaml_bytes @-> (returning (ptr hacl_Streaming_Poly1305_32_state_t)))
    let hacl_Streaming_Poly1305_32_reset =
      foreign "Hacl_Streaming_Poly1305_32_reset"
        (ocaml_bytes @->
           ((ptr hacl_Streaming_Poly1305_32_state_t) @-> (returning void)))
    let hacl_Streaming_Poly1305_32_update =
      foreign "Hacl_Streaming_Poly1305_32_update"
        ((ptr hacl_Streaming_Poly1305_32_state_t) @->
           (ocaml_bytes @-> (uint32_t @-> (returning uint32_t))))
    let hacl_Streaming_Poly1305_32_digest =
      foreign "Hacl_Streaming_Poly1305_32_digest"
        ((ptr hacl_Streaming_Poly1305_32_state_t) @->
           (ocaml_bytes @-> (returning void)))
    let hacl_Streaming_Poly1305_32_free =
      foreign "Hacl_Streaming_Poly1305_32_free"
        ((ptr hacl_Streaming_Poly1305_32_state_t) @-> (returning void))
  end