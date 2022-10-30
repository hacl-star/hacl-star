open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    type hacl_Streaming_Poly1305_32_poly1305_32_state =
      [ `hacl_Streaming_Poly1305_32_poly1305_32_state ] structure
    let (hacl_Streaming_Poly1305_32_poly1305_32_state :
      [ `hacl_Streaming_Poly1305_32_poly1305_32_state ] structure typ) =
      structure "Hacl_Streaming_Poly1305_32_poly1305_32_state_s"
    let hacl_Streaming_Poly1305_32_poly1305_32_state_block_state =
      field hacl_Streaming_Poly1305_32_poly1305_32_state "block_state"
        (ptr uint64_t)
    let hacl_Streaming_Poly1305_32_poly1305_32_state_buf =
      field hacl_Streaming_Poly1305_32_poly1305_32_state "buf" (ptr uint8_t)
    let hacl_Streaming_Poly1305_32_poly1305_32_state_total_len =
      field hacl_Streaming_Poly1305_32_poly1305_32_state "total_len" uint64_t
    let hacl_Streaming_Poly1305_32_poly1305_32_state_p_key =
      field hacl_Streaming_Poly1305_32_poly1305_32_state "p_key"
        (ptr uint8_t)
    let _ = seal hacl_Streaming_Poly1305_32_poly1305_32_state
    let hacl_Streaming_Poly1305_32_create_in =
      foreign "Hacl_Streaming_Poly1305_32_create_in"
        (ocaml_bytes @->
           (returning (ptr hacl_Streaming_Poly1305_32_poly1305_32_state)))
    let hacl_Streaming_Poly1305_32_init =
      foreign "Hacl_Streaming_Poly1305_32_init"
        (ocaml_bytes @->
           ((ptr hacl_Streaming_Poly1305_32_poly1305_32_state) @->
              (returning void)))
    let hacl_Streaming_Poly1305_32_update =
      foreign "Hacl_Streaming_Poly1305_32_update"
        ((ptr hacl_Streaming_Poly1305_32_poly1305_32_state) @->
           (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let hacl_Streaming_Poly1305_32_finish =
      foreign "Hacl_Streaming_Poly1305_32_finish"
        ((ptr hacl_Streaming_Poly1305_32_poly1305_32_state) @->
           (ocaml_bytes @-> (returning void)))
    let hacl_Streaming_Poly1305_32_free =
      foreign "Hacl_Streaming_Poly1305_32_free"
        ((ptr hacl_Streaming_Poly1305_32_poly1305_32_state) @->
           (returning void))
  end