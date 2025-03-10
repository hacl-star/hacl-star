open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    module Hacl_Streaming_Types_applied =
      (Hacl_Streaming_Types_bindings.Bindings)(Hacl_Streaming_Types_stubs)
    open Hacl_Streaming_Types_applied
    let hacl_MAC_Poly1305_poly1305_init =
      foreign "Hacl_MAC_Poly1305_poly1305_init"
        ((ptr uint64_t) @-> (ocaml_bytes @-> (returning void)))
    let hacl_MAC_Poly1305_poly1305_finish =
      foreign "Hacl_MAC_Poly1305_poly1305_finish"
        (ocaml_bytes @->
           (ocaml_bytes @-> ((ptr uint64_t) @-> (returning void))))
    type hacl_MAC_Poly1305_state_t = [ `hacl_MAC_Poly1305_state_t ] structure
    let (hacl_MAC_Poly1305_state_t :
      [ `hacl_MAC_Poly1305_state_t ] structure typ) =
      structure "Hacl_MAC_Poly1305_state_t_s"
    let hacl_MAC_Poly1305_malloc =
      foreign "Hacl_MAC_Poly1305_malloc"
        (ocaml_bytes @-> (returning (ptr hacl_MAC_Poly1305_state_t)))
    let hacl_MAC_Poly1305_reset =
      foreign "Hacl_MAC_Poly1305_reset"
        ((ptr hacl_MAC_Poly1305_state_t) @->
           (ocaml_bytes @-> (returning void)))
    let hacl_MAC_Poly1305_update =
      foreign "Hacl_MAC_Poly1305_update"
        ((ptr hacl_MAC_Poly1305_state_t) @->
           (ocaml_bytes @->
              (uint32_t @-> (returning hacl_Streaming_Types_error_code))))
    let hacl_MAC_Poly1305_digest =
      foreign "Hacl_MAC_Poly1305_digest"
        ((ptr hacl_MAC_Poly1305_state_t) @->
           (ocaml_bytes @-> (returning void)))
    let hacl_MAC_Poly1305_free =
      foreign "Hacl_MAC_Poly1305_free"
        ((ptr hacl_MAC_Poly1305_state_t) @-> (returning void))
    let hacl_MAC_Poly1305_mac =
      foreign "Hacl_MAC_Poly1305_mac"
        (ocaml_bytes @->
           (ocaml_bytes @-> (uint32_t @-> (ocaml_bytes @-> (returning void)))))
  end