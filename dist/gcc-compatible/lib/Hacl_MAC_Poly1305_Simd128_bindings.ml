open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    module Hacl_Streaming_Types_applied =
      (Hacl_Streaming_Types_bindings.Bindings)(Hacl_Streaming_Types_stubs)
    open Hacl_Streaming_Types_applied
    type hacl_MAC_Poly1305_Simd128_state_t =
      [ `hacl_MAC_Poly1305_Simd128_state_t ] structure
    let (hacl_MAC_Poly1305_Simd128_state_t :
      [ `hacl_MAC_Poly1305_Simd128_state_t ] structure typ) =
      structure "Hacl_MAC_Poly1305_Simd128_state_t_s"
    let hacl_MAC_Poly1305_Simd128_malloc =
      foreign "Hacl_MAC_Poly1305_Simd128_malloc"
        (ocaml_bytes @-> (returning (ptr hacl_MAC_Poly1305_Simd128_state_t)))
    let hacl_MAC_Poly1305_Simd128_reset =
      foreign "Hacl_MAC_Poly1305_Simd128_reset"
        ((ptr hacl_MAC_Poly1305_Simd128_state_t) @->
           (ocaml_bytes @-> (returning void)))
    let hacl_MAC_Poly1305_Simd128_update =
      foreign "Hacl_MAC_Poly1305_Simd128_update"
        ((ptr hacl_MAC_Poly1305_Simd128_state_t) @->
           (ocaml_bytes @->
              (uint32_t @-> (returning hacl_Streaming_Types_error_code))))
    let hacl_MAC_Poly1305_Simd128_digest =
      foreign "Hacl_MAC_Poly1305_Simd128_digest"
        ((ptr hacl_MAC_Poly1305_Simd128_state_t) @->
           (ocaml_bytes @-> (returning void)))
    let hacl_MAC_Poly1305_Simd128_free =
      foreign "Hacl_MAC_Poly1305_Simd128_free"
        ((ptr hacl_MAC_Poly1305_Simd128_state_t) @-> (returning void))
    let hacl_MAC_Poly1305_Simd128_mac =
      foreign "Hacl_MAC_Poly1305_Simd128_mac"
        (ocaml_bytes @->
           (ocaml_bytes @-> (uint32_t @-> (ocaml_bytes @-> (returning void)))))
  end