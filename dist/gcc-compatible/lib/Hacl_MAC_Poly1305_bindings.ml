open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_MAC_Poly1305_poly1305_init =
      foreign "Hacl_MAC_Poly1305_poly1305_init"
        ((ptr uint64_t) @-> (ocaml_bytes @-> (returning void)))
    let hacl_MAC_Poly1305_poly1305_update1 =
      foreign "Hacl_MAC_Poly1305_poly1305_update1"
        ((ptr uint64_t) @-> (ocaml_bytes @-> (returning void)))
    let hacl_MAC_Poly1305_poly1305_update =
      foreign "Hacl_MAC_Poly1305_poly1305_update"
        ((ptr uint64_t) @-> (uint32_t @-> (ocaml_bytes @-> (returning void))))
    let hacl_MAC_Poly1305_poly1305_finish =
      foreign "Hacl_MAC_Poly1305_poly1305_finish"
        (ocaml_bytes @->
           (ocaml_bytes @-> ((ptr uint64_t) @-> (returning void))))
    let hacl_MAC_Poly1305_mac =
      foreign "Hacl_MAC_Poly1305_mac"
        (ocaml_bytes @->
           (ocaml_bytes @-> (uint32_t @-> (ocaml_bytes @-> (returning void)))))
    type hacl_MAC_Poly1305_state_t = [ `hacl_MAC_Poly1305_state_t ] structure
    let (hacl_MAC_Poly1305_state_t :
      [ `hacl_MAC_Poly1305_state_t ] structure typ) =
      structure "Hacl_MAC_Poly1305_state_t_s"
    let hacl_MAC_Poly1305_state_t_block_state =
      field hacl_MAC_Poly1305_state_t "block_state" (ptr uint64_t)
    let hacl_MAC_Poly1305_state_t_buf =
      field hacl_MAC_Poly1305_state_t "buf" (ptr uint8_t)
    let hacl_MAC_Poly1305_state_t_total_len =
      field hacl_MAC_Poly1305_state_t "total_len" uint64_t
    let hacl_MAC_Poly1305_state_t_p_key =
      field hacl_MAC_Poly1305_state_t "p_key" (ptr uint8_t)
    let _ = seal hacl_MAC_Poly1305_state_t
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
           (ocaml_bytes @-> (uint32_t @-> (returning uint32_t))))
    let hacl_MAC_Poly1305_digest =
      foreign "Hacl_MAC_Poly1305_digest"
        ((ptr hacl_MAC_Poly1305_state_t) @->
           (ocaml_bytes @-> (returning void)))
    let hacl_MAC_Poly1305_free =
      foreign "Hacl_MAC_Poly1305_free"
        ((ptr hacl_MAC_Poly1305_state_t) @-> (returning void))
  end