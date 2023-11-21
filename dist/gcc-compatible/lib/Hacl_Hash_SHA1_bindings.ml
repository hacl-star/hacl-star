open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    module Hacl_Streaming_Types_applied =
      (Hacl_Streaming_Types_bindings.Bindings)(Hacl_Streaming_Types_stubs)
    open Hacl_Streaming_Types_applied
    let hacl_Hash_SHA1_init =
      foreign "Hacl_Hash_SHA1_init" ((ptr uint32_t) @-> (returning void))
    let hacl_Hash_SHA1_finish =
      foreign "Hacl_Hash_SHA1_finish"
        ((ptr uint32_t) @-> (ocaml_bytes @-> (returning void)))
    let hacl_Hash_SHA1_update_multi =
      foreign "Hacl_Hash_SHA1_update_multi"
        ((ptr uint32_t) @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let hacl_Hash_SHA1_update_last =
      foreign "Hacl_Hash_SHA1_update_last"
        ((ptr uint32_t) @->
           (uint64_t @-> (ocaml_bytes @-> (uint32_t @-> (returning void)))))
    let hacl_Hash_SHA1_hash_oneshot =
      foreign "Hacl_Hash_SHA1_hash_oneshot"
        (ocaml_bytes @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))
    type hacl_Hash_SHA1_state_t = hacl_Streaming_MD_state_32
    let hacl_Hash_SHA1_state_t =
      typedef hacl_Streaming_MD_state_32 "Hacl_Hash_SHA1_state_t"
    let hacl_Hash_SHA1_malloc =
      foreign "Hacl_Hash_SHA1_malloc"
        (void @-> (returning (ptr hacl_Streaming_MD_state_32)))
    let hacl_Hash_SHA1_reset =
      foreign "Hacl_Hash_SHA1_reset"
        ((ptr hacl_Streaming_MD_state_32) @-> (returning void))
    let hacl_Hash_SHA1_update =
      foreign "Hacl_Hash_SHA1_update"
        ((ptr hacl_Streaming_MD_state_32) @->
           (ocaml_bytes @->
              (uint32_t @-> (returning hacl_Streaming_Types_error_code))))
    let hacl_Hash_SHA1_digest =
      foreign "Hacl_Hash_SHA1_digest"
        ((ptr hacl_Streaming_MD_state_32) @->
           (ocaml_bytes @-> (returning void)))
    let hacl_Hash_SHA1_free =
      foreign "Hacl_Hash_SHA1_free"
        ((ptr hacl_Streaming_MD_state_32) @-> (returning void))
    let hacl_Hash_SHA1_copy =
      foreign "Hacl_Hash_SHA1_copy"
        ((ptr hacl_Streaming_MD_state_32) @->
           (returning (ptr hacl_Streaming_MD_state_32)))
    let hacl_Hash_SHA1_hash =
      foreign "Hacl_Hash_SHA1_hash"
        (ocaml_bytes @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))
  end