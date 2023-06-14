open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    module Hacl_Streaming_Types_applied =
      (Hacl_Streaming_Types_bindings.Bindings)(Hacl_Streaming_Types_stubs)
    open Hacl_Streaming_Types_applied
    let hacl_Hash_MD5_init =
      foreign "Hacl_Hash_MD5_init" ((ptr uint32_t) @-> (returning void))
    let hacl_Hash_MD5_finish =
      foreign "Hacl_Hash_MD5_finish"
        ((ptr uint32_t) @-> (ocaml_bytes @-> (returning void)))
    let hacl_Hash_MD5_update_multi =
      foreign "Hacl_Hash_MD5_update_multi"
        ((ptr uint32_t) @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let hacl_Hash_MD5_update_last =
      foreign "Hacl_Hash_MD5_update_last"
        ((ptr uint32_t) @->
           (uint64_t @-> (ocaml_bytes @-> (uint32_t @-> (returning void)))))
    let hacl_Hash_MD5_hash_oneshot =
      foreign "Hacl_Hash_MD5_hash_oneshot"
        (ocaml_bytes @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))
    type hacl_Hash_MD5_state_t = hacl_Streaming_MD_state_32
    let hacl_Hash_MD5_state_t =
      typedef hacl_Streaming_MD_state_32 "Hacl_Hash_MD5_state_t"
    let hacl_Hash_MD5_malloc =
      foreign "Hacl_Hash_MD5_malloc"
        (void @-> (returning (ptr hacl_Streaming_MD_state_32)))
    let hacl_Hash_MD5_reset =
      foreign "Hacl_Hash_MD5_reset"
        ((ptr hacl_Streaming_MD_state_32) @-> (returning void))
    let hacl_Hash_MD5_update =
      foreign "Hacl_Hash_MD5_update"
        ((ptr hacl_Streaming_MD_state_32) @->
           (ocaml_bytes @->
              (uint32_t @-> (returning hacl_Streaming_Types_error_code))))
    let hacl_Hash_MD5_digest =
      foreign "Hacl_Hash_MD5_digest"
        ((ptr hacl_Streaming_MD_state_32) @->
           (ocaml_bytes @-> (returning void)))
    let hacl_Hash_MD5_free =
      foreign "Hacl_Hash_MD5_free"
        ((ptr hacl_Streaming_MD_state_32) @-> (returning void))
    let hacl_Hash_MD5_copy =
      foreign "Hacl_Hash_MD5_copy"
        ((ptr hacl_Streaming_MD_state_32) @->
           (returning (ptr hacl_Streaming_MD_state_32)))
    let hacl_Hash_MD5_hash =
      foreign "Hacl_Hash_MD5_hash"
        (ocaml_bytes @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))
  end