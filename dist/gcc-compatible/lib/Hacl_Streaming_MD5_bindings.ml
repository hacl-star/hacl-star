open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    module Hacl_Streaming_SHA2_applied =
      (Hacl_Streaming_SHA2_bindings.Bindings)(Hacl_Streaming_SHA2_stubs)
    open Hacl_Streaming_SHA2_applied
    let hacl_Streaming_MD5_legacy_create_in_md5 =
      foreign "Hacl_Streaming_MD5_legacy_create_in_md5"
        (void @->
           (returning (ptr hacl_Streaming_Functor_state_s___uint32_t____)))
    let hacl_Streaming_MD5_legacy_init_md5 =
      foreign "Hacl_Streaming_MD5_legacy_init_md5"
        ((ptr hacl_Streaming_Functor_state_s___uint32_t____) @->
           (returning void))
    let hacl_Streaming_MD5_legacy_update_md5 =
      foreign "Hacl_Streaming_MD5_legacy_update_md5"
        ((ptr hacl_Streaming_Functor_state_s___uint32_t____) @->
           (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let hacl_Streaming_MD5_legacy_finish_md5 =
      foreign "Hacl_Streaming_MD5_legacy_finish_md5"
        ((ptr hacl_Streaming_Functor_state_s___uint32_t____) @->
           (ocaml_bytes @-> (returning void)))
    let hacl_Streaming_MD5_legacy_free_md5 =
      foreign "Hacl_Streaming_MD5_legacy_free_md5"
        ((ptr hacl_Streaming_Functor_state_s___uint32_t____) @->
           (returning void))
  end