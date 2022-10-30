open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    module Hacl_Streaming_SHA2_applied =
      (Hacl_Streaming_SHA2_bindings.Bindings)(Hacl_Streaming_SHA2_stubs)
    open Hacl_Streaming_SHA2_applied
    type hacl_Streaming_MD5_state_md5 = hacl_Streaming_SHA2_state_sha2_224
    let hacl_Streaming_MD5_state_md5 =
      typedef hacl_Streaming_SHA2_state_sha2_224
        "Hacl_Streaming_MD5_state_md5"
    let hacl_Streaming_MD5_legacy_create_in_md5 =
      foreign "Hacl_Streaming_MD5_legacy_create_in_md5"
        (void @-> (returning (ptr hacl_Streaming_SHA2_state_sha2_224)))
    let hacl_Streaming_MD5_legacy_init_md5 =
      foreign "Hacl_Streaming_MD5_legacy_init_md5"
        ((ptr hacl_Streaming_SHA2_state_sha2_224) @-> (returning void))
    let hacl_Streaming_MD5_legacy_update_md5 =
      foreign "Hacl_Streaming_MD5_legacy_update_md5"
        ((ptr hacl_Streaming_SHA2_state_sha2_224) @->
           (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let hacl_Streaming_MD5_legacy_finish_md5 =
      foreign "Hacl_Streaming_MD5_legacy_finish_md5"
        ((ptr hacl_Streaming_SHA2_state_sha2_224) @->
           (ocaml_bytes @-> (returning void)))
    let hacl_Streaming_MD5_legacy_free_md5 =
      foreign "Hacl_Streaming_MD5_legacy_free_md5"
        ((ptr hacl_Streaming_SHA2_state_sha2_224) @-> (returning void))
  end