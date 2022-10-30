open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    module Hacl_Streaming_SHA2_applied =
      (Hacl_Streaming_SHA2_bindings.Bindings)(Hacl_Streaming_SHA2_stubs)
    open Hacl_Streaming_SHA2_applied
    type hacl_Streaming_SHA3_state_sha3_256 =
      hacl_Streaming_SHA2_state_sha2_384
    let hacl_Streaming_SHA3_state_sha3_256 =
      typedef hacl_Streaming_SHA2_state_sha2_384
        "Hacl_Streaming_SHA3_state_sha3_256"
    let hacl_Streaming_SHA3_create_in_256 =
      foreign "Hacl_Streaming_SHA3_create_in_256"
        (void @-> (returning (ptr hacl_Streaming_SHA2_state_sha2_384)))
    let hacl_Streaming_SHA3_init_256 =
      foreign "Hacl_Streaming_SHA3_init_256"
        ((ptr hacl_Streaming_SHA2_state_sha2_384) @-> (returning void))
    let hacl_Streaming_SHA3_update_256 =
      foreign "Hacl_Streaming_SHA3_update_256"
        ((ptr hacl_Streaming_SHA2_state_sha2_384) @->
           (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let hacl_Streaming_SHA3_finish_256 =
      foreign "Hacl_Streaming_SHA3_finish_256"
        ((ptr hacl_Streaming_SHA2_state_sha2_384) @->
           (ocaml_bytes @-> (returning void)))
    let hacl_Streaming_SHA3_free_256 =
      foreign "Hacl_Streaming_SHA3_free_256"
        ((ptr hacl_Streaming_SHA2_state_sha2_384) @-> (returning void))
  end