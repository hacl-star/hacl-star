open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    module Hacl_Streaming_Types_applied =
      (Hacl_Streaming_Types_bindings.Bindings)(Hacl_Streaming_Types_stubs)
    open Hacl_Streaming_Types_applied
    type hacl_Streaming_SHA3_state_256 = hacl_Streaming_MD_state_64
    let hacl_Streaming_SHA3_state_256 =
      typedef hacl_Streaming_MD_state_64 "Hacl_Streaming_SHA3_state_256"
    let hacl_Streaming_SHA3_create_in_256 =
      foreign "Hacl_Streaming_SHA3_create_in_256"
        (void @-> (returning (ptr hacl_Streaming_MD_state_64)))
    let hacl_Streaming_SHA3_init_256 =
      foreign "Hacl_Streaming_SHA3_init_256"
        ((ptr hacl_Streaming_MD_state_64) @-> (returning void))
    let hacl_Streaming_SHA3_update_256 =
      foreign "Hacl_Streaming_SHA3_update_256"
        ((ptr hacl_Streaming_MD_state_64) @->
           (ocaml_bytes @-> (uint32_t @-> (returning uint32_t))))
    let hacl_Streaming_SHA3_finish_256 =
      foreign "Hacl_Streaming_SHA3_finish_256"
        ((ptr hacl_Streaming_MD_state_64) @->
           (ocaml_bytes @-> (returning void)))
    let hacl_Streaming_SHA3_free_256 =
      foreign "Hacl_Streaming_SHA3_free_256"
        ((ptr hacl_Streaming_MD_state_64) @-> (returning void))
    let hacl_Streaming_SHA3_copy_256 =
      foreign "Hacl_Streaming_SHA3_copy_256"
        ((ptr hacl_Streaming_MD_state_64) @->
           (returning (ptr hacl_Streaming_MD_state_64)))
    let hacl_SHA3_shake128_hacl =
      foreign "Hacl_SHA3_shake128_hacl"
        (uint32_t @->
           (ocaml_bytes @-> (uint32_t @-> (ocaml_bytes @-> (returning void)))))
    let hacl_SHA3_shake256_hacl =
      foreign "Hacl_SHA3_shake256_hacl"
        (uint32_t @->
           (ocaml_bytes @-> (uint32_t @-> (ocaml_bytes @-> (returning void)))))
    let hacl_SHA3_sha3_224 =
      foreign "Hacl_SHA3_sha3_224"
        (uint32_t @-> (ocaml_bytes @-> (ocaml_bytes @-> (returning void))))
    let hacl_SHA3_sha3_256 =
      foreign "Hacl_SHA3_sha3_256"
        (uint32_t @-> (ocaml_bytes @-> (ocaml_bytes @-> (returning void))))
    let hacl_SHA3_sha3_384 =
      foreign "Hacl_SHA3_sha3_384"
        (uint32_t @-> (ocaml_bytes @-> (ocaml_bytes @-> (returning void))))
    let hacl_SHA3_sha3_512 =
      foreign "Hacl_SHA3_sha3_512"
        (uint32_t @-> (ocaml_bytes @-> (ocaml_bytes @-> (returning void))))
    let hacl_Impl_SHA3_state_permute =
      foreign "Hacl_Impl_SHA3_state_permute"
        ((ptr uint64_t) @-> (returning void))
    let hacl_Impl_SHA3_loadState =
      foreign "Hacl_Impl_SHA3_loadState"
        (uint32_t @-> (ocaml_bytes @-> ((ptr uint64_t) @-> (returning void))))
    let hacl_Impl_SHA3_absorb_inner =
      foreign "Hacl_Impl_SHA3_absorb_inner"
        (uint32_t @-> (ocaml_bytes @-> ((ptr uint64_t) @-> (returning void))))
    let hacl_Impl_SHA3_squeeze =
      foreign "Hacl_Impl_SHA3_squeeze"
        ((ptr uint64_t) @->
           (uint32_t @-> (uint32_t @-> (ocaml_bytes @-> (returning void)))))
    let hacl_Impl_SHA3_keccak =
      foreign "Hacl_Impl_SHA3_keccak"
        (uint32_t @->
           (uint32_t @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (uint8_t @->
                       (uint32_t @-> (ocaml_bytes @-> (returning void))))))))
  end