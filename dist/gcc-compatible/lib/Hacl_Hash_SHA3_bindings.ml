open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    module Hacl_Spec_applied = (Hacl_Spec_bindings.Bindings)(Hacl_Spec_stubs)
    open Hacl_Spec_applied
    let hacl_Hash_SHA3_update_multi_sha3 =
      foreign "Hacl_Hash_SHA3_update_multi_sha3"
        (spec_Hash_Definitions_hash_alg @->
           ((ptr uint64_t) @->
              (ocaml_bytes @-> (uint32_t @-> (returning void)))))
    let hacl_Hash_SHA3_update_last_sha3 =
      foreign "Hacl_Hash_SHA3_update_last_sha3"
        (spec_Hash_Definitions_hash_alg @->
           ((ptr uint64_t) @->
              (ocaml_bytes @-> (uint32_t @-> (returning void)))))
    type k___Spec_Hash_Definitions_hash_alg__uint64_t_ =
      [ `k___Spec_Hash_Definitions_hash_alg__uint64_t_ ] structure
    let (k___Spec_Hash_Definitions_hash_alg__uint64_t_ :
      [ `k___Spec_Hash_Definitions_hash_alg__uint64_t_ ] structure typ) =
      structure "K___Spec_Hash_Definitions_hash_alg__uint64_t__s"
    let k___Spec_Hash_Definitions_hash_alg__uint64_t__fst =
      field k___Spec_Hash_Definitions_hash_alg__uint64_t_ "fst"
        spec_Hash_Definitions_hash_alg
    let k___Spec_Hash_Definitions_hash_alg__uint64_t__snd =
      field k___Spec_Hash_Definitions_hash_alg__uint64_t_ "snd"
        (ptr uint64_t)
    let _ = seal k___Spec_Hash_Definitions_hash_alg__uint64_t_
    type hacl_Streaming_Keccak_state =
      [ `hacl_Streaming_Keccak_state ] structure
    let (hacl_Streaming_Keccak_state :
      [ `hacl_Streaming_Keccak_state ] structure typ) =
      structure "Hacl_Streaming_Keccak_state_s"
    let hacl_Streaming_Keccak_state_block_state =
      field hacl_Streaming_Keccak_state "block_state"
        k___Spec_Hash_Definitions_hash_alg__uint64_t_
    let hacl_Streaming_Keccak_state_buf =
      field hacl_Streaming_Keccak_state "buf" (ptr uint8_t)
    let hacl_Streaming_Keccak_state_total_len =
      field hacl_Streaming_Keccak_state "total_len" uint64_t
    let _ = seal hacl_Streaming_Keccak_state
    let hacl_Streaming_Keccak_get_alg =
      foreign "Hacl_Streaming_Keccak_get_alg"
        ((ptr hacl_Streaming_Keccak_state) @->
           (returning spec_Hash_Definitions_hash_alg))
    let hacl_Streaming_Keccak_malloc =
      foreign "Hacl_Streaming_Keccak_malloc"
        (spec_Hash_Definitions_hash_alg @->
           (returning (ptr hacl_Streaming_Keccak_state)))
    let hacl_Streaming_Keccak_copy =
      foreign "Hacl_Streaming_Keccak_copy"
        ((ptr hacl_Streaming_Keccak_state) @->
           (returning (ptr hacl_Streaming_Keccak_state)))
    let hacl_Streaming_Keccak_reset =
      foreign "Hacl_Streaming_Keccak_reset"
        ((ptr hacl_Streaming_Keccak_state) @-> (returning void))
    let hacl_Streaming_Keccak_update =
      foreign "Hacl_Streaming_Keccak_update"
        ((ptr hacl_Streaming_Keccak_state) @->
           (ocaml_bytes @-> (uint32_t @-> (returning uint32_t))))
    let hacl_Streaming_Keccak_finish =
      foreign "Hacl_Streaming_Keccak_finish"
        ((ptr hacl_Streaming_Keccak_state) @->
           (ocaml_bytes @-> (uint32_t @-> (returning uint32_t))))
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