open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    module Hacl_Streaming_Types_applied =
      (Hacl_Streaming_Types_bindings.Bindings)(Hacl_Streaming_Types_stubs)
    open Hacl_Streaming_Types_applied
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
    type hacl_Hash_SHA3_hash_buf = [ `hacl_Hash_SHA3_hash_buf ] structure
    let (hacl_Hash_SHA3_hash_buf :
      [ `hacl_Hash_SHA3_hash_buf ] structure typ) =
      structure "Hacl_Hash_SHA3_hash_buf_s"
    let hacl_Hash_SHA3_hash_buf_fst =
      field hacl_Hash_SHA3_hash_buf "fst" spec_Hash_Definitions_hash_alg
    let hacl_Hash_SHA3_hash_buf_snd =
      field hacl_Hash_SHA3_hash_buf "snd" (ptr uint64_t)
    let _ = seal hacl_Hash_SHA3_hash_buf
    type hacl_Hash_SHA3_state_t = [ `hacl_Hash_SHA3_state_t ] structure
    let (hacl_Hash_SHA3_state_t : [ `hacl_Hash_SHA3_state_t ] structure typ)
      = structure "Hacl_Hash_SHA3_state_t_s"
    let hacl_Hash_SHA3_state_t_block_state =
      field hacl_Hash_SHA3_state_t "block_state" hacl_Hash_SHA3_hash_buf
    let hacl_Hash_SHA3_state_t_buf =
      field hacl_Hash_SHA3_state_t "buf" (ptr uint8_t)
    let hacl_Hash_SHA3_state_t_total_len =
      field hacl_Hash_SHA3_state_t "total_len" uint64_t
    let _ = seal hacl_Hash_SHA3_state_t
    let hacl_Hash_SHA3_get_alg =
      foreign "Hacl_Hash_SHA3_get_alg"
        ((ptr hacl_Hash_SHA3_state_t) @->
           (returning spec_Hash_Definitions_hash_alg))
    let hacl_Hash_SHA3_malloc =
      foreign "Hacl_Hash_SHA3_malloc"
        (spec_Hash_Definitions_hash_alg @->
           (returning (ptr hacl_Hash_SHA3_state_t)))
    let hacl_Hash_SHA3_free =
      foreign "Hacl_Hash_SHA3_free"
        ((ptr hacl_Hash_SHA3_state_t) @-> (returning void))
    let hacl_Hash_SHA3_copy =
      foreign "Hacl_Hash_SHA3_copy"
        ((ptr hacl_Hash_SHA3_state_t) @->
           (returning (ptr hacl_Hash_SHA3_state_t)))
    let hacl_Hash_SHA3_reset =
      foreign "Hacl_Hash_SHA3_reset"
        ((ptr hacl_Hash_SHA3_state_t) @-> (returning void))
    let hacl_Hash_SHA3_update =
      foreign "Hacl_Hash_SHA3_update"
        ((ptr hacl_Hash_SHA3_state_t) @->
           (ocaml_bytes @->
              (uint32_t @-> (returning hacl_Streaming_Types_error_code))))
    let hacl_Hash_SHA3_digest =
      foreign "Hacl_Hash_SHA3_digest"
        ((ptr hacl_Hash_SHA3_state_t) @->
           (ocaml_bytes @-> (returning hacl_Streaming_Types_error_code)))
    let hacl_Hash_SHA3_squeeze =
      foreign "Hacl_Hash_SHA3_squeeze"
        ((ptr hacl_Hash_SHA3_state_t) @->
           (ocaml_bytes @->
              (uint32_t @-> (returning hacl_Streaming_Types_error_code))))
    let hacl_Hash_SHA3_block_len =
      foreign "Hacl_Hash_SHA3_block_len"
        ((ptr hacl_Hash_SHA3_state_t) @-> (returning uint32_t))
    let hacl_Hash_SHA3_hash_len =
      foreign "Hacl_Hash_SHA3_hash_len"
        ((ptr hacl_Hash_SHA3_state_t) @-> (returning uint32_t))
    let hacl_Hash_SHA3_is_shake =
      foreign "Hacl_Hash_SHA3_is_shake"
        ((ptr hacl_Hash_SHA3_state_t) @-> (returning bool))
    let hacl_Hash_SHA3_absorb_inner_32 =
      foreign "Hacl_Hash_SHA3_absorb_inner_32"
        (uint32_t @-> (ocaml_bytes @-> ((ptr uint64_t) @-> (returning void))))
    let hacl_Hash_SHA3_shake128 =
      foreign "Hacl_Hash_SHA3_shake128"
        (ocaml_bytes @->
           (uint32_t @-> (ocaml_bytes @-> (uint32_t @-> (returning void)))))
    let hacl_Hash_SHA3_shake256 =
      foreign "Hacl_Hash_SHA3_shake256"
        (ocaml_bytes @->
           (uint32_t @-> (ocaml_bytes @-> (uint32_t @-> (returning void)))))
    let hacl_Hash_SHA3_sha3_224 =
      foreign "Hacl_Hash_SHA3_sha3_224"
        (ocaml_bytes @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let hacl_Hash_SHA3_sha3_256 =
      foreign "Hacl_Hash_SHA3_sha3_256"
        (ocaml_bytes @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let hacl_Hash_SHA3_sha3_384 =
      foreign "Hacl_Hash_SHA3_sha3_384"
        (ocaml_bytes @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let hacl_Hash_SHA3_sha3_512 =
      foreign "Hacl_Hash_SHA3_sha3_512"
        (ocaml_bytes @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let hacl_Hash_SHA3_state_malloc =
      foreign "Hacl_Hash_SHA3_state_malloc"
        (void @-> (returning (ptr uint64_t)))
    let hacl_Hash_SHA3_state_free =
      foreign "Hacl_Hash_SHA3_state_free"
        ((ptr uint64_t) @-> (returning void))
    let hacl_Hash_SHA3_shake128_absorb_nblocks =
      foreign "Hacl_Hash_SHA3_shake128_absorb_nblocks"
        ((ptr uint64_t) @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let hacl_Hash_SHA3_shake128_absorb_final =
      foreign "Hacl_Hash_SHA3_shake128_absorb_final"
        ((ptr uint64_t) @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let hacl_Hash_SHA3_shake128_squeeze_nblocks =
      foreign "Hacl_Hash_SHA3_shake128_squeeze_nblocks"
        ((ptr uint64_t) @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))
  end