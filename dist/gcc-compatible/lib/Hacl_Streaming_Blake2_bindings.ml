open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    module Hacl_Spec_applied = (Hacl_Spec_bindings.Bindings)(Hacl_Spec_stubs)
    open Hacl_Spec_applied
    module Hacl_Hash_Blake2_applied =
      (Hacl_Hash_Blake2_bindings.Bindings)(Hacl_Hash_Blake2_stubs)
    open Hacl_Hash_Blake2_applied
    let hacl_Streaming_Blake2_blocks_state_len =
      foreign "Hacl_Streaming_Blake2_blocks_state_len"
        (spec_Blake2_alg @->
           (hacl_Impl_Blake2_Core_m_spec @-> (returning uint32_t)))
    type hacl_Streaming_Blake2_blake2s_32_block_state =
      [ `hacl_Streaming_Blake2_blake2s_32_block_state ] structure
    let (hacl_Streaming_Blake2_blake2s_32_block_state :
      [ `hacl_Streaming_Blake2_blake2s_32_block_state ] structure typ) =
      structure "Hacl_Streaming_Blake2_blake2s_32_block_state_s"
    let hacl_Streaming_Blake2_blake2s_32_block_state_fst =
      field hacl_Streaming_Blake2_blake2s_32_block_state "fst" (ptr uint32_t)
    let hacl_Streaming_Blake2_blake2s_32_block_state_snd =
      field hacl_Streaming_Blake2_blake2s_32_block_state "snd" (ptr uint32_t)
    let _ = seal hacl_Streaming_Blake2_blake2s_32_block_state
    type hacl_Streaming_Blake2_blake2s_32_state =
      [ `hacl_Streaming_Blake2_blake2s_32_state ] structure
    let (hacl_Streaming_Blake2_blake2s_32_state :
      [ `hacl_Streaming_Blake2_blake2s_32_state ] structure typ) =
      structure "Hacl_Streaming_Blake2_blake2s_32_state_s"
    let hacl_Streaming_Blake2_blake2s_32_state_block_state =
      field hacl_Streaming_Blake2_blake2s_32_state "block_state"
        hacl_Streaming_Blake2_blake2s_32_block_state
    let hacl_Streaming_Blake2_blake2s_32_state_buf =
      field hacl_Streaming_Blake2_blake2s_32_state "buf" (ptr uint8_t)
    let hacl_Streaming_Blake2_blake2s_32_state_total_len =
      field hacl_Streaming_Blake2_blake2s_32_state "total_len" uint64_t
    let _ = seal hacl_Streaming_Blake2_blake2s_32_state
    let hacl_Streaming_Blake2_blake2s_32_no_key_create_in =
      foreign "Hacl_Streaming_Blake2_blake2s_32_no_key_create_in"
        (void @-> (returning (ptr hacl_Streaming_Blake2_blake2s_32_state)))
    let hacl_Streaming_Blake2_blake2s_32_no_key_init =
      foreign "Hacl_Streaming_Blake2_blake2s_32_no_key_init"
        ((ptr hacl_Streaming_Blake2_blake2s_32_state) @-> (returning void))
    let hacl_Streaming_Blake2_blake2s_32_no_key_update =
      foreign "Hacl_Streaming_Blake2_blake2s_32_no_key_update"
        ((ptr hacl_Streaming_Blake2_blake2s_32_state) @->
           (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let hacl_Streaming_Blake2_blake2s_32_no_key_finish =
      foreign "Hacl_Streaming_Blake2_blake2s_32_no_key_finish"
        ((ptr hacl_Streaming_Blake2_blake2s_32_state) @->
           (ocaml_bytes @-> (returning void)))
    let hacl_Streaming_Blake2_blake2s_32_no_key_free =
      foreign "Hacl_Streaming_Blake2_blake2s_32_no_key_free"
        ((ptr hacl_Streaming_Blake2_blake2s_32_state) @-> (returning void))
    type hacl_Streaming_Blake2_blake2b_32_block_state =
      [ `hacl_Streaming_Blake2_blake2b_32_block_state ] structure
    let (hacl_Streaming_Blake2_blake2b_32_block_state :
      [ `hacl_Streaming_Blake2_blake2b_32_block_state ] structure typ) =
      structure "Hacl_Streaming_Blake2_blake2b_32_block_state_s"
    let hacl_Streaming_Blake2_blake2b_32_block_state_fst =
      field hacl_Streaming_Blake2_blake2b_32_block_state "fst" (ptr uint64_t)
    let hacl_Streaming_Blake2_blake2b_32_block_state_snd =
      field hacl_Streaming_Blake2_blake2b_32_block_state "snd" (ptr uint64_t)
    let _ = seal hacl_Streaming_Blake2_blake2b_32_block_state
    type hacl_Streaming_Blake2_blake2b_32_state =
      [ `hacl_Streaming_Blake2_blake2b_32_state ] structure
    let (hacl_Streaming_Blake2_blake2b_32_state :
      [ `hacl_Streaming_Blake2_blake2b_32_state ] structure typ) =
      structure "Hacl_Streaming_Blake2_blake2b_32_state_s"
    let hacl_Streaming_Blake2_blake2b_32_state_block_state =
      field hacl_Streaming_Blake2_blake2b_32_state "block_state"
        hacl_Streaming_Blake2_blake2b_32_block_state
    let hacl_Streaming_Blake2_blake2b_32_state_buf =
      field hacl_Streaming_Blake2_blake2b_32_state "buf" (ptr uint8_t)
    let hacl_Streaming_Blake2_blake2b_32_state_total_len =
      field hacl_Streaming_Blake2_blake2b_32_state "total_len" uint64_t
    let _ = seal hacl_Streaming_Blake2_blake2b_32_state
    let hacl_Streaming_Blake2_blake2b_32_no_key_create_in =
      foreign "Hacl_Streaming_Blake2_blake2b_32_no_key_create_in"
        (void @-> (returning (ptr hacl_Streaming_Blake2_blake2b_32_state)))
    let hacl_Streaming_Blake2_blake2b_32_no_key_init =
      foreign "Hacl_Streaming_Blake2_blake2b_32_no_key_init"
        ((ptr hacl_Streaming_Blake2_blake2b_32_state) @-> (returning void))
    let hacl_Streaming_Blake2_blake2b_32_no_key_update =
      foreign "Hacl_Streaming_Blake2_blake2b_32_no_key_update"
        ((ptr hacl_Streaming_Blake2_blake2b_32_state) @->
           (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let hacl_Streaming_Blake2_blake2b_32_no_key_finish =
      foreign "Hacl_Streaming_Blake2_blake2b_32_no_key_finish"
        ((ptr hacl_Streaming_Blake2_blake2b_32_state) @->
           (ocaml_bytes @-> (returning void)))
    let hacl_Streaming_Blake2_blake2b_32_no_key_free =
      foreign "Hacl_Streaming_Blake2_blake2b_32_no_key_free"
        ((ptr hacl_Streaming_Blake2_blake2b_32_state) @-> (returning void))
  end