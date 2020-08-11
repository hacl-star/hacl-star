open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    type k____uint32_t___uint32_t_ = [ `k____uint32_t___uint32_t_ ] structure
    let (k____uint32_t___uint32_t_ :
      [ `k____uint32_t___uint32_t_ ] structure typ) =
      structure "K____uint32_t___uint32_t__s"
    let k____uint32_t___uint32_t__fst =
      field k____uint32_t___uint32_t_ "fst" (ptr uint32_t)
    let k____uint32_t___uint32_t__snd =
      field k____uint32_t___uint32_t_ "snd" (ptr uint32_t)
    let _ = seal k____uint32_t___uint32_t_
    type hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____ =
      [ `hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____ ]
        structure
    let (hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____ :
      [ `hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____ ]
        structure typ)
      =
      structure
        "Hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t_____s"
    let hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t_____block_state
      =
      field hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____
        "block_state" k____uint32_t___uint32_t_
    let hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t_____buf =
      field hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____
        "buf" (ptr uint8_t)
    let hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t_____total_len
      =
      field hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____
        "total_len" uint64_t
    let _ = seal hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____
    let hacl_Streaming_Blake2_blake2s_32_no_key_create_in =
      foreign "Hacl_Streaming_Blake2_blake2s_32_no_key_create_in"
        (void @->
           (returning
              (ptr
                 hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____)))
    let hacl_Streaming_Blake2_blake2s_32_no_key_update =
      foreign "Hacl_Streaming_Blake2_blake2s_32_no_key_update"
        ((ptr hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____)
           @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let hacl_Streaming_Blake2_blake2s_32_no_key_finish =
      foreign "Hacl_Streaming_Blake2_blake2s_32_no_key_finish"
        ((ptr hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____)
           @-> (ocaml_bytes @-> (returning void)))
    let hacl_Streaming_Blake2_blake2s_32_no_key_free =
      foreign "Hacl_Streaming_Blake2_blake2s_32_no_key_free"
        ((ptr hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____)
           @-> (returning void))
    type k____uint64_t___uint64_t_ = [ `k____uint64_t___uint64_t_ ] structure
    let (k____uint64_t___uint64_t_ :
      [ `k____uint64_t___uint64_t_ ] structure typ) =
      structure "K____uint64_t___uint64_t__s"
    let k____uint64_t___uint64_t__fst =
      field k____uint64_t___uint64_t_ "fst" (ptr uint64_t)
    let k____uint64_t___uint64_t__snd =
      field k____uint64_t___uint64_t_ "snd" (ptr uint64_t)
    let _ = seal k____uint64_t___uint64_t_
    type hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____ =
      [ `hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____ ]
        structure
    let (hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____ :
      [ `hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____ ]
        structure typ)
      =
      structure
        "Hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t_____s"
    let hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t_____block_state
      =
      field hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____
        "block_state" k____uint64_t___uint64_t_
    let hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t_____buf =
      field hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____
        "buf" (ptr uint8_t)
    let hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t_____total_len
      =
      field hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____
        "total_len" uint64_t
    let _ = seal hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____
    let hacl_Streaming_Blake2_blake2b_32_no_key_create_in =
      foreign "Hacl_Streaming_Blake2_blake2b_32_no_key_create_in"
        (void @->
           (returning
              (ptr
                 hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____)))
    let hacl_Streaming_Blake2_blake2b_32_no_key_update =
      foreign "Hacl_Streaming_Blake2_blake2b_32_no_key_update"
        ((ptr hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____)
           @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let hacl_Streaming_Blake2_blake2b_32_no_key_finish =
      foreign "Hacl_Streaming_Blake2_blake2b_32_no_key_finish"
        ((ptr hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____)
           @-> (ocaml_bytes @-> (returning void)))
    let hacl_Streaming_Blake2_blake2b_32_no_key_free =
      foreign "Hacl_Streaming_Blake2_blake2b_32_no_key_free"
        ((ptr hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____)
           @-> (returning void))
    let hacl_Streaming_Blake2_blake2s_32_with_key_create_in =
      foreign "Hacl_Streaming_Blake2_blake2s_32_with_key_create_in"
        (uint32_t @->
           (ocaml_bytes @->
              (returning
                 (ptr
                    hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____))))
    let hacl_Streaming_Blake2_blake2s_32_with_key_update =
      foreign "Hacl_Streaming_Blake2_blake2s_32_with_key_update"
        (uint32_t @->
           ((ptr hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____)
              @-> (ocaml_bytes @-> (uint32_t @-> (returning void)))))
    let hacl_Streaming_Blake2_blake2s_32_with_key_finish =
      foreign "Hacl_Streaming_Blake2_blake2s_32_with_key_finish"
        (uint32_t @->
           ((ptr hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____)
              @-> (ocaml_bytes @-> (returning void))))
    let hacl_Streaming_Blake2_blake2s_32_with_key_free =
      foreign "Hacl_Streaming_Blake2_blake2s_32_with_key_free"
        (uint32_t @->
           ((ptr hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____)
              @-> (returning void)))
    let hacl_Streaming_Blake2_blake2b_32_with_key_create_in =
      foreign "Hacl_Streaming_Blake2_blake2b_32_with_key_create_in"
        (uint32_t @->
           (ocaml_bytes @->
              (returning
                 (ptr
                    hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____))))
    let hacl_Streaming_Blake2_blake2b_32_with_key_update =
      foreign "Hacl_Streaming_Blake2_blake2b_32_with_key_update"
        (uint32_t @->
           ((ptr hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____)
              @-> (ocaml_bytes @-> (uint32_t @-> (returning void)))))
    let hacl_Streaming_Blake2_blake2b_32_with_key_finish =
      foreign "Hacl_Streaming_Blake2_blake2b_32_with_key_finish"
        (uint32_t @->
           ((ptr hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____)
              @-> (ocaml_bytes @-> (returning void))))
    let hacl_Streaming_Blake2_blake2b_32_with_key_free =
      foreign "Hacl_Streaming_Blake2_blake2b_32_with_key_free"
        (uint32_t @->
           ((ptr hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____)
              @-> (returning void)))
  end