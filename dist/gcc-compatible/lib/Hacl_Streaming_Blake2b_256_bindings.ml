open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    type hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____ =
      [
        `hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____
          ]
        structure
    let (hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____
      :
      [
        `hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____
          ]
        structure typ)
      =
      structure
        "Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256_____s"
    let hacl_Streaming_Blake2b_256_blake2b_256_no_key_create_in =
      foreign "Hacl_Streaming_Blake2b_256_blake2b_256_no_key_create_in"
        (void @->
           (returning
              (ptr
                 hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____)))
    let hacl_Streaming_Blake2b_256_blake2b_256_no_key_update =
      foreign "Hacl_Streaming_Blake2b_256_blake2b_256_no_key_update"
        ((ptr
            hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____)
           @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let hacl_Streaming_Blake2b_256_blake2b_256_no_key_finish =
      foreign "Hacl_Streaming_Blake2b_256_blake2b_256_no_key_finish"
        ((ptr
            hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____)
           @-> (ocaml_bytes @-> (returning void)))
    let hacl_Streaming_Blake2b_256_blake2b_256_no_key_free =
      foreign "Hacl_Streaming_Blake2b_256_blake2b_256_no_key_free"
        ((ptr
            hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____)
           @-> (returning void))
    let hacl_Streaming_Blake2b_256_blake2b_256_with_key_create_in =
      foreign "Hacl_Streaming_Blake2b_256_blake2b_256_with_key_create_in"
        (uint32_t @->
           (ocaml_bytes @->
              (returning
                 (ptr
                    hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____))))
    let hacl_Streaming_Blake2b_256_blake2b_256_with_key_update =
      foreign "Hacl_Streaming_Blake2b_256_blake2b_256_with_key_update"
        (uint32_t @->
           ((ptr
               hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____)
              @-> (ocaml_bytes @-> (uint32_t @-> (returning void)))))
    let hacl_Streaming_Blake2b_256_blake2b_256_with_key_finish =
      foreign "Hacl_Streaming_Blake2b_256_blake2b_256_with_key_finish"
        (uint32_t @->
           ((ptr
               hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____)
              @-> (ocaml_bytes @-> (returning void))))
    let hacl_Streaming_Blake2b_256_blake2b_256_with_key_free =
      foreign "Hacl_Streaming_Blake2b_256_blake2b_256_with_key_free"
        (uint32_t @->
           ((ptr
               hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____)
              @-> (returning void)))
  end