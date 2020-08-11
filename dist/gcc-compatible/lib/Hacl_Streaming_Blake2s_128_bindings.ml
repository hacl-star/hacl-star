open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Streaming_Blake2s_128_blake2s_128_no_key_create_in =
      foreign "Hacl_Streaming_Blake2s_128_blake2s_128_no_key_create_in"
        (void @->
           (returning
              (ptr
                 hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____)))
    let hacl_Streaming_Blake2s_128_blake2s_128_no_key_update =
      foreign "Hacl_Streaming_Blake2s_128_blake2s_128_no_key_update"
        ((ptr
            hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____)
           @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let hacl_Streaming_Blake2s_128_blake2s_128_no_key_finish =
      foreign "Hacl_Streaming_Blake2s_128_blake2s_128_no_key_finish"
        ((ptr
            hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____)
           @-> (ocaml_bytes @-> (returning void)))
    let hacl_Streaming_Blake2s_128_blake2s_128_no_key_free =
      foreign "Hacl_Streaming_Blake2s_128_blake2s_128_no_key_free"
        ((ptr
            hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____)
           @-> (returning void))
    let hacl_Streaming_Blake2s_128_blake2s_128_with_key_create_in =
      foreign "Hacl_Streaming_Blake2s_128_blake2s_128_with_key_create_in"
        (uint32_t @->
           (ocaml_bytes @->
              (returning
                 (ptr
                    hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____))))
    let hacl_Streaming_Blake2s_128_blake2s_128_with_key_update =
      foreign "Hacl_Streaming_Blake2s_128_blake2s_128_with_key_update"
        (uint32_t @->
           ((ptr
               hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____)
              @-> (ocaml_bytes @-> (uint32_t @-> (returning void)))))
    let hacl_Streaming_Blake2s_128_blake2s_128_with_key_finish =
      foreign "Hacl_Streaming_Blake2s_128_blake2s_128_with_key_finish"
        (uint32_t @->
           ((ptr
               hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____)
              @-> (ocaml_bytes @-> (returning void))))
    let hacl_Streaming_Blake2s_128_blake2s_128_with_key_free =
      foreign "Hacl_Streaming_Blake2s_128_blake2s_128_with_key_free"
        (uint32_t @->
           ((ptr
               hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____)
              @-> (returning void)))
  end