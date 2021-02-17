open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    module Hacl_Spec_applied = (Hacl_Spec_bindings.Bindings)(Hacl_Spec_stubs)
    open Hacl_Spec_applied
    let hacl_Keccak_shake128_4x =
      foreign "Hacl_Keccak_shake128_4x"
        (uint32_t @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (ocaml_bytes @->
                    (ocaml_bytes @->
                       (uint32_t @->
                          (ocaml_bytes @->
                             (ocaml_bytes @->
                                (ocaml_bytes @->
                                   (ocaml_bytes @-> (returning void)))))))))))
    let hacl_Impl_Matrix_mod_pow2 =
      foreign "Hacl_Impl_Matrix_mod_pow2"
        (uint32_t @->
           (uint32_t @-> (uint32_t @-> ((ptr uint16_t) @-> (returning void)))))
    let hacl_Impl_Matrix_matrix_add =
      foreign "Hacl_Impl_Matrix_matrix_add"
        (uint32_t @->
           (uint32_t @->
              ((ptr uint16_t) @-> ((ptr uint16_t) @-> (returning void)))))
    let hacl_Impl_Matrix_matrix_sub =
      foreign "Hacl_Impl_Matrix_matrix_sub"
        (uint32_t @->
           (uint32_t @->
              ((ptr uint16_t) @-> ((ptr uint16_t) @-> (returning void)))))
    let hacl_Impl_Matrix_matrix_mul =
      foreign "Hacl_Impl_Matrix_matrix_mul"
        (uint32_t @->
           (uint32_t @->
              (uint32_t @->
                 ((ptr uint16_t) @->
                    ((ptr uint16_t) @-> ((ptr uint16_t) @-> (returning void)))))))
    let hacl_Impl_Matrix_matrix_mul_s =
      foreign "Hacl_Impl_Matrix_matrix_mul_s"
        (uint32_t @->
           (uint32_t @->
              (uint32_t @->
                 ((ptr uint16_t) @->
                    ((ptr uint16_t) @-> ((ptr uint16_t) @-> (returning void)))))))
    let hacl_Impl_Matrix_matrix_eq =
      foreign "Hacl_Impl_Matrix_matrix_eq"
        (uint32_t @->
           (uint32_t @->
              ((ptr uint16_t) @-> ((ptr uint16_t) @-> (returning uint16_t)))))
    let hacl_Impl_Matrix_matrix_to_lbytes =
      foreign "Hacl_Impl_Matrix_matrix_to_lbytes"
        (uint32_t @->
           (uint32_t @->
              ((ptr uint16_t) @-> (ocaml_bytes @-> (returning void)))))
    let hacl_Impl_Matrix_matrix_from_lbytes =
      foreign "Hacl_Impl_Matrix_matrix_from_lbytes"
        (uint32_t @->
           (uint32_t @->
              (ocaml_bytes @-> ((ptr uint16_t) @-> (returning void)))))
    let hacl_Impl_Frodo_Gen_frodo_gen_matrix_shake_4x =
      foreign "Hacl_Impl_Frodo_Gen_frodo_gen_matrix_shake_4x"
        (uint32_t @-> (ocaml_bytes @-> ((ptr uint16_t) @-> (returning void))))
    let hacl_Impl_Frodo_Params_frodo_gen_matrix =
      foreign "Hacl_Impl_Frodo_Params_frodo_gen_matrix"
        (spec_Frodo_Params_frodo_gen_a @->
           (uint32_t @->
              (ocaml_bytes @-> ((ptr uint16_t) @-> (returning void)))))
    let hacl_Impl_Frodo_Sample_frodo_sample_matrix64 =
      foreign "Hacl_Impl_Frodo_Sample_frodo_sample_matrix64"
        (uint32_t @->
           (uint32_t @->
              (ocaml_bytes @-> ((ptr uint16_t) @-> (returning void)))))
    let hacl_Impl_Frodo_Sample_frodo_sample_matrix640 =
      foreign "Hacl_Impl_Frodo_Sample_frodo_sample_matrix640"
        (uint32_t @->
           (uint32_t @->
              (ocaml_bytes @-> ((ptr uint16_t) @-> (returning void)))))
    let hacl_Impl_Frodo_Sample_frodo_sample_matrix976 =
      foreign "Hacl_Impl_Frodo_Sample_frodo_sample_matrix976"
        (uint32_t @->
           (uint32_t @->
              (ocaml_bytes @-> ((ptr uint16_t) @-> (returning void)))))
    let hacl_Impl_Frodo_Sample_frodo_sample_matrix1344 =
      foreign "Hacl_Impl_Frodo_Sample_frodo_sample_matrix1344"
        (uint32_t @->
           (uint32_t @->
              (ocaml_bytes @-> ((ptr uint16_t) @-> (returning void)))))
    let randombytes_ =
      foreign "randombytes_"
        (uint32_t @-> (ocaml_bytes @-> (returning void)))
    let hacl_Impl_Frodo_Pack_frodo_pack =
      foreign "Hacl_Impl_Frodo_Pack_frodo_pack"
        (uint32_t @->
           (uint32_t @->
              (uint32_t @->
                 ((ptr uint16_t) @-> (ocaml_bytes @-> (returning void))))))
    let hacl_Impl_Frodo_Pack_frodo_unpack =
      foreign "Hacl_Impl_Frodo_Pack_frodo_unpack"
        (uint32_t @->
           (uint32_t @->
              (uint32_t @->
                 (ocaml_bytes @-> ((ptr uint16_t) @-> (returning void))))))
    let hacl_Impl_Frodo_Encode_frodo_key_encode =
      foreign "Hacl_Impl_Frodo_Encode_frodo_key_encode"
        (uint32_t @->
           (uint32_t @->
              (uint32_t @->
                 (ocaml_bytes @-> ((ptr uint16_t) @-> (returning void))))))
    let hacl_Impl_Frodo_Encode_frodo_key_decode =
      foreign "Hacl_Impl_Frodo_Encode_frodo_key_decode"
        (uint32_t @->
           (uint32_t @->
              (uint32_t @->
                 ((ptr uint16_t) @-> (ocaml_bytes @-> (returning void))))))
  end