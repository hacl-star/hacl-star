open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Hash_SHA3_Simd256_shake128 =
      foreign "Hacl_Hash_SHA3_Simd256_shake128"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (ocaml_bytes @->
                    (uint32_t @->
                       (ocaml_bytes @->
                          (ocaml_bytes @->
                             (ocaml_bytes @->
                                (ocaml_bytes @->
                                   (uint32_t @-> (returning void)))))))))))
    let hacl_Hash_SHA3_Simd256_shake256 =
      foreign "Hacl_Hash_SHA3_Simd256_shake256"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (ocaml_bytes @->
                    (uint32_t @->
                       (ocaml_bytes @->
                          (ocaml_bytes @->
                             (ocaml_bytes @->
                                (ocaml_bytes @->
                                   (uint32_t @-> (returning void)))))))))))
    let hacl_Hash_SHA3_Simd256_sha3_224 =
      foreign "Hacl_Hash_SHA3_Simd256_sha3_224"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (ocaml_bytes @->
                    (ocaml_bytes @->
                       (ocaml_bytes @->
                          (ocaml_bytes @->
                             (ocaml_bytes @-> (uint32_t @-> (returning void))))))))))
    let hacl_Hash_SHA3_Simd256_sha3_256 =
      foreign "Hacl_Hash_SHA3_Simd256_sha3_256"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (ocaml_bytes @->
                    (ocaml_bytes @->
                       (ocaml_bytes @->
                          (ocaml_bytes @->
                             (ocaml_bytes @-> (uint32_t @-> (returning void))))))))))
    let hacl_Hash_SHA3_Simd256_sha3_384 =
      foreign "Hacl_Hash_SHA3_Simd256_sha3_384"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (ocaml_bytes @->
                    (ocaml_bytes @->
                       (ocaml_bytes @->
                          (ocaml_bytes @->
                             (ocaml_bytes @-> (uint32_t @-> (returning void))))))))))
    let hacl_Hash_SHA3_Simd256_sha3_512 =
      foreign "Hacl_Hash_SHA3_Simd256_sha3_512"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (ocaml_bytes @->
                    (ocaml_bytes @->
                       (ocaml_bytes @->
                          (ocaml_bytes @->
                             (ocaml_bytes @-> (uint32_t @-> (returning void))))))))))
  end