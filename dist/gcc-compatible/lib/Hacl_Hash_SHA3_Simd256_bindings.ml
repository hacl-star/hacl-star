open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    type k____uint8_t___uint8_t_ = [ `k____uint8_t___uint8_t_ ] structure
    let (k____uint8_t___uint8_t_ :
      [ `k____uint8_t___uint8_t_ ] structure typ) =
      structure "K____uint8_t___uint8_t__s"
    let k____uint8_t___uint8_t__fst =
      field k____uint8_t___uint8_t_ "fst" (ptr uint8_t)
    let k____uint8_t___uint8_t__snd =
      field k____uint8_t___uint8_t_ "snd" (ptr uint8_t)
    let _ = seal k____uint8_t___uint8_t_
    type k____uint8_t__K____uint8_t___uint8_t_ =
      [ `k____uint8_t__K____uint8_t___uint8_t_ ] structure
    let (k____uint8_t__K____uint8_t___uint8_t_ :
      [ `k____uint8_t__K____uint8_t___uint8_t_ ] structure typ) =
      structure "K____uint8_t__K____uint8_t___uint8_t__s"
    let k____uint8_t__K____uint8_t___uint8_t__fst =
      field k____uint8_t__K____uint8_t___uint8_t_ "fst" (ptr uint8_t)
    let k____uint8_t__K____uint8_t___uint8_t__snd =
      field k____uint8_t__K____uint8_t___uint8_t_ "snd"
        k____uint8_t___uint8_t_
    let _ = seal k____uint8_t__K____uint8_t___uint8_t_
    type k____uint8_t___uint8_t____K____uint8_t___uint8_t_ =
      [ `k____uint8_t___uint8_t____K____uint8_t___uint8_t_ ] structure
    let (k____uint8_t___uint8_t____K____uint8_t___uint8_t_ :
      [ `k____uint8_t___uint8_t____K____uint8_t___uint8_t_ ] structure typ) =
      structure "K____uint8_t___uint8_t____K____uint8_t___uint8_t__s"
    let k____uint8_t___uint8_t____K____uint8_t___uint8_t__fst =
      field k____uint8_t___uint8_t____K____uint8_t___uint8_t_ "fst"
        (ptr uint8_t)
    let k____uint8_t___uint8_t____K____uint8_t___uint8_t__snd =
      field k____uint8_t___uint8_t____K____uint8_t___uint8_t_ "snd"
        k____uint8_t__K____uint8_t___uint8_t_
    let _ = seal k____uint8_t___uint8_t____K____uint8_t___uint8_t_
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