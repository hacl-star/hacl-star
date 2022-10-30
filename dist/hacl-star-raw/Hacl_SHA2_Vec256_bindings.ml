open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_SHA2_Vec256_sha224_8 =
      foreign "Hacl_SHA2_Vec256_sha224_8"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (ocaml_bytes @->
                    (ocaml_bytes @->
                       (ocaml_bytes @->
                          (ocaml_bytes @->
                             (ocaml_bytes @->
                                (uint32_t @->
                                   (ocaml_bytes @->
                                      (ocaml_bytes @->
                                         (ocaml_bytes @->
                                            (ocaml_bytes @->
                                               (ocaml_bytes @->
                                                  (ocaml_bytes @->
                                                     (ocaml_bytes @->
                                                        (ocaml_bytes @->
                                                           (returning void))))))))))))))))))
    let hacl_SHA2_Vec256_sha256_8 =
      foreign "Hacl_SHA2_Vec256_sha256_8"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (ocaml_bytes @->
                    (ocaml_bytes @->
                       (ocaml_bytes @->
                          (ocaml_bytes @->
                             (ocaml_bytes @->
                                (uint32_t @->
                                   (ocaml_bytes @->
                                      (ocaml_bytes @->
                                         (ocaml_bytes @->
                                            (ocaml_bytes @->
                                               (ocaml_bytes @->
                                                  (ocaml_bytes @->
                                                     (ocaml_bytes @->
                                                        (ocaml_bytes @->
                                                           (returning void))))))))))))))))))
    let hacl_SHA2_Vec256_sha384_4 =
      foreign "Hacl_SHA2_Vec256_sha384_4"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (ocaml_bytes @->
                    (uint32_t @->
                       (ocaml_bytes @->
                          (ocaml_bytes @->
                             (ocaml_bytes @->
                                (ocaml_bytes @-> (returning void))))))))))
    let hacl_SHA2_Vec256_sha512_4 =
      foreign "Hacl_SHA2_Vec256_sha512_4"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (ocaml_bytes @->
                    (uint32_t @->
                       (ocaml_bytes @->
                          (ocaml_bytes @->
                             (ocaml_bytes @->
                                (ocaml_bytes @-> (returning void))))))))))
  end