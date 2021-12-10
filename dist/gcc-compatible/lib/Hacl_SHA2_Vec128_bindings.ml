open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_SHA2_Vec128_sha224_4 =
      foreign "Hacl_SHA2_Vec128_sha224_4"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (ocaml_bytes @->
                    (uint32_t @->
                       (ocaml_bytes @->
                          (ocaml_bytes @->
                             (ocaml_bytes @->
                                (ocaml_bytes @-> (returning void))))))))))
    let hacl_SHA2_Vec128_sha256_4 =
      foreign "Hacl_SHA2_Vec128_sha256_4"
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