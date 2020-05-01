open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_SHA2_Vec512_sha512_8 =
      foreign "Hacl_SHA2_Vec512_sha512_8"
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
  end