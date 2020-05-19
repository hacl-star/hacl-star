open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_HPKE_Curve64_CP128_SHA512_setupBaseI =
      foreign "Hacl_HPKE_Curve64_CP128_SHA512_setupBaseI"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (ocaml_bytes @->
                    (ocaml_bytes @->
                       (uint32_t @-> (ocaml_bytes @-> (returning uint32_t))))))))
    let hacl_HPKE_Curve64_CP128_SHA512_setupBaseR =
      foreign "Hacl_HPKE_Curve64_CP128_SHA512_setupBaseR"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (ocaml_bytes @->
                    (uint32_t @-> (ocaml_bytes @-> (returning uint32_t)))))))
    let hacl_HPKE_Curve64_CP128_SHA512_sealBase =
      foreign "Hacl_HPKE_Curve64_CP128_SHA512_sealBase"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (uint32_t @->
                       (ocaml_bytes @->
                          (ocaml_bytes @-> (returning uint32_t))))))))
    let hacl_HPKE_Curve64_CP128_SHA512_openBase =
      foreign "Hacl_HPKE_Curve64_CP128_SHA512_openBase"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (uint32_t @->
                       (ocaml_bytes @->
                          (ocaml_bytes @-> (returning uint32_t))))))))
  end