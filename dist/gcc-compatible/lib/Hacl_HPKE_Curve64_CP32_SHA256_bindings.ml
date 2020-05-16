open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_HPKE_Curve64_CP32_SHA256_setupBaseI =
      foreign "Hacl_HPKE_Curve64_CP32_SHA256_setupBaseI"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (ocaml_bytes @->
                    (ocaml_bytes @->
                       (uint32_t @-> (ocaml_bytes @-> (returning uint32_t))))))))
    let hacl_HPKE_Curve64_CP32_SHA256_setupBaseR =
      foreign "Hacl_HPKE_Curve64_CP32_SHA256_setupBaseR"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (ocaml_bytes @->
                    (uint32_t @-> (ocaml_bytes @-> (returning uint32_t)))))))
    let hacl_HPKE_Curve64_CP32_SHA256_sealBase =
      foreign "Hacl_HPKE_Curve64_CP32_SHA256_sealBase"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (uint32_t @->
                       (ocaml_bytes @->
                          (ocaml_bytes @-> (returning uint32_t))))))))
    let hacl_HPKE_Curve64_CP32_SHA256_openBase =
      foreign "Hacl_HPKE_Curve64_CP32_SHA256_openBase"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (uint32_t @->
                       (ocaml_bytes @->
                          (ocaml_bytes @-> (returning uint32_t))))))))
  end