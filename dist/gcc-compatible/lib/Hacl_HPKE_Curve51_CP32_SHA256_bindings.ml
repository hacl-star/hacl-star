open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    module Hacl_Impl_HPKE_applied =
      (Hacl_Impl_HPKE_bindings.Bindings)(Hacl_Impl_HPKE_stubs)
    open Hacl_Impl_HPKE_applied
    let hacl_HPKE_Curve51_CP32_SHA256_setupBaseS =
      foreign "Hacl_HPKE_Curve51_CP32_SHA256_setupBaseS"
        (ocaml_bytes @->
           (hacl_Impl_HPKE_context_s @->
              (ocaml_bytes @->
                 (ocaml_bytes @->
                    (uint32_t @-> (ocaml_bytes @-> (returning uint32_t)))))))
    let hacl_HPKE_Curve51_CP32_SHA256_setupBaseR =
      foreign "Hacl_HPKE_Curve51_CP32_SHA256_setupBaseR"
        (hacl_Impl_HPKE_context_s @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (uint32_t @-> (ocaml_bytes @-> (returning uint32_t))))))
    let hacl_HPKE_Curve51_CP32_SHA256_sealBase =
      foreign "Hacl_HPKE_Curve51_CP32_SHA256_sealBase"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (uint32_t @->
                       (ocaml_bytes @->
                          (uint32_t @->
                             (ocaml_bytes @->
                                (ocaml_bytes @->
                                   (ocaml_bytes @-> (returning uint32_t)))))))))))
    let hacl_HPKE_Curve51_CP32_SHA256_openBase =
      foreign "Hacl_HPKE_Curve51_CP32_SHA256_openBase"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (uint32_t @->
                       (ocaml_bytes @->
                          (uint32_t @->
                             (ocaml_bytes @->
                                (ocaml_bytes @-> (returning uint32_t))))))))))
  end