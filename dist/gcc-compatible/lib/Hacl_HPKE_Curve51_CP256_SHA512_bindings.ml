open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    module Hacl_HPKE_Interface_Hacl_Impl_HPKE_Hacl_Meta_HPKE_applied =
      (Hacl_HPKE_Interface_Hacl_Impl_HPKE_Hacl_Meta_HPKE_bindings.Bindings)(Hacl_HPKE_Interface_Hacl_Impl_HPKE_Hacl_Meta_HPKE_stubs)
    open Hacl_HPKE_Interface_Hacl_Impl_HPKE_Hacl_Meta_HPKE_applied
    let hacl_HPKE_Curve51_CP256_SHA512_setupBaseS =
      foreign "Hacl_HPKE_Curve51_CP256_SHA512_setupBaseS"
        (ocaml_bytes @->
           (hacl_Impl_HPKE_context_s @->
              (ocaml_bytes @->
                 (ocaml_bytes @->
                    (uint32_t @-> (ocaml_bytes @-> (returning uint32_t)))))))
    let hacl_HPKE_Curve51_CP256_SHA512_setupBaseR =
      foreign "Hacl_HPKE_Curve51_CP256_SHA512_setupBaseR"
        (hacl_Impl_HPKE_context_s @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (uint32_t @-> (ocaml_bytes @-> (returning uint32_t))))))
    let hacl_HPKE_Curve51_CP256_SHA512_sealBase =
      foreign "Hacl_HPKE_Curve51_CP256_SHA512_sealBase"
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
    let hacl_HPKE_Curve51_CP256_SHA512_openBase =
      foreign "Hacl_HPKE_Curve51_CP256_SHA512_openBase"
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