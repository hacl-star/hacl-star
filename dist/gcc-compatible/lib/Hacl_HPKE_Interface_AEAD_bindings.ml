open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    module Hacl_Spec_applied = (Hacl_Spec_bindings.Bindings)(Hacl_Spec_stubs)
    open Hacl_Spec_applied
    let hacl_HPKE_Interface_AEAD_aead_encrypt =
      foreign "Hacl_HPKE_Interface_AEAD_aead_encrypt"
        (spec_Agile_HPKE_ciphersuite @->
           (returning
              (ocaml_bytes @->
                 (ocaml_bytes @->
                    (uint32_t @->
                       (ocaml_bytes @->
                          (uint32_t @->
                             (ocaml_bytes @->
                                (ocaml_bytes @-> (returning void))))))))))
    let hacl_HPKE_Interface_AEAD_aead_decrypt =
      foreign "Hacl_HPKE_Interface_AEAD_aead_decrypt"
        (spec_Agile_HPKE_ciphersuite @->
           (returning
              (ocaml_bytes @->
                 (ocaml_bytes @->
                    (uint32_t @->
                       (ocaml_bytes @->
                          (uint32_t @->
                             (ocaml_bytes @->
                                (ocaml_bytes @-> (returning uint32_t))))))))))
  end