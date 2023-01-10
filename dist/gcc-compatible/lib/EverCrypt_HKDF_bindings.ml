open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    module Hacl_Spec_applied = (Hacl_Spec_bindings.Bindings)(Hacl_Spec_stubs)
    open Hacl_Spec_applied
    let everCrypt_HKDF_expand =
      foreign "EverCrypt_HKDF_expand"
        (spec_Hash_Definitions_hash_alg @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (uint32_t @->
                    (ocaml_bytes @->
                       (uint32_t @-> (uint32_t @-> (returning void))))))))
    let everCrypt_HKDF_extract =
      foreign "EverCrypt_HKDF_extract"
        (spec_Hash_Definitions_hash_alg @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (uint32_t @->
                    (ocaml_bytes @-> (uint32_t @-> (returning void)))))))
  end