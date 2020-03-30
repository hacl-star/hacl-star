open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Impl_P256_DH_ecp256dh_i =
      foreign "Hacl_Impl_P256_DH_ecp256dh_i"
        (ocaml_bytes @-> (ocaml_bytes @-> (returning uint64_t)))
    let hacl_Impl_P256_DH_ecp256dh_r =
      foreign "Hacl_Impl_P256_DH_ecp256dh_r"
        (ocaml_bytes @->
           (ocaml_bytes @-> (ocaml_bytes @-> (returning uint64_t))))
    let hacl_Impl_ECDSA_ecdsa_p256_sha2_sign =
      foreign "Hacl_Impl_ECDSA_ecdsa_p256_sha2_sign"
        (ocaml_bytes @->
           (uint32_t @->
              (ocaml_bytes @->
                 (ocaml_bytes @-> (ocaml_bytes @-> (returning uint64_t))))))
    let hacl_Impl_ECDSA_ecdsa_p256_sha2_verify =
      foreign "Hacl_Impl_ECDSA_ecdsa_p256_sha2_verify"
        (uint32_t @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (ocaml_bytes @-> (ocaml_bytes @-> (returning bool))))))
  end