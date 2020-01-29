open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Impl_ECDSA_ecdsa_p256_sha2_keyGen =
      foreign "Hacl_Impl_ECDSA_ecdsa_p256_sha2_keyGen"
        ((ptr uint8_t) @-> ((ptr uint8_t) @-> (returning void)))
    let hacl_Impl_ECDSA_ecdsa_p256_sha2_sign =
      foreign "Hacl_Impl_ECDSA_ecdsa_p256_sha2_sign"
        ((ptr uint8_t) @->
           (uint32_t @->
              ((ptr uint8_t) @->
                 ((ptr uint8_t) @-> ((ptr uint8_t) @-> (returning uint64_t))))))
    let hacl_Impl_ECDSA_ecdsa_p256_sha2_sign_nist =
      foreign "Hacl_Impl_ECDSA_ecdsa_p256_sha2_sign_nist"
        ((ptr uint8_t) @->
           ((ptr uint8_t) @->
              ((ptr uint8_t) @-> ((ptr uint8_t) @-> (returning uint64_t)))))
    let hacl_Impl_ECDSA_ecdsa_p256_sha2_verify =
      foreign "Hacl_Impl_ECDSA_ecdsa_p256_sha2_verify"
        (uint32_t @->
           ((ptr uint8_t) @->
              ((ptr uint64_t) @->
                 ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning bool))))))
    let hacl_Impl_ECDSA_ecdsa_p256_sha2_verify_u8 =
      foreign "Hacl_Impl_ECDSA_ecdsa_p256_sha2_verify_u8"
        (uint32_t @->
           ((ptr uint8_t) @->
              ((ptr uint8_t) @->
                 ((ptr uint8_t) @-> ((ptr uint8_t) @-> (returning bool))))))
  end