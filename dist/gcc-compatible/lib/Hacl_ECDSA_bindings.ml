open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Impl_ECDSA_ecdsa_p256_sha2_sign =
      foreign "Hacl_Impl_ECDSA_ecdsa_p256_sha2_sign"
        ((ptr uint8_t) @->
           (uint32_t @->
              ((ptr uint8_t) @->
                 ((ptr uint8_t) @-> ((ptr uint8_t) @-> (returning uint64_t))))))
    let hacl_Impl_ECDSA_ecdsa_p256_sha2_verify =
      foreign "Hacl_Impl_ECDSA_ecdsa_p256_sha2_verify"
        (uint32_t @->
           ((ptr uint8_t) @->
              ((ptr uint8_t) @->
                 ((ptr uint8_t) @-> ((ptr uint8_t) @-> (returning bool))))))
  end