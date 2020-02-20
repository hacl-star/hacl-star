open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_HPKE_Curve64_CP256_SHA512_setupBaseI =
      foreign "Hacl_HPKE_Curve64_CP256_SHA512_setupBaseI"
        ((ptr uint8_t) @->
           ((ptr uint8_t) @->
              ((ptr uint8_t) @->
                 ((ptr uint8_t) @->
                    ((ptr uint8_t) @->
                       (uint32_t @-> ((ptr uint8_t) @-> (returning uint32_t))))))))
      
    let hacl_HPKE_Curve64_CP256_SHA512_setupBaseR =
      foreign "Hacl_HPKE_Curve64_CP256_SHA512_setupBaseR"
        ((ptr uint8_t) @->
           ((ptr uint8_t) @->
              ((ptr uint8_t) @->
                 ((ptr uint8_t) @->
                    (uint32_t @-> ((ptr uint8_t) @-> (returning uint32_t)))))))
      
    let hacl_HPKE_Curve64_CP256_SHA512_sealBase =
      foreign "Hacl_HPKE_Curve64_CP256_SHA512_sealBase"
        ((ptr uint8_t) @->
           ((ptr uint8_t) @->
              (uint32_t @->
                 ((ptr uint8_t) @->
                    (uint32_t @->
                       ((ptr uint8_t) @->
                          ((ptr uint8_t) @-> (returning uint32_t))))))))
      
    let hacl_HPKE_Curve64_CP256_SHA512_openBase =
      foreign "Hacl_HPKE_Curve64_CP256_SHA512_openBase"
        ((ptr uint8_t) @->
           ((ptr uint8_t) @->
              (uint32_t @->
                 ((ptr uint8_t) @->
                    (uint32_t @->
                       ((ptr uint8_t) @->
                          ((ptr uint8_t) @-> (returning uint32_t))))))))
      
  end