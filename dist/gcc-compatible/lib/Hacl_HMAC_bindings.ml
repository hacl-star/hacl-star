open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_HMAC_legacy_compute_sha1 =
      foreign "Hacl_HMAC_legacy_compute_sha1"
        ((ptr uint8_t) @->
           ((ptr uint8_t) @->
              (uint32_t @->
                 ((ptr uint8_t) @-> (uint32_t @-> (returning void))))))
      
    let hacl_HMAC_compute_sha2_256 =
      foreign "Hacl_HMAC_compute_sha2_256"
        ((ptr uint8_t) @->
           ((ptr uint8_t) @->
              (uint32_t @->
                 ((ptr uint8_t) @-> (uint32_t @-> (returning void))))))
      
    let hacl_HMAC_compute_sha2_384 =
      foreign "Hacl_HMAC_compute_sha2_384"
        ((ptr uint8_t) @->
           ((ptr uint8_t) @->
              (uint32_t @->
                 ((ptr uint8_t) @-> (uint32_t @-> (returning void))))))
      
    let hacl_HMAC_compute_sha2_512 =
      foreign "Hacl_HMAC_compute_sha2_512"
        ((ptr uint8_t) @->
           ((ptr uint8_t) @->
              (uint32_t @->
                 ((ptr uint8_t) @-> (uint32_t @-> (returning void))))))
      
  end