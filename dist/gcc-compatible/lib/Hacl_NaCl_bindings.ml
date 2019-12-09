open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_NaCl_crypto_secretbox_detached =
      foreign "Hacl_NaCl_crypto_secretbox_detached"
        ((ptr uint8_t) @->
           ((ptr uint8_t) @->
              ((ptr uint8_t) @->
                 (uint32_t @->
                    ((ptr uint8_t) @->
                       ((ptr uint8_t) @-> (returning uint32_t)))))))
      
    let hacl_NaCl_crypto_secretbox_open_detached =
      foreign "Hacl_NaCl_crypto_secretbox_open_detached"
        ((ptr uint8_t) @->
           ((ptr uint8_t) @->
              ((ptr uint8_t) @->
                 (uint32_t @->
                    ((ptr uint8_t) @->
                       ((ptr uint8_t) @-> (returning uint32_t)))))))
      
    let hacl_NaCl_crypto_secretbox_easy =
      foreign "Hacl_NaCl_crypto_secretbox_easy"
        ((ptr uint8_t) @->
           ((ptr uint8_t) @->
              (uint32_t @->
                 ((ptr uint8_t) @-> ((ptr uint8_t) @-> (returning uint32_t))))))
      
    let hacl_NaCl_crypto_secretbox_open_easy =
      foreign "Hacl_NaCl_crypto_secretbox_open_easy"
        ((ptr uint8_t) @->
           ((ptr uint8_t) @->
              (uint32_t @->
                 ((ptr uint8_t) @-> ((ptr uint8_t) @-> (returning uint32_t))))))
      
    let hacl_NaCl_crypto_box_beforenm =
      foreign "Hacl_NaCl_crypto_box_beforenm"
        ((ptr uint8_t) @->
           ((ptr uint8_t) @-> ((ptr uint8_t) @-> (returning uint32_t))))
      
    let hacl_NaCl_crypto_box_detached_afternm =
      foreign "Hacl_NaCl_crypto_box_detached_afternm"
        ((ptr uint8_t) @->
           ((ptr uint8_t) @->
              ((ptr uint8_t) @->
                 (uint32_t @->
                    ((ptr uint8_t) @->
                       ((ptr uint8_t) @-> (returning uint32_t)))))))
      
    let hacl_NaCl_crypto_box_detached =
      foreign "Hacl_NaCl_crypto_box_detached"
        ((ptr uint8_t) @->
           ((ptr uint8_t) @->
              ((ptr uint8_t) @->
                 (uint32_t @->
                    ((ptr uint8_t) @->
                       ((ptr uint8_t) @->
                          ((ptr uint8_t) @-> (returning uint32_t))))))))
      
    let hacl_NaCl_crypto_box_open_detached_afternm =
      foreign "Hacl_NaCl_crypto_box_open_detached_afternm"
        ((ptr uint8_t) @->
           ((ptr uint8_t) @->
              ((ptr uint8_t) @->
                 (uint32_t @->
                    ((ptr uint8_t) @->
                       ((ptr uint8_t) @-> (returning uint32_t)))))))
      
    let hacl_NaCl_crypto_box_open_detached =
      foreign "Hacl_NaCl_crypto_box_open_detached"
        ((ptr uint8_t) @->
           ((ptr uint8_t) @->
              ((ptr uint8_t) @->
                 (uint32_t @->
                    ((ptr uint8_t) @->
                       ((ptr uint8_t) @->
                          ((ptr uint8_t) @-> (returning uint32_t))))))))
      
    let hacl_NaCl_crypto_box_easy_afternm =
      foreign "Hacl_NaCl_crypto_box_easy_afternm"
        ((ptr uint8_t) @->
           ((ptr uint8_t) @->
              (uint32_t @->
                 ((ptr uint8_t) @-> ((ptr uint8_t) @-> (returning uint32_t))))))
      
    let hacl_NaCl_crypto_box_easy =
      foreign "Hacl_NaCl_crypto_box_easy"
        ((ptr uint8_t) @->
           ((ptr uint8_t) @->
              (uint32_t @->
                 ((ptr uint8_t) @->
                    ((ptr uint8_t) @->
                       ((ptr uint8_t) @-> (returning uint32_t)))))))
      
    let hacl_NaCl_crypto_box_open_easy_afternm =
      foreign "Hacl_NaCl_crypto_box_open_easy_afternm"
        ((ptr uint8_t) @->
           ((ptr uint8_t) @->
              (uint32_t @->
                 ((ptr uint8_t) @-> ((ptr uint8_t) @-> (returning uint32_t))))))
      
    let hacl_NaCl_crypto_box_open_easy =
      foreign "Hacl_NaCl_crypto_box_open_easy"
        ((ptr uint8_t) @->
           ((ptr uint8_t) @->
              (uint32_t @->
                 ((ptr uint8_t) @->
                    ((ptr uint8_t) @->
                       ((ptr uint8_t) @-> (returning uint32_t)))))))
      
  end