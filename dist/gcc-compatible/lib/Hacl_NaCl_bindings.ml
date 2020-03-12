open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_NaCl_crypto_secretbox_detached =
      foreign "Hacl_NaCl_crypto_secretbox_detached"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (uint32_t @->
                    (ocaml_bytes @-> (ocaml_bytes @-> (returning uint32_t)))))))
    let hacl_NaCl_crypto_secretbox_open_detached =
      foreign "Hacl_NaCl_crypto_secretbox_open_detached"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (uint32_t @->
                    (ocaml_bytes @-> (ocaml_bytes @-> (returning uint32_t)))))))
    let hacl_NaCl_crypto_secretbox_easy =
      foreign "Hacl_NaCl_crypto_secretbox_easy"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @-> (ocaml_bytes @-> (returning uint32_t))))))
    let hacl_NaCl_crypto_secretbox_open_easy =
      foreign "Hacl_NaCl_crypto_secretbox_open_easy"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @-> (ocaml_bytes @-> (returning uint32_t))))))
    let hacl_NaCl_crypto_box_beforenm =
      foreign "Hacl_NaCl_crypto_box_beforenm"
        (ocaml_bytes @->
           (ocaml_bytes @-> (ocaml_bytes @-> (returning uint32_t))))
    let hacl_NaCl_crypto_box_detached_afternm =
      foreign "Hacl_NaCl_crypto_box_detached_afternm"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (uint32_t @->
                    (ocaml_bytes @-> (ocaml_bytes @-> (returning uint32_t)))))))
    let hacl_NaCl_crypto_box_detached =
      foreign "Hacl_NaCl_crypto_box_detached"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (uint32_t @->
                    (ocaml_bytes @->
                       (ocaml_bytes @->
                          (ocaml_bytes @-> (returning uint32_t))))))))
    let hacl_NaCl_crypto_box_open_detached_afternm =
      foreign "Hacl_NaCl_crypto_box_open_detached_afternm"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (uint32_t @->
                    (ocaml_bytes @-> (ocaml_bytes @-> (returning uint32_t)))))))
    let hacl_NaCl_crypto_box_open_detached =
      foreign "Hacl_NaCl_crypto_box_open_detached"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (uint32_t @->
                    (ocaml_bytes @->
                       (ocaml_bytes @->
                          (ocaml_bytes @-> (returning uint32_t))))))))
    let hacl_NaCl_crypto_box_easy_afternm =
      foreign "Hacl_NaCl_crypto_box_easy_afternm"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @-> (ocaml_bytes @-> (returning uint32_t))))))
    let hacl_NaCl_crypto_box_easy =
      foreign "Hacl_NaCl_crypto_box_easy"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (ocaml_bytes @-> (ocaml_bytes @-> (returning uint32_t)))))))
    let hacl_NaCl_crypto_box_open_easy_afternm =
      foreign "Hacl_NaCl_crypto_box_open_easy_afternm"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @-> (ocaml_bytes @-> (returning uint32_t))))))
    let hacl_NaCl_crypto_box_open_easy =
      foreign "Hacl_NaCl_crypto_box_open_easy"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (ocaml_bytes @-> (ocaml_bytes @-> (returning uint32_t)))))))
  end