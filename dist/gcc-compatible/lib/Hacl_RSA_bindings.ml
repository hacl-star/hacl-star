open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_RSA_rsa_dec =
      foreign "Hacl_RSA_rsa_dec"
        (uint32_t @->
           (uint32_t @->
              (uint32_t @->
                 ((ptr uint64_t) @->
                    (ocaml_bytes @-> (ocaml_bytes @-> (returning bool)))))))
    let hacl_RSA_rsa_enc =
      foreign "Hacl_RSA_rsa_enc"
        (uint32_t @->
           (uint32_t @->
              ((ptr uint64_t) @->
                 (ocaml_bytes @-> (ocaml_bytes @-> (returning bool))))))
    let hacl_RSA_new_rsa_load_pkey =
      foreign "Hacl_RSA_new_rsa_load_pkey"
        (uint32_t @->
           (uint32_t @->
              (ocaml_bytes @-> (ocaml_bytes @-> (returning (ptr uint64_t))))))
    let hacl_RSA_new_rsa_load_skey =
      foreign "Hacl_RSA_new_rsa_load_skey"
        (uint32_t @->
           (uint32_t @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (ocaml_bytes @->
                       (ocaml_bytes @-> (returning (ptr uint64_t))))))))
  end