open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Frodo64_crypto_bytes =
      foreign_value "Hacl_Frodo64_crypto_bytes" uint32_t
    let hacl_Frodo64_crypto_publickeybytes =
      foreign_value "Hacl_Frodo64_crypto_publickeybytes" uint32_t
    let hacl_Frodo64_crypto_secretkeybytes =
      foreign_value "Hacl_Frodo64_crypto_secretkeybytes" uint32_t
    let hacl_Frodo64_crypto_ciphertextbytes =
      foreign_value "Hacl_Frodo64_crypto_ciphertextbytes" uint32_t
    let hacl_Frodo64_crypto_kem_keypair =
      foreign "Hacl_Frodo64_crypto_kem_keypair"
        (ocaml_bytes @-> (ocaml_bytes @-> (returning uint32_t)))
    let hacl_Frodo64_crypto_kem_enc =
      foreign "Hacl_Frodo64_crypto_kem_enc"
        (ocaml_bytes @->
           (ocaml_bytes @-> (ocaml_bytes @-> (returning uint32_t))))
    let hacl_Frodo64_crypto_kem_dec =
      foreign "Hacl_Frodo64_crypto_kem_dec"
        (ocaml_bytes @->
           (ocaml_bytes @-> (ocaml_bytes @-> (returning uint32_t))))
  end