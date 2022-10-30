open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    module Hacl_Spec_applied = (Hacl_Spec_bindings.Bindings)(Hacl_Spec_stubs)
    open Hacl_Spec_applied
    module EverCrypt_Error_applied =
      (EverCrypt_Error_bindings.Bindings)(EverCrypt_Error_stubs)
    open EverCrypt_Error_applied
    type everCrypt_AEAD_state_s = [ `everCrypt_AEAD_state_s ] structure
    let (everCrypt_AEAD_state_s : [ `everCrypt_AEAD_state_s ] structure typ)
      = structure "EverCrypt_AEAD_state_s_s"
    let everCrypt_AEAD_alg_of_state =
      foreign "EverCrypt_AEAD_alg_of_state"
        ((ptr everCrypt_AEAD_state_s) @-> (returning spec_Agile_AEAD_alg))
    let everCrypt_AEAD_create_in =
      foreign "EverCrypt_AEAD_create_in"
        (spec_Agile_AEAD_alg @->
           ((ptr (ptr everCrypt_AEAD_state_s)) @->
              (ocaml_bytes @-> (returning everCrypt_Error_error_code))))
    let everCrypt_AEAD_encrypt =
      foreign "EverCrypt_AEAD_encrypt"
        ((ptr everCrypt_AEAD_state_s) @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (uint32_t @->
                       (ocaml_bytes @->
                          (uint32_t @->
                             (ocaml_bytes @->
                                (ocaml_bytes @->
                                   (returning everCrypt_Error_error_code))))))))))
    let everCrypt_AEAD_encrypt_expand_aes128_gcm_no_check =
      foreign "EverCrypt_AEAD_encrypt_expand_aes128_gcm_no_check"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (uint32_t @->
                       (ocaml_bytes @->
                          (uint32_t @->
                             (ocaml_bytes @->
                                (ocaml_bytes @->
                                   (returning everCrypt_Error_error_code))))))))))
    let everCrypt_AEAD_encrypt_expand_aes256_gcm_no_check =
      foreign "EverCrypt_AEAD_encrypt_expand_aes256_gcm_no_check"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (uint32_t @->
                       (ocaml_bytes @->
                          (uint32_t @->
                             (ocaml_bytes @->
                                (ocaml_bytes @->
                                   (returning everCrypt_Error_error_code))))))))))
    let everCrypt_AEAD_encrypt_expand_aes128_gcm =
      foreign "EverCrypt_AEAD_encrypt_expand_aes128_gcm"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (uint32_t @->
                       (ocaml_bytes @->
                          (uint32_t @->
                             (ocaml_bytes @->
                                (ocaml_bytes @->
                                   (returning everCrypt_Error_error_code))))))))))
    let everCrypt_AEAD_encrypt_expand_aes256_gcm =
      foreign "EverCrypt_AEAD_encrypt_expand_aes256_gcm"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (uint32_t @->
                       (ocaml_bytes @->
                          (uint32_t @->
                             (ocaml_bytes @->
                                (ocaml_bytes @->
                                   (returning everCrypt_Error_error_code))))))))))
    let everCrypt_AEAD_encrypt_expand_chacha20_poly1305 =
      foreign "EverCrypt_AEAD_encrypt_expand_chacha20_poly1305"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (uint32_t @->
                       (ocaml_bytes @->
                          (uint32_t @->
                             (ocaml_bytes @->
                                (ocaml_bytes @->
                                   (returning everCrypt_Error_error_code))))))))))
    let everCrypt_AEAD_encrypt_expand =
      foreign "EverCrypt_AEAD_encrypt_expand"
        (spec_Agile_AEAD_alg @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (uint32_t @->
                    (ocaml_bytes @->
                       (uint32_t @->
                          (ocaml_bytes @->
                             (uint32_t @->
                                (ocaml_bytes @->
                                   (ocaml_bytes @->
                                      (returning everCrypt_Error_error_code)))))))))))
    let everCrypt_AEAD_decrypt =
      foreign "EverCrypt_AEAD_decrypt"
        ((ptr everCrypt_AEAD_state_s) @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (uint32_t @->
                       (ocaml_bytes @->
                          (uint32_t @->
                             (ocaml_bytes @->
                                (ocaml_bytes @->
                                   (returning everCrypt_Error_error_code))))))))))
    let everCrypt_AEAD_decrypt_expand_aes128_gcm_no_check =
      foreign "EverCrypt_AEAD_decrypt_expand_aes128_gcm_no_check"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (uint32_t @->
                       (ocaml_bytes @->
                          (uint32_t @->
                             (ocaml_bytes @->
                                (ocaml_bytes @->
                                   (returning everCrypt_Error_error_code))))))))))
    let everCrypt_AEAD_decrypt_expand_aes256_gcm_no_check =
      foreign "EverCrypt_AEAD_decrypt_expand_aes256_gcm_no_check"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (uint32_t @->
                       (ocaml_bytes @->
                          (uint32_t @->
                             (ocaml_bytes @->
                                (ocaml_bytes @->
                                   (returning everCrypt_Error_error_code))))))))))
    let everCrypt_AEAD_decrypt_expand_aes128_gcm =
      foreign "EverCrypt_AEAD_decrypt_expand_aes128_gcm"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (uint32_t @->
                       (ocaml_bytes @->
                          (uint32_t @->
                             (ocaml_bytes @->
                                (ocaml_bytes @->
                                   (returning everCrypt_Error_error_code))))))))))
    let everCrypt_AEAD_decrypt_expand_aes256_gcm =
      foreign "EverCrypt_AEAD_decrypt_expand_aes256_gcm"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (uint32_t @->
                       (ocaml_bytes @->
                          (uint32_t @->
                             (ocaml_bytes @->
                                (ocaml_bytes @->
                                   (returning everCrypt_Error_error_code))))))))))
    let everCrypt_AEAD_decrypt_expand_chacha20_poly1305 =
      foreign "EverCrypt_AEAD_decrypt_expand_chacha20_poly1305"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (uint32_t @->
                       (ocaml_bytes @->
                          (uint32_t @->
                             (ocaml_bytes @->
                                (ocaml_bytes @->
                                   (returning everCrypt_Error_error_code))))))))))
    let everCrypt_AEAD_decrypt_expand =
      foreign "EverCrypt_AEAD_decrypt_expand"
        (spec_Agile_AEAD_alg @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (uint32_t @->
                    (ocaml_bytes @->
                       (uint32_t @->
                          (ocaml_bytes @->
                             (uint32_t @->
                                (ocaml_bytes @->
                                   (ocaml_bytes @->
                                      (returning everCrypt_Error_error_code)))))))))))
    let everCrypt_AEAD_free =
      foreign "EverCrypt_AEAD_free"
        ((ptr everCrypt_AEAD_state_s) @-> (returning void))
  end