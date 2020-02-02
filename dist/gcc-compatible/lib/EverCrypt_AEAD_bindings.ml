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
    let everCrypt_AEAD_state_s_impl =
      field everCrypt_AEAD_state_s "impl" spec_Cipher_Expansion_impl 
    let everCrypt_AEAD_state_s_ek =
      field everCrypt_AEAD_state_s "ek" (ptr uint8_t) 
    let _ = seal everCrypt_AEAD_state_s 
    let everCrypt_AEAD_alg_of_state =
      foreign "EverCrypt_AEAD_alg_of_state"
        ((ptr everCrypt_AEAD_state_s) @-> (returning spec_Agile_AEAD_alg))
      
    let everCrypt_AEAD_create_in =
      foreign "EverCrypt_AEAD_create_in"
        (spec_Agile_AEAD_alg @->
           ((ptr (ptr everCrypt_AEAD_state_s)) @->
              ((ptr uint8_t) @-> (returning everCrypt_Error_error_code))))
      
    let everCrypt_AEAD_encrypt =
      foreign "EverCrypt_AEAD_encrypt"
        ((ptr everCrypt_AEAD_state_s) @->
           ((ptr uint8_t) @->
              (uint32_t @->
                 ((ptr uint8_t) @->
                    (uint32_t @->
                       ((ptr uint8_t) @->
                          (uint32_t @->
                             ((ptr uint8_t) @->
                                ((ptr uint8_t) @->
                                   (returning everCrypt_Error_error_code))))))))))
      
    let everCrypt_AEAD_decrypt =
      foreign "EverCrypt_AEAD_decrypt"
        ((ptr everCrypt_AEAD_state_s) @->
           ((ptr uint8_t) @->
              (uint32_t @->
                 ((ptr uint8_t) @->
                    (uint32_t @->
                       ((ptr uint8_t) @->
                          (uint32_t @->
                             ((ptr uint8_t) @->
                                ((ptr uint8_t) @->
                                   (returning everCrypt_Error_error_code))))))))))
      
    let everCrypt_AEAD_free =
      foreign "EverCrypt_AEAD_free"
        ((ptr everCrypt_AEAD_state_s) @-> (returning void))
      
  end