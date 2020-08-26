open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    module Hacl_Spec_applied = (Hacl_Spec_bindings.Bindings)(Hacl_Spec_stubs)
    open Hacl_Spec_applied
    module EverCrypt_Error_applied =
      (EverCrypt_Error_bindings.Bindings)(EverCrypt_Error_stubs)
    open EverCrypt_Error_applied
    type everCrypt_CTR_state_s = [ `everCrypt_CTR_state_s ] structure
    let (everCrypt_CTR_state_s : [ `everCrypt_CTR_state_s ] structure typ) =
      structure "EverCrypt_CTR_state_s_s"
    let everCrypt_CTR_xor8 =
      foreign "EverCrypt_CTR_xor8"
        (uint8_t @-> (uint8_t @-> (returning uint8_t)))
    let everCrypt_CTR_alg_of_state =
      foreign "EverCrypt_CTR_alg_of_state"
        ((ptr everCrypt_CTR_state_s) @->
           (returning spec_Agile_Cipher_cipher_alg))
    let everCrypt_CTR_create_in =
      foreign "EverCrypt_CTR_create_in"
        (spec_Agile_Cipher_cipher_alg @->
           ((ptr (ptr everCrypt_CTR_state_s)) @->
              (ocaml_bytes @->
                 (ocaml_bytes @->
                    (uint32_t @->
                       (uint32_t @-> (returning everCrypt_Error_error_code)))))))
    let everCrypt_CTR_init =
      foreign "EverCrypt_CTR_init"
        ((ptr everCrypt_CTR_state_s) @->
           (ocaml_bytes @->
              (ocaml_bytes @-> (uint32_t @-> (uint32_t @-> (returning void))))))
    let everCrypt_CTR_update_block =
      foreign "EverCrypt_CTR_update_block"
        ((ptr everCrypt_CTR_state_s) @->
           (ocaml_bytes @-> (ocaml_bytes @-> (returning void))))
    let everCrypt_CTR_free =
      foreign "EverCrypt_CTR_free"
        ((ptr everCrypt_CTR_state_s) @-> (returning void))
  end