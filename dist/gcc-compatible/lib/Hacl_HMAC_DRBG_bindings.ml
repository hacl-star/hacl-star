open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    module Hacl_Spec_applied = (Hacl_Spec_bindings.Bindings)(Hacl_Spec_stubs)
    open Hacl_Spec_applied
    type hacl_HMAC_DRBG_supported_alg = spec_Hash_Definitions_hash_alg
    let hacl_HMAC_DRBG_supported_alg =
      typedef spec_Hash_Definitions_hash_alg "Hacl_HMAC_DRBG_supported_alg"
    let hacl_HMAC_DRBG_reseed_interval =
      foreign_value "Hacl_HMAC_DRBG_reseed_interval" uint32_t
    let hacl_HMAC_DRBG_max_output_length =
      foreign_value "Hacl_HMAC_DRBG_max_output_length" uint32_t
    let hacl_HMAC_DRBG_max_length =
      foreign_value "Hacl_HMAC_DRBG_max_length" uint32_t
    let hacl_HMAC_DRBG_max_personalization_string_length =
      foreign_value "Hacl_HMAC_DRBG_max_personalization_string_length"
        uint32_t
    let hacl_HMAC_DRBG_max_additional_input_length =
      foreign_value "Hacl_HMAC_DRBG_max_additional_input_length" uint32_t
    let hacl_HMAC_DRBG_min_length =
      foreign "Hacl_HMAC_DRBG_min_length"
        (spec_Hash_Definitions_hash_alg @-> (returning uint32_t))
    type hacl_HMAC_DRBG_state = [ `hacl_HMAC_DRBG_state ] structure
    let (hacl_HMAC_DRBG_state : [ `hacl_HMAC_DRBG_state ] structure typ) =
      structure "Hacl_HMAC_DRBG_state_s"
    let hacl_HMAC_DRBG_state_k = field hacl_HMAC_DRBG_state "k" (ptr uint8_t)
    let hacl_HMAC_DRBG_state_v = field hacl_HMAC_DRBG_state "v" (ptr uint8_t)
    let hacl_HMAC_DRBG_state_reseed_counter =
      field hacl_HMAC_DRBG_state "reseed_counter" (ptr uint32_t)
    let _ = seal hacl_HMAC_DRBG_state
    let hacl_HMAC_DRBG_create_in =
      foreign "Hacl_HMAC_DRBG_create_in"
        (spec_Hash_Definitions_hash_alg @-> (returning hacl_HMAC_DRBG_state))
    let hacl_HMAC_DRBG_instantiate =
      foreign "Hacl_HMAC_DRBG_instantiate"
        (spec_Hash_Definitions_hash_alg @->
           (hacl_HMAC_DRBG_state @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (uint32_t @->
                       (ocaml_bytes @->
                          (uint32_t @-> (ocaml_bytes @-> (returning void)))))))))
    let hacl_HMAC_DRBG_reseed =
      foreign "Hacl_HMAC_DRBG_reseed"
        (spec_Hash_Definitions_hash_alg @->
           (hacl_HMAC_DRBG_state @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (uint32_t @-> (ocaml_bytes @-> (returning void)))))))
    let hacl_HMAC_DRBG_generate =
      foreign "Hacl_HMAC_DRBG_generate"
        (spec_Hash_Definitions_hash_alg @->
           (ocaml_bytes @->
              (hacl_HMAC_DRBG_state @->
                 (uint32_t @->
                    (uint32_t @-> (ocaml_bytes @-> (returning bool)))))))
  end