open Ctypes
open PosixTypes
open Foreign
open Unsigned

open Utils

module EverCrypt_AutoConfig2 = EverCrypt_AutoConfig2_bindings.Bindings(EverCrypt_AutoConfig2_stubs)
module EverCrypt_AEAD = EverCrypt_AEAD_bindings.Bindings(EverCrypt_AEAD_stubs)

module AutoConfig2 = struct
  open EverCrypt_AutoConfig2
  let has_shaext () = everCrypt_AutoConfig2_has_shaext ()
  let has_aesni () = everCrypt_AutoConfig2_has_aesni ()
  let has_pclmulqdq () = everCrypt_AutoConfig2_has_pclmulqdq ()
  let has_avx2 () = everCrypt_AutoConfig2_has_avx2 ()
  let has_avx () = everCrypt_AutoConfig2_has_avx ()
  let has_bmi2 () = everCrypt_AutoConfig2_has_bmi2 ()
  let has_adx () = everCrypt_AutoConfig2_has_adx ()
  let has_sse () = everCrypt_AutoConfig2_has_sse ()
  let has_movbe () = everCrypt_AutoConfig2_has_movbe ()
  let has_rdrand () = everCrypt_AutoConfig2_has_rdrand ()
  let wants_vale () = everCrypt_AutoConfig2_wants_vale ()
  let wants_hacl () = everCrypt_AutoConfig2_wants_hacl ()
  let wants_openssl () = everCrypt_AutoConfig2_wants_openssl ()
  let wants_bcrypt () = everCrypt_AutoConfig2_wants_bcrypt ()
  let recall () = everCrypt_AutoConfig2_recall ()
  let init () = everCrypt_AutoConfig2_init ()
  let disable_avx2 () = everCrypt_AutoConfig2_disable_avx2 ()
  let disable_avx () = everCrypt_AutoConfig2_disable_avx ()
  let disable_bmi2 () = everCrypt_AutoConfig2_disable_bmi2 ()
  let disable_adx () = everCrypt_AutoConfig2_disable_adx ()
  let disable_shaext () = everCrypt_AutoConfig2_disable_shaext ()
  let disable_aesni () = everCrypt_AutoConfig2_disable_aesni ()
  let disable_pclmulqdq () = everCrypt_AutoConfig2_disable_pclmulqdq ()
  let disable_sse () = everCrypt_AutoConfig2_disable_sse ()
  let disable_movbe () = everCrypt_AutoConfig2_disable_movbe ()
  let disable_rdrand () = everCrypt_AutoConfig2_disable_rdrand ()
  let disable_vale () = everCrypt_AutoConfig2_disable_vale ()
  let disable_hacl () = everCrypt_AutoConfig2_disable_hacl ()
  let disable_openssl () = everCrypt_AutoConfig2_disable_openssl ()
  let disable_bcrypt () = everCrypt_AutoConfig2_disable_bcrypt ()
end

module Error = struct
  type error_code =
    | UnsupportedAlgorithm
    | InvalidKey
    | AuthenticationFailure
    | InvalidIVLength
    | DecodeError
  type result =
    | Success
    | Error of error_code
  let error n =
    let err = match n with
      | 1 -> UnsupportedAlgorithm
      | 2 -> InvalidKey
      | 3 -> AuthenticationFailure
      | 4 -> InvalidIVLength
      | 5 -> DecodeError
      | _ -> failwith "Impossible"
    in
    Error err
  let get_result r = match UInt8.to_int r with
    | 0 -> Success
    | n -> error n
end

module AEAD = struct
  open Error
  open EverCrypt_AEAD

  type t = (everCrypt_AEAD_state_s ptr) ptr
  type alg =
    | AES128_GCM
    | AES256_GCM
    | CHACHA20_POLY1305
  type result_init =
    | Success of t
    | Err of int
  let init alg key : result_init =
    let st = allocate (ptr everCrypt_AEAD_state_s) (from_voidp everCrypt_AEAD_state_s null) in
    let alg = match alg with
      | AES128_GCM -> spec_Agile_AEAD_alg_Spec_Agile_AEAD_AES128_GCM
      | AES256_GCM -> spec_Agile_AEAD_alg_Spec_Agile_AEAD_AES256_GCM
      | CHACHA20_POLY1305 -> spec_Agile_AEAD_alg_Spec_Agile_AEAD_CHACHA20_POLY1305
    in
    match UInt8.to_int
            (everCrypt_AEAD_create_in alg st (uint8_ptr key)) with
    | 0 -> Success st
    | n -> Err n
  let encrypt st iv ad pt ct tag : result =
    get_result (everCrypt_AEAD_encrypt (!@st)
                  (uint8_ptr iv) (size_uint32 iv) (uint8_ptr ad) (size_uint32 ad)
                  (uint8_ptr pt) (size_uint32 pt) (uint8_ptr ct) (uint8_ptr tag))
  let decrypt st iv ad ct tag dt : result =
    get_result (everCrypt_AEAD_decrypt (!@st)
                  (uint8_ptr iv) (size_uint32 iv) (uint8_ptr ad) (size_uint32 ad)
                  (uint8_ptr ct) (size_uint32 ct) (uint8_ptr tag) (uint8_ptr dt))
end
