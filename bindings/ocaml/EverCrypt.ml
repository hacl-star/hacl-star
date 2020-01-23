open Ctypes
open PosixTypes
open Foreign
open Unsigned

open Utils

module EverCrypt_AEAD = EverCrypt_AEAD_bindings.Bindings(EverCrypt_AEAD_stubs)
module EverCrypt_AutoConfig2 = EverCrypt_AutoConfig2_bindings.Bindings(EverCrypt_AutoConfig2_stubs)

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

module AEAD = struct
  open EverCrypt_AEAD

  type t = (everCrypt_AEAD_state_s ptr) ptr

  type alg =
    | AES128_GCM
    | AES256_GCM
    | CHACHA20_POLY1305

  type result =
    | Error of int
    | Success

  let alloc_t () =
    allocate (ptr everCrypt_AEAD_state_s) (from_voidp everCrypt_AEAD_state_s null)

  let create_in alg st key =
    let key = uint8_ptr_of_bigstring key in
    let alg = match alg with
      | AES128_GCM -> spec_Agile_AEAD_alg_Spec_Agile_AEAD_AES128_GCM
      | AES256_GCM -> spec_Agile_AEAD_alg_Spec_Agile_AEAD_AES256_GCM
      | CHACHA20_POLY1305 -> spec_Agile_AEAD_alg_Spec_Agile_AEAD_CHACHA20_POLY1305
    in
    let res = everCrypt_AEAD_create_in alg st key in
    match UInt8.to_int res with
    | 0 -> Success
    | n -> Error n

  let encrypt st iv iv_len ad ad_len pt pt_len ct tag =
    let iv = uint8_ptr_of_bigstring iv in
    let ad = uint8_ptr_of_bigstring ad in
    let pt = uint8_ptr_of_bigstring pt in
    let ct = uint8_ptr_of_bigstring ct in
    let tag = uint8_ptr_of_bigstring tag in
    match UInt8.to_int
            (everCrypt_AEAD_encrypt (!@st)
               iv (UInt32.of_int iv_len)
               ad (UInt32.of_int ad_len)
               pt (UInt32.of_int pt_len) ct tag) with
    | 0 -> Success
    | n -> Error n

  let decrypt st iv iv_len ad ad_len ct ct_len tag dt =
    let iv = uint8_ptr_of_bigstring iv in
    let ad = uint8_ptr_of_bigstring ad in
    let ct = uint8_ptr_of_bigstring ct in
    let tag = uint8_ptr_of_bigstring tag in
    let dt = uint8_ptr_of_bigstring dt in
    match UInt8.to_int
            (everCrypt_AEAD_decrypt (!@st)
               iv (UInt32.of_int iv_len)
               ad (UInt32.of_int ad_len)
               ct (UInt32.of_int ct_len) tag dt) with
    | 0 -> Success
    | n -> Error n

end
