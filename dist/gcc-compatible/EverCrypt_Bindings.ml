open Ctypes
open PosixTypes
open Foreign

module EverCrypt_AEAD = EverCrypt_AEAD_bindings.Bindings(EverCrypt_AEAD_stubs)

let uint8_ptr_of_bigstring buf = from_voidp uint8_t (to_voidp (bigarray_start array1 buf))

module AEAD = struct
  type t = (EverCrypt_AEAD.everCrypt_AEAD_state_s ptr) ptr

  type alg =
    | AES128_GCM
    | AES256_GCM
    | CHACHA20_POLY1305

  type result =
    | Error of int
    | Success

  let alloc_t () =
    allocate (ptr EverCrypt_AEAD.everCrypt_AEAD_state_s) (from_voidp EverCrypt_AEAD.everCrypt_AEAD_state_s null)

  let create_in alg st key =
    let key = uint8_ptr_of_bigstring key in
    let alg = match alg with
      | AES128_GCM -> EverCrypt_AEAD.spec_Agile_AEAD_alg_Spec_Agile_AEAD_AES128_GCM
      | AES256_GCM -> EverCrypt_AEAD.spec_Agile_AEAD_alg_Spec_Agile_AEAD_AES256_GCM
      | CHACHA20_POLY1305 -> EverCrypt_AEAD.spec_Agile_AEAD_alg_Spec_Agile_AEAD_CHACHA20_POLY1305
    in
    let res = EverCrypt_AEAD.everCrypt_AEAD_create_in alg st key in
    match Unsigned.UInt8.to_int res with
    | 0 -> Success
    | n -> Error n

  let encrypt st iv iv_len ad ad_len pt pt_len ct tag =
    let iv = uint8_ptr_of_bigstring iv in
    let ad = uint8_ptr_of_bigstring ad in
    let pt = uint8_ptr_of_bigstring pt in
    let ct = uint8_ptr_of_bigstring ct in
    let tag = uint8_ptr_of_bigstring tag in
    match Unsigned.UInt8.to_int (EverCrypt_AEAD.everCrypt_AEAD_encrypt (!@st)
                                   iv (Unsigned.UInt32.of_int iv_len)
                                   ad (Unsigned.UInt32.of_int ad_len)
                                   pt (Unsigned.UInt32.of_int pt_len) ct tag) with
    | 0 -> Success
    | n -> Error n

  let decrypt st iv iv_len ad ad_len ct ct_len tag dt =
    let iv = uint8_ptr_of_bigstring iv in
    let ad = uint8_ptr_of_bigstring ad in
    let ct = uint8_ptr_of_bigstring ct in
    let tag = uint8_ptr_of_bigstring tag in
    let dt = uint8_ptr_of_bigstring dt in
    match Unsigned.UInt8.to_int (EverCrypt_AEAD.everCrypt_AEAD_decrypt (!@st)
                                   iv (Unsigned.UInt32.of_int iv_len)
                                   ad (Unsigned.UInt32.of_int ad_len)
                                   ct (Unsigned.UInt32.of_int ct_len) tag dt) with
    | 0 -> Success
    | n -> Error n

end
