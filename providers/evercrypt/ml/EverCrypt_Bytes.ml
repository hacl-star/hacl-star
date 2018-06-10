open Ctypes
open PosixTypes
open Foreign

(* This module implements EverCrypt.Bytes, using fstarlib's `type bytes =
 * string`. *)

(* See Santiago's comment in PKI.ml *)
let () =
  if Sys.os_type = "Win32" then
    ignore (Dl.dlopen ~filename:"libevercrypt.so" ~flags:[])

let x25519_ =
  foreign "EverCrypt_x25519" (
    ptr char @->
    string @->
    string @->
    returning void)

let x25519 secret base =
  let dst = allocate_n char 32 in
  x25519_ dst secret base;
  string_from_ptr dst 32


type cipher_tag = {
  cipher: string;
  tag:    string
}

let chacha20_poly1305_encrypt_ =
  foreign "EverCrypt_chacha20_poly1305_encrypt" (
    ptr char @->
    ptr char @->
    string @->
    uint32_t @->
    string @->
    uint32_t @->
    string @->
    string @->
    returning uint32_t)

let chacha20_poly1305_encrypt m aad k n =
  let m_len   = String.length m in
  let aad_len = String.length aad in
  let cipher  = allocate_n char m_len in
  let tag     = allocate_n char 16 in
  let _ = chacha20_poly1305_encrypt_ cipher tag
            m   (Unsigned.UInt32.of_int m_len)
            aad (Unsigned.UInt32.of_int aad_len) k n in
  { cipher = string_from_ptr cipher m_len;
    tag    = string_from_ptr tag 16 }

type maybe_plaintext =
| Error
| Correct of string

let chacha20_poly1305_decrypt_ =
  foreign "EverCrypt_chacha20_poly1305_decrypt" (
    ptr char @->
    string @->
    uint32_t @->
    string @->
    string @->
    uint32_t @->
    string @->
    string @->
    returning uint32_t)

let chacha20_poly1305_decrypt c tag aad k n =
  let m_len   = String.length c in
  let aad_len = String.length aad in
  let m       = allocate_n char m_len in
  let res = chacha20_poly1305_decrypt_ m c
            (Unsigned.UInt32.of_int m_len) tag aad
            (Unsigned.UInt32.of_int aad_len) k n in
  if Unsigned.UInt32.to_int res = 0 then
    Correct (string_from_ptr m m_len)
  else Error
