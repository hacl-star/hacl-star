module EverCrypt

module B = LowStar.Buffer

module Hacl = EverCrypt.Hacl
module Vale = EverCrypt.Vale
module ValeGlue = EverCrypt.ValeGlue

module SC = EverCrypt.StaticConfig
module AC = EverCrypt.AutoConfig
module U32 = FStar.UInt32

open EverCrypt.Helpers
open C.Failure
open LowStar.BufferOps

let x25519 dst secret base =
  let i = AC.x25519_impl () in
  if SC.hacl && i = AC.Hacl then
    Hacl.x25519 dst secret base
  else
    failwith !$"ERROR: inconsistent configuration"

let aes128_gcm_encrypt key iv ad adlen plaintext len cipher tag =
  let i = AC.aes128_gcm_impl () in
  if SC.vale && i = AC.Vale then begin
    push_frame ();
    let open EverCrypt.Vale in
    let expanded   = B.alloca 0uy 176ul in
    let iv'        = B.alloca 0uy 16ul in
    let plaintext' = B.alloca 0uy U32.(((len +^ 15ul) /^ 16ul) *^ 16ul) in
    let cipher'    = B.alloca 0uy U32.(((len +^ 15ul) /^ 16ul) *^ 16ul) in
    let ad'        = B.alloca 0uy U32.(((adlen +^ 15ul) /^ 16ul) *^ 16ul) in
    blit iv 0ul iv' 0ul 16ul;
    blit plaintext 0ul plaintext' 0ul len;
    blit ad 0ul ad' 0ul adlen;
    Vale.aes_key_expansion key expanded;
    let b = B.alloca ({
      plain = plaintext';
      plain_len = FStar.Int.Cast.Full.uint32_to_uint64 len;
      aad = ad';
      aad_len = FStar.Int.Cast.Full.uint32_to_uint64 adlen;
      iv = iv';
      expanded_key = expanded;
      cipher = cipher';
      tag = tag
    }) 1ul in
    Vale.gcm_encrypt b;
    blit cipher' 0ul cipher 0ul len;
    pop_frame ()
  end
  else if SC.openssl && i = AC.OpenSSL then
    EverCrypt.OpenSSL.aes128_gcm_encrypt key iv ad adlen plaintext len cipher tag
  else if SC.bcrypt && i = AC.BCrypt then
    EverCrypt.BCrypt.aes128_gcm_encrypt key iv ad adlen plaintext len cipher tag
  else
    failwith !$"ERROR: inconsistent configuration"

let aes128_gcm_decrypt key iv ad adlen plaintext len cipher tag =
  let i = AC.aes128_gcm_impl () in
  if SC.vale && i = AC.Vale then begin
    push_frame ();
    let open EverCrypt.Vale in
    let expanded   = B.alloca 0uy 176ul in
    let iv'        = B.alloca 0uy 16ul in
    let plaintext' = B.alloca 0uy U32.(((len +^ 15ul) /^ 16ul) *^ 16ul) in
    let cipher'    = B.alloca 0uy U32.(((len +^ 15ul) /^ 16ul) *^ 16ul) in
    let ad'        = B.alloca 0uy U32.(((adlen +^ 15ul) /^ 16ul) *^ 16ul) in
    blit iv 0ul iv' 0ul 16ul;
    blit cipher 0ul cipher' 0ul len;
    blit ad 0ul ad' 0ul adlen;
    Vale.aes_key_expansion key expanded;
    let b = B.alloca ({
      plain = cipher';
      plain_len = FStar.Int.Cast.Full.uint32_to_uint64 len;
      aad = ad';
      aad_len = FStar.Int.Cast.Full.uint32_to_uint64 adlen;
      iv = iv';
      expanded_key = expanded;
      cipher = plaintext';
      tag = tag
    }) 1ul in
    let ret = Vale.gcm_decrypt b in
    blit plaintext' 0ul plaintext 0ul len;
    pop_frame ();
    // FIXME: restore tag verification once Vale is fixed
    //U32.(1ul -^ ret)
    1ul
    end
  else if SC.openssl && i = AC.OpenSSL then
    EverCrypt.OpenSSL.aes128_gcm_decrypt key iv ad adlen plaintext len cipher tag
  else if SC.bcrypt && i = AC.BCrypt then
    EverCrypt.BCrypt.aes128_gcm_decrypt key iv ad adlen plaintext len cipher tag
  else
    failwith !$"ERROR: inconsistent configuration"

let aes256_gcm_encrypt key iv ad adlen plaintext len cipher tag =
  let i = AC.aes256_gcm_impl () in
  if SC.openssl && i = AC.OpenSSL then
    EverCrypt.OpenSSL.aes256_gcm_encrypt key iv ad adlen plaintext len cipher tag
  else if SC.bcrypt && i = AC.BCrypt then
    EverCrypt.BCrypt.aes256_gcm_encrypt key iv ad adlen plaintext len cipher tag
  else
    failwith !$"ERROR: inconsistent configuration"

let aes256_gcm_decrypt key iv ad adlen plaintext len cipher tag =
  let i = AC.aes256_gcm_impl () in
  if SC.openssl && i = AC.OpenSSL then
    EverCrypt.OpenSSL.aes256_gcm_decrypt key iv ad adlen plaintext len cipher tag
  else if SC.bcrypt && i = AC.BCrypt then
    EverCrypt.BCrypt.aes256_gcm_decrypt key iv ad adlen plaintext len cipher tag
  else
    failwith !$"ERROR: inconsistent configuration"

let chacha20_poly1305_encode_length lb aad_len m_len =
  let i = AC.chacha20_poly1305_impl () in
  if SC.hacl && i = AC.Hacl then
    EverCrypt.Hacl.chacha20_poly1305_encode_length lb aad_len m_len
  else
    failwith !$"ERROR: inconsistent configuration"

let chacha20_poly1305_encrypt key iv ad adlen plaintext len cipher tag =
  let i = AC.chacha20_poly1305_impl () in
  if SC.hacl && i = AC.Hacl then
    ignore (EverCrypt.Hacl.chacha20_poly1305_encrypt cipher tag plaintext len ad adlen key iv)
  else if SC.openssl && i = AC.OpenSSL then
    EverCrypt.OpenSSL.chacha20_poly1305_encrypt key iv ad adlen plaintext len cipher tag
  else
    failwith !$"ERROR: inconsistent configuration"

let chacha20_poly1305_decrypt key iv ad adlen plaintext len cipher tag =
  let i = AC.chacha20_poly1305_impl () in
  if SC.hacl && i = AC.Hacl then
    U32.(1ul -^ EverCrypt.Hacl.chacha20_poly1305_decrypt plaintext cipher len tag ad adlen key iv)
  else if SC.openssl && i = AC.OpenSSL then
    EverCrypt.OpenSSL.chacha20_poly1305_decrypt key iv ad adlen plaintext len cipher tag
  else
    failwith !$"ERROR: inconsistent configuration"
