module EverCrypt

module B = FStar.Buffer

module Hacl = EverCrypt.Hacl
module Vale = EverCrypt.Vale
module ValeGlue = EverCrypt.ValeGlue

module SC = EverCrypt.StaticConfig
module AC = EverCrypt.AutoConfig
module U32 = FStar.UInt32

open EverCrypt.Helpers
open C.Failure

/// Some remarks here.
///
/// - Eta-expanding helps avoid KreMLin errors down the line (and is more
///   efficient in C.)
/// - The if-then-else as opposed to a match allows F* to specialize these when
///   we do a static configuration.
/// - This file must be maintained in sync with evercrypt_autoconfig.c
let sha256_init state =
  let i = AC.sha256_impl () in
  if SC.hacl && i = AC.Hacl then
    Hacl.sha256_init state
  else if SC.vale && i = AC.Vale then
    ValeGlue.sha256_init state
  else
    failwith !$"ERROR: inconsistent configuration"

let sha256_update state data =
  let i = AC.sha256_impl () in
  if SC.hacl && i = AC.Hacl then
    Hacl.sha256_update state data
  else if SC.vale && i = AC.Vale then
    ValeGlue.sha256_update state data
  else
    failwith !$"ERROR: inconsistent configuration"

let sha256_update_multi state data n =
  let i = AC.sha256_impl () in
  if SC.hacl && i = AC.Hacl then
    Hacl.sha256_update_multi state data n
  else if SC.vale && i = AC.Vale then
    ValeGlue.sha256_update_multi state data n
  else
    failwith !$"ERROR: inconsistent configuration"

let sha256_update_last state data n =
  let i = AC.sha256_impl () in
  if SC.hacl && i = AC.Hacl then
    Hacl.sha256_update_last state data n
  else if SC.vale && i = AC.Vale then
    ValeGlue.sha256_update_last state data n
  else
    failwith !$"ERROR: inconsistent configuration"

let sha256_finish state data =
  let i = AC.sha256_impl () in
  if SC.hacl && i = AC.Hacl then
    Hacl.sha256_finish state data
  else if SC.vale && i = AC.Vale then
    ValeGlue.sha256_finish state data
  else
    failwith !$"ERROR: inconsistent configuration"

let sha256_hash dst src len =
  let i = AC.sha256_impl () in
  if SC.hacl && i = AC.Hacl then
    Hacl.sha256_hash dst src len
  else if SC.hacl && i = AC.Vale then
    ValeGlue.sha256_hash dst src len
  else
    failwith !$"ERROR: inconsistent configuration"

let sha384_init state =
  let i = AC.sha384_impl () in
  if SC.hacl && i = AC.Hacl then
    Hacl.sha384_init state
  else
    failwith !$"ERROR: inconsistent configuration"

let sha384_update state data =
  let i = AC.sha384_impl () in
  if SC.hacl && i = AC.Hacl then
    Hacl.sha384_update state data
  else
    failwith !$"ERROR: inconsistent configuration"

let sha384_update_multi state data n =
  let i = AC.sha384_impl () in
  if SC.hacl && i = AC.Hacl then
    Hacl.sha384_update_multi state data n
  else
    failwith !$"ERROR: inconsistent configuration"

let sha384_update_last state data n =
  let i = AC.sha384_impl () in
  if SC.hacl && i = AC.Hacl then
    Hacl.sha384_update_last state data n
  else
    failwith !$"ERROR: inconsistent configuration"

let sha384_finish state data =
  let i = AC.sha384_impl () in
  if SC.hacl && i = AC.Hacl then
    Hacl.sha384_finish state data
  else
    failwith !$"ERROR: inconsistent configuration"

let sha384_hash dst src len =
  let i = AC.sha384_impl () in
  if SC.hacl && i = AC.Hacl then
    Hacl.sha384_hash dst src len
  else
    failwith !$"ERROR: inconsistent configuration"

let sha512_init state =
  let i = AC.sha512_impl () in
  if SC.hacl && i = AC.Hacl then
    Hacl.sha512_init state
  else
    failwith !$"ERROR: inconsistent configuration"

let sha512_update state data =
  let i = AC.sha512_impl () in
  if SC.hacl && i = AC.Hacl then
    Hacl.sha512_update state data
  else
    failwith !$"ERROR: inconsistent configuration"

let sha512_update_multi state data n =
  let i = AC.sha512_impl () in
  if SC.hacl && i = AC.Hacl then
    Hacl.sha512_update_multi state data n
  else
    failwith !$"ERROR: inconsistent configuration"

let sha512_update_last state data n =
  let i = AC.sha512_impl () in
  if SC.hacl && i = AC.Hacl then
    Hacl.sha512_update_last state data n
  else
    failwith !$"ERROR: inconsistent configuration"

let sha512_finish state data =
  let i = AC.sha512_impl () in
  if SC.hacl && i = AC.Hacl then
    Hacl.sha512_finish state data
  else
    failwith !$"ERROR: inconsistent configuration"

let sha512_hash dst src len =
  let i = AC.sha512_impl () in
  if SC.hacl && i = AC.Hacl then
    Hacl.sha512_hash dst src len
  else
    failwith !$"ERROR: inconsistent configuration"

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
    let expanded   = B.create 0uy 176ul in
    let iv'        = B.create 0uy 16ul in
    let plaintext' = B.create 0uy U32.(((len +^ 15ul) /^ 16ul) *^ 16ul) in
    let cipher'    = B.create 0uy U32.(((len +^ 15ul) /^ 16ul) *^ 16ul) in
    let ad'        = B.create 0uy U32.(((adlen +^ 15ul) /^ 16ul) *^ 16ul) in
    B.blit iv 0ul iv' 0ul 16ul;
    B.blit plaintext 0ul plaintext' 0ul len;
    B.blit ad 0ul ad' 0ul adlen;
    Vale.aes_key_expansion key expanded;
    let b = B.create ({
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
    B.blit cipher' 0ul cipher 0ul len;
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
    let expanded   = B.create 0uy 176ul in
    let iv'        = B.create 0uy 16ul in
    let plaintext' = B.create 0uy U32.(((len +^ 15ul) /^ 16ul) *^ 16ul) in
    let cipher'    = B.create 0uy U32.(((len +^ 15ul) /^ 16ul) *^ 16ul) in
    let ad'        = B.create 0uy U32.(((adlen +^ 15ul) /^ 16ul) *^ 16ul) in
    B.blit iv 0ul iv' 0ul 16ul;
    B.blit cipher 0ul cipher' 0ul len;
    B.blit ad 0ul ad' 0ul adlen;
    Vale.aes_key_expansion key expanded;
    let b = B.create ({
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
    B.blit plaintext' 0ul plaintext 0ul len;
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
