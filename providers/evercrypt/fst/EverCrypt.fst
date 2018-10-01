module EverCrypt

module B = LowStar.Buffer

module BCrypt = EverCrypt.BCrypt
module Hacl = EverCrypt.Hacl
module OpenSSL = EverCrypt.OpenSSL
module Vale = EverCrypt.Vale
module ValeGlue = EverCrypt.ValeGlue

module SC = EverCrypt.StaticConfig
module AC = EverCrypt.AutoConfig
module U32 = FStar.UInt32
module HS = FStar.HyperStack

open EverCrypt.Helpers
open C.Failure
open LowStar.BufferOps

/// X25519

let x25519 dst secret base =
  let i = AC.x25519_impl () in
  if SC.hacl && i = AC.Hacl then
    Hacl.x25519 dst secret base
  else
    failwith !$"ERROR: inconsistent configuration"

/// AES128-ECB

[@CAbstractStruct]
noeq type aes128_key_s =
  | AES128_OPENSSL: st:Dyn.dyn -> aes128_key_s
  | AES128_BCRYPT: st:Dyn.dyn -> aes128_key_s
  | AES128_VALE: w:uint8_p -> sbox:uint8_p -> aes128_key_s
  | AES128_HACL: w:uint8_p -> sbox:uint8_p -> aes128_key_s

let aes128_create k =
  let i = AC.aes128_impl () in
  let st =
    if SC.vale && i = AC.Vale then
      let w    = B.malloc HS.root 0uy 176ul in
      let sbox = B.malloc HS.root 0uy 256ul in
      Vale.aes128_key_expansion_sbox k w sbox;
      AES128_VALE w sbox
    else if SC.hacl && i = AC.Hacl then
      let w    = B.malloc HS.root 0uy 176ul in
      let sbox = B.malloc HS.root 0uy 256ul in
      Hacl.aes128_keyExpansion k w sbox;
      AES128_HACL w sbox
  //  else if SC.openssl && i = AC.OpenSSL then
  //    EverCrypt.OpenSSL.aes128_gcm_encrypt key iv ad adlen plaintext len cipher tag
  //  else if SC.bcrypt && i = AC.BCrypt then
  //    EverCrypt.BCrypt.aes128_gcm_encrypt key iv ad adlen plaintext len cipher tag
    else
      failwith !$"ERROR: inconsistent configuration"
  in
  B.malloc HS.root st 1ul

let aes128_compute k plain cipher =
  let k = !*k in
  if SC.vale && AES128_VALE? k then
    let AES128_VALE w sbox = k in
    Vale.aes128_encrypt_one_block cipher plain w sbox
  else if SC.hacl && AES128_HACL? k then
    let AES128_HACL w sbox = k in
    Hacl.aes128_cipher cipher plain w sbox
//  else if SC.openssl && i = AC.OpenSSL then
//    EverCrypt.OpenSSL.aes128_gcm_encrypt key iv ad adlen plaintext len cipher tag
//  else if SC.bcrypt && i = AC.BCrypt then
//    EverCrypt.BCrypt.aes128_gcm_encrypt key iv ad adlen plaintext len cipher tag
  else
    failwith !$"ERROR: inconsistent configuration"

let aes128_free pk =
  let k = !*pk in
  if SC.vale && AES128_VALE? k then
    let AES128_VALE w sbox = k in
    B.free w;
    B.free sbox
  else if SC.hacl && AES128_HACL? k then
    let AES128_HACL w sbox = k in
    B.free w;
    B.free sbox
//  else if SC.openssl && i = AC.OpenSSL then
//    EverCrypt.OpenSSL.aes128_gcm_encrypt key iv ad adlen plaintext len cipher tag
//  else if SC.bcrypt && i = AC.BCrypt then
//    EverCrypt.BCrypt.aes128_gcm_encrypt key iv ad adlen plaintext len cipher tag
  else
    failwith !$"ERROR: inconsistent configuration";
  B.free pk

[@CAbstractStruct]
noeq type aes256_key_s =
  | AES256_OPENSSL: st:Dyn.dyn -> aes256_key_s
  | AES256_BCRYPT: st:Dyn.dyn -> aes256_key_s
  | AES256_HACL: w:uint8_p -> sbox:uint8_p -> aes256_key_s

let aes256_create k =
  let i = AC.aes256_impl () in
  let st =
    if SC.hacl && i = AC.Hacl then
      let w    = B.malloc HS.root 0uy 240ul in
      let sbox = B.malloc HS.root 0uy 256ul in
      Hacl.aes256_keyExpansion k w sbox;
      AES256_HACL w sbox
  //  else if SC.openssl && i = AC.OpenSSL then
  //    EverCrypt.OpenSSL.aes128_gcm_encrypt key iv ad adlen plaintext len cipher tag
  //  else if SC.bcrypt && i = AC.BCrypt then
  //    EverCrypt.BCrypt.aes128_gcm_encrypt key iv ad adlen plaintext len cipher tag
    else
      failwith !$"ERROR: inconsistent configuration"
  in
  B.malloc HS.root st 1ul

let aes256_compute k plain cipher =
  let k = !*k in
  if SC.hacl && AES256_HACL? k then
    let AES256_HACL w sbox = k in
    Hacl.aes256_cipher cipher plain w sbox
//  else if SC.openssl && i = AC.OpenSSL then
//    EverCrypt.OpenSSL.aes128_gcm_encrypt key iv ad adlen plaintext len cipher tag
//  else if SC.bcrypt && i = AC.BCrypt then
//    EverCrypt.BCrypt.aes128_gcm_encrypt key iv ad adlen plaintext len cipher tag
  else
    failwith !$"ERROR: inconsistent configuration"

let aes256_free pk =
  let k = !*pk in
  if SC.hacl && AES256_HACL? k then
    let AES256_HACL w sbox = k in
    B.free w;
    B.free sbox
//  else if SC.openssl && i = AC.OpenSSL then
//    EverCrypt.OpenSSL.aes128_gcm_encrypt key iv ad adlen plaintext len cipher tag
//  else if SC.bcrypt && i = AC.BCrypt then
//    EverCrypt.BCrypt.aes128_gcm_encrypt key iv ad adlen plaintext len cipher tag
  else
    failwith !$"ERROR: inconsistent configuration";
  B.free pk

/// ChaCha20

let chacha20 key iv ctr plain len cipher =
  let i = AC.chacha20_impl () in
  if SC.hacl && i = AC.Hacl then
    EverCrypt.Hacl.chacha20 key iv ctr plain len cipher
  else
    failwith !$"ERROR: inconsistent configuration"

/// AES128-GCM

// TODO move to ValeGlue
private inline_for_extraction
let vale_aes128_gcm_encrypt xkey iv ad adlen plaintext len cipher tag =
  push_frame ();
  let open EverCrypt.Vale in
  let iv'        = B.alloca 0uy 16ul in
  let plaintext' = B.alloca 0uy U32.(((len +^ 15ul) /^ 16ul) *^ 16ul) in
  let cipher'    = B.alloca 0uy U32.(((len +^ 15ul) /^ 16ul) *^ 16ul) in
  let ad'        = B.alloca 0uy U32.(((adlen +^ 15ul) /^ 16ul) *^ 16ul) in
  blit iv 0ul iv' 0ul 12ul;
  blit plaintext 0ul plaintext' 0ul len;
  blit ad 0ul ad' 0ul adlen;
  let b = B.alloca ({
    plain = plaintext';
    plain_len = FStar.Int.Cast.Full.uint32_to_uint64 len;
    aad = ad';
    aad_len = FStar.Int.Cast.Full.uint32_to_uint64 adlen;
    iv = iv';
    expanded_key = xkey;
    cipher = cipher';
    tag = tag
  }) 1ul in
  Vale.gcm128_encrypt b;
  blit cipher' 0ul cipher 0ul len;
  pop_frame ()

private inline_for_extraction
let vale_aes128_gcm_decrypt xkey iv ad adlen plaintext len cipher tag =
  push_frame ();
  let open EverCrypt.Vale in
  let iv'        = B.alloca 0uy 16ul in
  let plaintext' = B.alloca 0uy U32.(((len +^ 15ul) /^ 16ul) *^ 16ul) in
  let cipher'    = B.alloca 0uy U32.(((len +^ 15ul) /^ 16ul) *^ 16ul) in
  let ad'        = B.alloca 0uy U32.(((adlen +^ 15ul) /^ 16ul) *^ 16ul) in
  blit iv 0ul iv' 0ul 12ul;
  blit cipher 0ul cipher' 0ul len;
  blit ad 0ul ad' 0ul adlen;
  let b = B.alloca ({
    plain = cipher';
    plain_len = FStar.Int.Cast.Full.uint32_to_uint64 len;
    aad = ad';
    aad_len = FStar.Int.Cast.Full.uint32_to_uint64 adlen;
    iv = iv';
    expanded_key = xkey;
    cipher = plaintext';
    tag = tag
  }) 1ul in
  let ret = Vale.gcm128_decrypt b in
  blit plaintext' 0ul plaintext 0ul len;
  pop_frame ();
  U32.(1ul -^ ret)

let aes128_gcm_encrypt key iv ad adlen plaintext len cipher tag =
  let i = AC.aes128_gcm_impl () in
  if SC.vale && i = AC.Vale then begin
    push_frame ();
    let expanded = B.alloca 0uy 176ul in
    Vale.aes128_key_expansion key expanded;
    vale_aes128_gcm_encrypt expanded iv ad adlen plaintext len cipher tag;
    pop_frame ()
  end
  else if SC.openssl && i = AC.OpenSSL then
    OpenSSL.aes128_gcm_encrypt key iv ad adlen plaintext len cipher tag
  else if SC.bcrypt && i = AC.BCrypt then
    BCrypt.aes128_gcm_encrypt key iv ad adlen plaintext len cipher tag
  else
    failwith !$"ERROR: inconsistent configuration"

let aes128_gcm_decrypt key iv ad adlen plaintext len cipher tag =
  let i = AC.aes128_gcm_impl () in
  if SC.vale && i = AC.Vale then
   begin
    push_frame ();
    let expanded = B.alloca 0uy 176ul in
    Vale.aes128_key_expansion key expanded;
    let r = vale_aes128_gcm_decrypt expanded iv ad adlen plaintext len cipher tag in
    pop_frame ();
    r
   end
  else if SC.openssl && i = AC.OpenSSL then
    OpenSSL.aes128_gcm_decrypt key iv ad adlen plaintext len cipher tag
  else if SC.bcrypt && i = AC.BCrypt then
    BCrypt.aes128_gcm_decrypt key iv ad adlen plaintext len cipher tag
  else
    failwith !$"ERROR: inconsistent configuration"

/// AES256-GCM

// TODO move to ValeGlue
private inline_for_extraction
let vale_aes256_gcm_encrypt xkey iv ad adlen plaintext len cipher tag =
  push_frame ();
  let open EverCrypt.Vale in
  let iv'        = B.alloca 0uy 16ul in
  let plaintext' = B.alloca 0uy U32.(((len +^ 15ul) /^ 16ul) *^ 16ul) in
  let cipher'    = B.alloca 0uy U32.(((len +^ 15ul) /^ 16ul) *^ 16ul) in
  let ad'        = B.alloca 0uy U32.(((adlen +^ 15ul) /^ 16ul) *^ 16ul) in
  blit iv 0ul iv' 0ul 12ul;
  blit plaintext 0ul plaintext' 0ul len;
  blit ad 0ul ad' 0ul adlen;
  let b = B.alloca ({
    plain = plaintext';
    plain_len = FStar.Int.Cast.Full.uint32_to_uint64 len;
    aad = ad';
    aad_len = FStar.Int.Cast.Full.uint32_to_uint64 adlen;
    iv = iv';
    expanded_key = xkey;
    cipher = cipher';
    tag = tag
  }) 1ul in
  Vale.gcm256_encrypt b;
  blit cipher' 0ul cipher 0ul len;
  pop_frame ()

private inline_for_extraction
let vale_aes256_gcm_decrypt xkey iv ad adlen plaintext len cipher tag =
  push_frame ();
  let open EverCrypt.Vale in
  let iv'        = B.alloca 0uy 16ul in
  let plaintext' = B.alloca 0uy U32.(((len +^ 15ul) /^ 16ul) *^ 16ul) in
  let cipher'    = B.alloca 0uy U32.(((len +^ 15ul) /^ 16ul) *^ 16ul) in
  let ad'        = B.alloca 0uy U32.(((adlen +^ 15ul) /^ 16ul) *^ 16ul) in
  blit iv 0ul iv' 0ul 12ul;
  blit cipher 0ul cipher' 0ul len;
  blit ad 0ul ad' 0ul adlen;
  let b = B.alloca ({
    plain = cipher';
    plain_len = FStar.Int.Cast.Full.uint32_to_uint64 len;
    aad = ad';
    aad_len = FStar.Int.Cast.Full.uint32_to_uint64 adlen;
    iv = iv';
    expanded_key = xkey;
    cipher = plaintext';
    tag = tag
  }) 1ul in
  let ret = Vale.gcm256_decrypt b in
  blit plaintext' 0ul plaintext 0ul len;
  pop_frame ();
  U32.(1ul -^ ret)

let aes256_gcm_encrypt key iv ad adlen plaintext len cipher tag =
  let i = AC.aes256_gcm_impl () in
  if SC.vale && i = AC.Vale then begin
    push_frame ();
    let expanded = B.alloca 0uy 240ul in
    Vale.aes256_key_expansion key expanded;
    vale_aes256_gcm_encrypt expanded iv ad adlen plaintext len cipher tag;
    pop_frame ()
  end
  else if SC.openssl && i = AC.OpenSSL then
    OpenSSL.aes256_gcm_encrypt key iv ad adlen plaintext len cipher tag
  else if SC.bcrypt && i = AC.BCrypt then
    BCrypt.aes256_gcm_encrypt key iv ad adlen plaintext len cipher tag
  else
    failwith !$"ERROR: inconsistent configuration"

let aes256_gcm_decrypt key iv ad adlen plaintext len cipher tag =
  let i = AC.aes256_gcm_impl () in
  if SC.vale && i = AC.Vale then begin
    push_frame ();
    let expanded = B.alloca 0uy 240ul in
    Vale.aes256_key_expansion key expanded;
    let r = vale_aes256_gcm_decrypt expanded iv ad adlen plaintext len cipher tag in
    pop_frame ();
    r
  end
  else if SC.openssl && i = AC.OpenSSL then
    OpenSSL.aes256_gcm_decrypt key iv ad adlen plaintext len cipher tag
  else if SC.bcrypt && i = AC.BCrypt then
    BCrypt.aes256_gcm_decrypt key iv ad adlen plaintext len cipher tag
  else
    failwith !$"ERROR: inconsistent configuration"

/// Chacha20-Poly1305

let chacha20_poly1305_encrypt key iv ad adlen plaintext len cipher tag =
  let i = AC.chacha20_poly1305_impl () in
  if SC.hacl && i = AC.Hacl then
    ignore (Hacl.chacha20_poly1305_encrypt cipher tag plaintext len ad adlen key iv)
  else if SC.openssl && i = AC.OpenSSL then
    OpenSSL.chacha20_poly1305_encrypt key iv ad adlen plaintext len cipher tag
  else
    failwith !$"ERROR: inconsistent configuration"

let chacha20_poly1305_decrypt key iv ad adlen plaintext len cipher tag =
  let i = AC.chacha20_poly1305_impl () in
  if SC.hacl && i = AC.Hacl then
    U32.(1ul -^ Hacl.chacha20_poly1305_decrypt plaintext cipher len tag ad adlen key iv)
  else if SC.openssl && i = AC.OpenSSL then
    OpenSSL.chacha20_poly1305_decrypt key iv ad adlen plaintext len cipher tag
  else
    failwith !$"ERROR: inconsistent configuration"

/// AEAD

[@CAbstractStruct]
private noeq type _aead_state =
  | AEAD_OPENSSL: st:Dyn.dyn -> _aead_state
  | AEAD_BCRYPT: st:Dyn.dyn -> _aead_state
  | AEAD_AES128_GCM_VALE: xkey:uint8_p -> _aead_state
  | AEAD_AES256_GCM_VALE: xkey:uint8_p -> _aead_state
  | AEAD_CHACHA20_POLY1305_HACL: k:uint8_p -> _aead_state

let aead_state_s = _aead_state

let aead_create alg k =
  let st: aead_state_s =
    match alg with
    | AES128_GCM ->
      let i = AC.aes128_gcm_impl () in
      if SC.vale && i = AC.Vale then
        let xk = B.malloc HS.root 0uy 176ul in
        Vale.aes128_key_expansion k xk;
        AEAD_AES128_GCM_VALE xk
      else if SC.bcrypt && i = AC.BCrypt then
        AEAD_BCRYPT (BCrypt.aead_create BCrypt.AES128_GCM k)
      else if SC.openssl && i = AC.OpenSSL then
        AEAD_OPENSSL (OpenSSL.aead_create OpenSSL.AES128_GCM k)
      else
        failwith !$"ERROR: inconsistent configuration"
    | AES256_GCM ->
      let i = AC.aes256_gcm_impl () in
      if SC.vale && i = AC.Vale then
        let xk = B.malloc HS.root 0uy 240ul in
        Vale.aes256_key_expansion k xk;
        AEAD_AES256_GCM_VALE xk
      else if SC.bcrypt && i = AC.BCrypt then
        AEAD_BCRYPT (BCrypt.aead_create BCrypt.AES256_GCM k)
      else if SC.openssl && i = AC.OpenSSL then
        AEAD_OPENSSL (OpenSSL.aead_create OpenSSL.AES256_GCM k)
      else
        failwith !$"ERROR: inconsistent configuration"
    | CHACHA20_POLY1305 ->
      let i = AC.chacha20_poly1305_impl () in
      if SC.hacl && i = AC.Hacl then
        let k0 = B.malloc HS.root 0uy 32ul in
        blit k 0ul k0 0ul 32ul;
        AEAD_CHACHA20_POLY1305_HACL k0
      else if SC.openssl && i = AC.OpenSSL then
        AEAD_OPENSSL (OpenSSL.aead_create OpenSSL.CHACHA20_POLY1305 k)
      else
        failwith !$"ERROR: inconsistent configuration"
  in
  B.malloc HS.root st 1ul

let aead_encrypt pkey iv ad adlen plaintext len cipher tag =
  let k = !*pkey in
  if SC.vale && AEAD_AES128_GCM_VALE? k then
    let xk = AEAD_AES128_GCM_VALE?.xkey k in
    vale_aes128_gcm_encrypt xk iv ad adlen plaintext len cipher tag
  else if SC.vale && AEAD_AES256_GCM_VALE? k then
    let xk = AEAD_AES256_GCM_VALE?.xkey k in
    vale_aes256_gcm_encrypt xk iv ad adlen plaintext len cipher tag
  else if SC.hacl && AEAD_CHACHA20_POLY1305_HACL? k then
    let key = AEAD_CHACHA20_POLY1305_HACL?.k k in
    ignore (Hacl.chacha20_poly1305_encrypt cipher tag plaintext len ad adlen key iv)
  else if SC.openssl && AEAD_OPENSSL? k then
    let key = AEAD_OPENSSL?.st k in
    OpenSSL.aead_encrypt key iv ad adlen plaintext len cipher tag
  else if SC.bcrypt && AEAD_BCRYPT? k then
    let key = AEAD_BCRYPT?.st k in
    BCrypt.aead_encrypt key iv ad adlen plaintext len cipher tag
  else
    failwith !$"ERROR: inconsistent configuration"

let aead_decrypt pkey iv ad adlen plaintext len cipher tag =
  let k = !*pkey in
  if SC.vale && AEAD_AES128_GCM_VALE? k then
    let xk = AEAD_AES128_GCM_VALE?.xkey k in
    vale_aes128_gcm_decrypt xk iv ad adlen plaintext len cipher tag
  else if SC.vale && AEAD_AES256_GCM_VALE? k then
    let xk = AEAD_AES256_GCM_VALE?.xkey k in
    vale_aes256_gcm_decrypt xk iv ad adlen plaintext len cipher tag
  else if SC.hacl && AEAD_CHACHA20_POLY1305_HACL? k then
    let key = AEAD_CHACHA20_POLY1305_HACL?.k k in
    let r = Hacl.chacha20_poly1305_decrypt plaintext cipher len tag ad adlen key iv in
    U32.(1ul -^ r)
  else if SC.openssl && AEAD_OPENSSL? k then
    let key = AEAD_OPENSSL?.st k in
    OpenSSL.aead_decrypt key iv ad adlen plaintext len cipher tag
  else if SC.bcrypt && AEAD_BCRYPT? k then
    let key = AEAD_BCRYPT?.st k in
    BCrypt.aead_decrypt key iv ad adlen plaintext len cipher tag
  else
    failwith !$"ERROR: inconsistent configuration"

let aead_free pk =
  let k = !*pk in
  if SC.vale && AEAD_AES128_GCM_VALE? k then
    let AEAD_AES128_GCM_VALE xk = k in
    B.free xk
  else if SC.vale && AEAD_AES256_GCM_VALE? k then
    let AEAD_AES256_GCM_VALE xk = k in
    B.free xk
  else if SC.hacl && AEAD_CHACHA20_POLY1305_HACL? k then
    let AEAD_CHACHA20_POLY1305_HACL key = k in
    B.free key
  else if SC.openssl && AEAD_OPENSSL? k then
    OpenSSL.aead_free (AEAD_OPENSSL?.st k)
  else if SC.bcrypt && AEAD_BCRYPT? k then
    BCrypt.aead_free (AEAD_BCRYPT?.st k)
  else
    failwith !$"ERROR: inconsistent configuration";
  B.free pk
