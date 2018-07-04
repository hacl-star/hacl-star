module EverCrypt

module B = FStar.Buffer
module LB = LowStar.Buffer

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

/// X25519

let x25519 dst secret base =
  let i = AC.x25519_impl () in
  if SC.hacl && i = AC.Hacl then
    Hacl.x25519 dst secret base
  else
    failwith !$"ERROR: inconsistent configuration"

/// AES128-ECB

private noeq type _aes128_key =
  | AES128_OPENSSL: st:Dyn.dyn -> _aes128_key
  | AES128_BCRYPT: st:Dyn.dyn -> _aes128_key
  | AES128_VALE: w:uint8_p -> sbox:uint8_p -> _aes128_key
  | AES128_HACL: w:uint8_p -> sbox:uint8_p -> _aes128_key

[@(CEpilogue "#define __EverCrypt_aes128_key_s")]
let aes128_key_s = _aes128_key

let aes128_create k =
  let i = AC.aes128_impl () in
  let st =
    if SC.vale && i = AC.Vale then
    begin
      push_frame ();
      let w    = B.rcreate_mm HS.root 0uy 176ul in
      let sbox = B.rcreate_mm HS.root 0uy 256ul in
      Vale.aes128_key_expansion k w sbox;
      pop_frame ();
      AES128_VALE w sbox
    end
    else if SC.hacl && i = AC.Hacl then
    begin
      push_frame ();
      let w    = B.rcreate_mm HS.root 0uy 176ul in
      let sbox = B.rcreate_mm HS.root 0uy 256ul in
      Hacl.aes128_keyExpansion k w sbox;
      pop_frame ();
      AES128_HACL w sbox
    end
  //  else if SC.openssl && i = AC.OpenSSL then
  //    EverCrypt.OpenSSL.aes128_gcm_encrypt key iv ad adlen plaintext len cipher tag
  //  else if SC.bcrypt && i = AC.BCrypt then
  //    EverCrypt.BCrypt.aes128_gcm_encrypt key iv ad adlen plaintext len cipher tag
    else
      failwith !$"ERROR: inconsistent configuration"
  in
  LB.malloc HS.root st 1ul

let aes128_compute k plain cipher =
  let k = LB.index k 0ul in
  if SC.vale && AES128_VALE? k then
   begin
    push_frame ();
    let AES128_VALE w sbox = k in
    Vale.aes128_encrypt_one_block cipher plain w sbox;
    pop_frame ()
   end
  else if SC.hacl && AES128_HACL? k then
   begin
    push_frame ();
    let AES128_HACL w sbox = k in
    Hacl.aes128_cipher cipher plain w sbox;
    pop_frame ()
   end
//  else if SC.openssl && i = AC.OpenSSL then
//    EverCrypt.OpenSSL.aes128_gcm_encrypt key iv ad adlen plaintext len cipher tag
//  else if SC.bcrypt && i = AC.BCrypt then
//    EverCrypt.BCrypt.aes128_gcm_encrypt key iv ad adlen plaintext len cipher tag
  else
    failwith !$"ERROR: inconsistent configuration"

let aes128_free pk =
  let k = LB.index pk 0ul in
  if SC.vale && AES128_VALE? k then
   begin
    push_frame ();
    let AES128_VALE w sbox = k in
    Buffer.rfree w;
    Buffer.rfree sbox;
    pop_frame ()
   end
  else if SC.hacl && AES128_HACL? k then
   begin
    push_frame ();
    let AES128_HACL w sbox = k in
    Buffer.rfree w;
    Buffer.rfree sbox;
    pop_frame ()
   end
//  else if SC.openssl && i = AC.OpenSSL then
//    EverCrypt.OpenSSL.aes128_gcm_encrypt key iv ad adlen plaintext len cipher tag
//  else if SC.bcrypt && i = AC.BCrypt then
//    EverCrypt.BCrypt.aes128_gcm_encrypt key iv ad adlen plaintext len cipher tag
  else
    failwith !$"ERROR: inconsistent configuration";
  LB.free pk

private noeq type _aes256_key =
  | AES256_OPENSSL: st:Dyn.dyn -> _aes256_key
  | AES256_BCRYPT: st:Dyn.dyn -> _aes256_key
  | AES256_HACL: w:uint8_p -> sbox:uint8_p -> _aes256_key

[@(CEpilogue "#define __EverCrypt_aes256_key_s")]
let aes256_key_s = _aes256_key

let aes256_create k =
  let i = AC.aes256_impl () in
  let st =
    if SC.hacl && i = AC.Hacl then
    begin
      push_frame ();
      let w    = B.rcreate_mm HS.root 0uy 240ul in
      let sbox = B.rcreate_mm HS.root 0uy 256ul in
      Hacl.aes256_keyExpansion k w sbox;
      pop_frame ();
      AES256_HACL w sbox
    end
  //  else if SC.openssl && i = AC.OpenSSL then
  //    EverCrypt.OpenSSL.aes128_gcm_encrypt key iv ad adlen plaintext len cipher tag
  //  else if SC.bcrypt && i = AC.BCrypt then
  //    EverCrypt.BCrypt.aes128_gcm_encrypt key iv ad adlen plaintext len cipher tag
    else
      failwith !$"ERROR: inconsistent configuration"
  in
  LB.malloc HS.root st 1ul

let aes256_compute k plain cipher =
  let k = LB.index k 0ul in
  if SC.hacl && AES256_HACL? k then
   begin
    push_frame ();
    let AES256_HACL w sbox = k in
    Hacl.aes256_cipher cipher plain w sbox;
    pop_frame ()
   end
//  else if SC.openssl && i = AC.OpenSSL then
//    EverCrypt.OpenSSL.aes128_gcm_encrypt key iv ad adlen plaintext len cipher tag
//  else if SC.bcrypt && i = AC.BCrypt then
//    EverCrypt.BCrypt.aes128_gcm_encrypt key iv ad adlen plaintext len cipher tag
  else
    failwith !$"ERROR: inconsistent configuration"

let aes256_free pk =
  let k = LB.index pk 0ul in
  if SC.hacl && AES256_HACL? k then
   begin
    push_frame ();
    let AES256_HACL w sbox = k in
    Buffer.rfree w;
    Buffer.rfree sbox;
    pop_frame ()
   end
//  else if SC.openssl && i = AC.OpenSSL then
//    EverCrypt.OpenSSL.aes128_gcm_encrypt key iv ad adlen plaintext len cipher tag
//  else if SC.bcrypt && i = AC.BCrypt then
//    EverCrypt.BCrypt.aes128_gcm_encrypt key iv ad adlen plaintext len cipher tag
  else
    failwith !$"ERROR: inconsistent configuration";
  LB.free pk

/// ChaCha20

let chacha20 key iv ctr plain len cipher =
  let i = AC.chacha20_impl () in
  if SC.hacl && i = AC.Hacl then
   begin
    push_frame ();
    EverCrypt.Hacl.chacha20 key iv ctr plain len cipher;
    pop_frame ()
   end
  else 
    failwith !$"ERROR: inconsistent configuration"

/// AES128-GCM

// TODO move to ValeGlue
private inline_for_extraction
let vale_aes128_gcm_encrypt xkey iv ad adlen plaintext len cipher tag =
  push_frame ();
  let open EverCrypt.Vale in
  let iv'        = B.create 0uy 16ul in
  let plaintext' = B.create 0uy U32.(((len +^ 15ul) /^ 16ul) *^ 16ul) in
  let cipher'    = B.create 0uy U32.(((len +^ 15ul) /^ 16ul) *^ 16ul) in
  let ad'        = B.create 0uy U32.(((adlen +^ 15ul) /^ 16ul) *^ 16ul) in
  B.blit iv 0ul iv' 0ul 12ul;
  B.blit plaintext 0ul plaintext' 0ul len;
  B.blit ad 0ul ad' 0ul adlen;
  let b = B.create ({
    plain = plaintext';
    plain_len = FStar.Int.Cast.Full.uint32_to_uint64 len;
    aad = ad';
    aad_len = FStar.Int.Cast.Full.uint32_to_uint64 adlen;
    iv = iv';
    expanded_key = xkey;
    cipher = cipher';
    tag = tag
  }) 1ul in
  Vale.gcm_encrypt b;
  B.blit cipher' 0ul cipher 0ul len;
  pop_frame ()

private inline_for_extraction
let vale_aes128_gcm_decrypt xkey iv ad adlen plaintext len cipher tag =
  push_frame ();
  let open EverCrypt.Vale in
  let iv'        = B.create 0uy 16ul in
  let plaintext' = B.create 0uy U32.(((len +^ 15ul) /^ 16ul) *^ 16ul) in
  let cipher'    = B.create 0uy U32.(((len +^ 15ul) /^ 16ul) *^ 16ul) in
  let ad'        = B.create 0uy U32.(((adlen +^ 15ul) /^ 16ul) *^ 16ul) in
  B.blit iv 0ul iv' 0ul 12ul;
  B.blit cipher 0ul cipher' 0ul len;
  B.blit ad 0ul ad' 0ul adlen;
  let b = B.create ({
    plain = cipher';
    plain_len = FStar.Int.Cast.Full.uint32_to_uint64 len;
    aad = ad';
    aad_len = FStar.Int.Cast.Full.uint32_to_uint64 adlen;
    iv = iv';
    expanded_key = xkey;
    cipher = plaintext';
    tag = tag
  }) 1ul in
  let ret = Vale.gcm_decrypt b in
  B.blit plaintext' 0ul plaintext 0ul len;
  pop_frame ();
  // FIXME: restore tag verification once Vale is fixed
  //U32.(1ul -^ ret)
  1ul

let aes128_gcm_encrypt key iv ad adlen plaintext len cipher tag =
  let i = AC.aes128_gcm_impl () in
  if SC.vale && i = AC.Vale then begin
    push_frame ();
    let expanded   = B.create 0uy 176ul in
    Vale.aes_key_expansion key expanded;
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
    let expanded   = B.create 0uy 176ul in
    Vale.aes_key_expansion key expanded;
    let r = vale_aes128_gcm_decrypt expanded iv ad adlen plaintext len cipher tag in
    pop_frame (); r
   end
  else if SC.openssl && i = AC.OpenSSL then
    OpenSSL.aes128_gcm_decrypt key iv ad adlen plaintext len cipher tag
  else if SC.bcrypt && i = AC.BCrypt then
    BCrypt.aes128_gcm_decrypt key iv ad adlen plaintext len cipher tag
  else
    failwith !$"ERROR: inconsistent configuration"

/// AES256-GCM

let aes256_gcm_encrypt key iv ad adlen plaintext len cipher tag =
  let i = AC.aes256_gcm_impl () in
  if SC.openssl && i = AC.OpenSSL then
    OpenSSL.aes256_gcm_encrypt key iv ad adlen plaintext len cipher tag
  else if SC.bcrypt && i = AC.BCrypt then
    BCrypt.aes256_gcm_encrypt key iv ad adlen plaintext len cipher tag
  else
    failwith !$"ERROR: inconsistent configuration"

let aes256_gcm_decrypt key iv ad adlen plaintext len cipher tag =
  let i = AC.aes256_gcm_impl () in
  if SC.openssl && i = AC.OpenSSL then
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

private noeq type _aead_state =
  | AEAD_OPENSSL: st:Dyn.dyn -> _aead_state
  | AEAD_BCRYPT: st:Dyn.dyn -> _aead_state
  | AEAD_AES128_GCM_VALE: xkey:uint8_p -> _aead_state
  | AEAD_CHACHA20_POLY1305_HACL: k:uint8_p -> _aead_state

[@(CEpilogue "#define __EverCrypt_aead_state_s")]
let aead_state_s = _aead_state

let aead_create alg k =
  let st: aead_state_s =
    match alg with
    | AES128_GCM ->
      let i = AC.aes128_gcm_impl () in
      if SC.vale && i = AC.Vale then
      begin
	push_frame ();
	let xk = B.rcreate_mm HS.root 0uy 176ul in
	Vale.aes_key_expansion k xk;
	pop_frame ();
	AEAD_AES128_GCM_VALE xk
      end
      else if SC.bcrypt && i = AC.BCrypt then
	AEAD_BCRYPT (BCrypt.aead_create BCrypt.AES128_GCM k)
      else if SC.openssl && i = AC.OpenSSL then
	AEAD_OPENSSL (OpenSSL.aead_create OpenSSL.AES128_GCM k)
      else
	failwith !$"ERROR: inconsistent configuration"
    | AES256_GCM ->
      let i = AC.aes256_gcm_impl () in
      if SC.bcrypt && i = AC.BCrypt then
	AEAD_BCRYPT (BCrypt.aead_create BCrypt.AES256_GCM k)
      else if SC.openssl && i = AC.OpenSSL then
	AEAD_OPENSSL (OpenSSL.aead_create OpenSSL.AES256_GCM k)
      else
	failwith !$"ERROR: inconsistent configuration"  
    | CHACHA20_POLY1305 ->
      let i = AC.chacha20_poly1305_impl () in
      if SC.hacl && i = AC.Hacl then
      begin
	let k0 = B.rcreate_mm HS.root 0uy 32ul in
	B.blit k 0ul k0 0ul 32ul;
	AEAD_CHACHA20_POLY1305_HACL k0
      end
      else if SC.openssl && i = AC.OpenSSL then
	AEAD_OPENSSL (OpenSSL.aead_create OpenSSL.CHACHA20_POLY1305 k)
      else
	failwith !$"ERROR: inconsistent configuration"
  in
  LB.malloc HS.root st 1ul

let aead_encrypt pkey iv ad adlen plaintext len cipher tag =
  let k = LB.index pkey 0ul in
  if SC.vale && AEAD_AES128_GCM_VALE? k then
    let xk = AEAD_AES128_GCM_VALE?.xkey k in
    vale_aes128_gcm_encrypt xk iv ad adlen plaintext len cipher tag
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
  let k = LB.index pkey 0ul in
  if SC.vale && AEAD_AES128_GCM_VALE? k then
    let xk = AEAD_AES128_GCM_VALE?.xkey k in
    vale_aes128_gcm_decrypt xk iv ad adlen plaintext len cipher tag
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
  let k = LB.index pk 0ul in
  if SC.vale && AEAD_AES128_GCM_VALE? k then
    let AEAD_AES128_GCM_VALE xk = k in
    B.rfree xk
  else if SC.hacl && AEAD_CHACHA20_POLY1305_HACL? k then
    let AEAD_CHACHA20_POLY1305_HACL key = k in
    B.rfree key
  else if SC.openssl && AEAD_OPENSSL? k then
    OpenSSL.aead_free (AEAD_OPENSSL?.st k)
  else if SC.bcrypt && AEAD_BCRYPT? k then
    BCrypt.aead_free (AEAD_BCRYPT?.st k)
  else
    failwith !$"ERROR: inconsistent configuration";
  LB.free pk

    
