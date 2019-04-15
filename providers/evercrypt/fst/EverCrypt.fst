module EverCrypt

module B = LowStar.Buffer

module BCrypt = EverCrypt.BCrypt
module Hacl = EverCrypt.Hacl
module OpenSSL = EverCrypt.OpenSSL
module Vale = EverCrypt.Vale

module SC = EverCrypt.StaticConfig
module AC = EverCrypt.AutoConfig2
module U32 = FStar.UInt32
module HS = FStar.HyperStack

open EverCrypt.Helpers
open C.Failure
open LowStar.BufferOps

inline_for_extraction
let vale (): Stack bool (fun _ -> True) (fun h0 _ h1 -> B.modifies B.loc_none h0 h1) =
  if SC.vale then
    AC.wants_vale ()
  else
    false

inline_for_extraction
let vale_and_aesni (): Stack bool (fun _ -> True) (fun h0 _ h1 -> B.modifies B.loc_none h0 h1) =
  if vale () then
    AC.has_aesni ()
  else
    false

inline_for_extraction
let hacl (): Stack bool (fun _ -> True) (fun h0 _ h1 -> B.modifies B.loc_none h0 h1) =
  if SC.hacl then
    AC.wants_hacl ()
  else
    false

inline_for_extraction
let openssl (): Stack bool (fun _ -> True) (fun h0 _ h1 -> B.modifies B.loc_none h0 h1) =
  if SC.openssl then
    AC.wants_openssl ()
  else
    false

inline_for_extraction
let bcrypt (): Stack bool (fun _ -> True) (fun h0 _ h1 -> B.modifies B.loc_none h0 h1) =
  if SC.bcrypt then
    AC.wants_bcrypt ()
  else
    false

/// Random sampling

let random_init () =
  if openssl () then
    OpenSSL.random_init ()
  else if bcrypt () then
    BCrypt.random_init ()
  else
    failwith !$"ERROR: inconsistent configuration (random_init)"

let random_sample len out =
  if openssl () then
    OpenSSL.random_sample len out
  else if bcrypt () then
    BCrypt.random_sample len out
  else
    failwith !$"ERROR: inconsistent configuration (random_sample)"

let random_cleanup () =
  if openssl () then
    ()
  else if bcrypt () then
    BCrypt.random_cleanup ()
  else
    failwith !$"ERROR: inconsistent configuration (random_cleanup)"

/// AES128-ECB

[@CAbstractStruct]
noeq type aes128_key_s =
  | AES128_OPENSSL: st:Dyn.dyn -> aes128_key_s
  | AES128_BCRYPT: st:Dyn.dyn -> aes128_key_s
  | AES128_VALE: w:uint8_p -> sbox:uint8_p -> aes128_key_s
  | AES128_HACL: w:uint8_p -> sbox:uint8_p -> aes128_key_s

let aes128_create k =
  let st =
    if vale_and_aesni () then
      let w    = B.malloc HS.root 0uy 176ul in
      let sbox = B.malloc HS.root 0uy 256ul in
      Vale.aes128_key_expansion_sbox k w sbox;
      AES128_VALE w sbox
    else if hacl () then
      let w    = B.malloc HS.root 0uy 176ul in
      let sbox = B.malloc HS.root 0uy 256ul in
      Hacl.aes128_mk_sbox sbox;
      Hacl.aes128_keyExpansion k w sbox;
      AES128_HACL w sbox
  //  else if openssl () then
  //    EverCrypt.OpenSSL.aes128_gcm_encrypt key iv ad adlen plaintext len cipher tag
  //  else if bcrypt () then
  //    EverCrypt.BCrypt.aes128_gcm_encrypt key iv ad adlen plaintext len cipher tag
    else
      failwith !$"ERROR: inconsistent configuration (aes128_create)"
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
//  else if openssl () then
//    EverCrypt.OpenSSL.aes128_gcm_encrypt key iv ad adlen plaintext len cipher tag
//  else if bcrypt () then
//    EverCrypt.BCrypt.aes128_gcm_encrypt key iv ad adlen plaintext len cipher tag
  else
    failwith !$"ERROR: inconsistent configuration (aes128_compute)"

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
//  else if openssl () then
//    EverCrypt.OpenSSL.aes128_gcm_encrypt key iv ad adlen plaintext len cipher tag
//  else if bcrypt () then
//    EverCrypt.BCrypt.aes128_gcm_encrypt key iv ad adlen plaintext len cipher tag
  else
    failwith !$"ERROR: inconsistent configuration (aes128_free)";
  B.free pk

[@CAbstractStruct]
noeq type aes256_key_s =
  | AES256_OPENSSL: st:Dyn.dyn -> aes256_key_s
  | AES256_BCRYPT: st:Dyn.dyn -> aes256_key_s
  | AES256_HACL: w:uint8_p -> sbox:uint8_p -> aes256_key_s

let aes256_create k =
  let st =
    if hacl () then
      let w    = B.malloc HS.root 0uy 240ul in
      let sbox = B.malloc HS.root 0uy 256ul in
      Hacl.aes256_mk_sbox sbox;
      Hacl.aes256_keyExpansion k w sbox;
      AES256_HACL w sbox
  //  else if openssl () then
  //    EverCrypt.OpenSSL.aes128_gcm_encrypt key iv ad adlen plaintext len cipher tag
  //  else if bcrypt () then
  //    EverCrypt.BCrypt.aes128_gcm_encrypt key iv ad adlen plaintext len cipher tag
    else
      failwith !$"ERROR: inconsistent configuration (aes256_create)"
  in
  B.malloc HS.root st 1ul

let aes256_compute k plain cipher =
  let k = !*k in
  if SC.hacl && AES256_HACL? k then
    let AES256_HACL w sbox = k in
    Hacl.aes256_cipher cipher plain w sbox
//  else if openssl () then
//    EverCrypt.OpenSSL.aes128_gcm_encrypt key iv ad adlen plaintext len cipher tag
//  else if bcrypt () then
//    EverCrypt.BCrypt.aes128_gcm_encrypt key iv ad adlen plaintext len cipher tag
  else
    failwith !$"ERROR: inconsistent configuration (aes256_compute)"

let aes256_free pk =
  let k = !*pk in
  if SC.hacl && AES256_HACL? k then
    let AES256_HACL w sbox = k in
    B.free w;
    B.free sbox
//  else if openssl () then
//    EverCrypt.OpenSSL.aes128_gcm_encrypt key iv ad adlen plaintext len cipher tag
//  else if bcrypt () then
//    EverCrypt.BCrypt.aes128_gcm_encrypt key iv ad adlen plaintext len cipher tag
  else
    failwith !$"ERROR: inconsistent configuration (aes256_free)";
  B.free pk

/// AES128-GCM

// TODO move to ValeGlue
private inline_for_extraction
let vale_aes128_gcm_encrypt xkey (iv:uint8_p) (ad:uint8_p) (adlen:uint32_t)
                            (plaintext:uint8_p) (len:uint32_t) (cipher:uint8_p) (tag:uint8_p) =
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
  Vale.old_gcm128_encrypt b;
  blit cipher' 0ul cipher 0ul len;
  pop_frame ()

private inline_for_extraction
let vale_aes128_gcm_decrypt xkey (iv:uint8_p) (ad:uint8_p) (adlen:uint32_t)
                            (plaintext:uint8_p) (len:uint32_t) (cipher:uint8_p) (tag:uint8_p) =
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
  let ret = Vale.old_gcm128_decrypt b in
  blit plaintext' 0ul plaintext 0ul len;
  pop_frame ();
  if ret = 0ul then 1ul else 0ul

let aes128_gcm_encrypt key iv ad adlen plaintext len cipher tag =
  if vale_and_aesni () then begin
    push_frame ();
    let expanded = B.alloca 0uy 176ul in
    Vale.old_aes128_key_expansion key expanded;
    vale_aes128_gcm_encrypt expanded iv ad adlen plaintext len cipher tag;
    pop_frame ()
  end
  else if openssl () then
    OpenSSL.aes128_gcm_encrypt key iv ad adlen plaintext len cipher tag
  else if bcrypt () then
    BCrypt.aes128_gcm_encrypt key iv ad adlen plaintext len cipher tag
  else
    failwith !$"ERROR: inconsistent configuration (aes128_gcm_encrypt)"

let aes128_gcm_decrypt key iv ad adlen plaintext len cipher tag =
  if vale_and_aesni () then
   begin
    push_frame ();
    let expanded = B.alloca 0uy 176ul in
    Vale.old_aes128_key_expansion key expanded;
    let r = vale_aes128_gcm_decrypt expanded iv ad adlen plaintext len cipher tag in
    pop_frame ();
    r
   end
  else if openssl () then
    OpenSSL.aes128_gcm_decrypt key iv ad adlen plaintext len cipher tag
  else if bcrypt () then
    BCrypt.aes128_gcm_decrypt key iv ad adlen plaintext len cipher tag
  else
    failwith !$"ERROR: inconsistent configuration (aes128_gcm_decrypt)"

/// AES256-GCM

// TODO move to ValeGlue
private inline_for_extraction
let vale_aes256_gcm_encrypt xkey (iv:uint8_p) (ad:uint8_p) (adlen:uint32_t)
                            (plaintext:uint8_p) (len:uint32_t) (cipher:uint8_p) (tag:uint8_p) =
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
  Vale.old_gcm256_encrypt b;
  blit cipher' 0ul cipher 0ul len;
  pop_frame ()

private inline_for_extraction
let vale_aes256_gcm_decrypt xkey (iv:uint8_p) (ad:uint8_p) (adlen:uint32_t)
                            (plaintext:uint8_p) (len:uint32_t) (cipher:uint8_p) (tag:uint8_p) =
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
  let ret = Vale.old_gcm256_decrypt b in
  blit plaintext' 0ul plaintext 0ul len;
  pop_frame ();
  if ret = 0ul then 1ul else 0ul

let aes256_gcm_encrypt key iv ad adlen plaintext len cipher tag =
  if vale_and_aesni () then begin
    push_frame ();
    let expanded = B.alloca 0uy 240ul in
    Vale.old_aes256_key_expansion key expanded;
    vale_aes256_gcm_encrypt expanded iv ad adlen plaintext len cipher tag;
    pop_frame ()
  end
  else if openssl () then
    OpenSSL.aes256_gcm_encrypt key iv ad adlen plaintext len cipher tag
  else if bcrypt () then
    BCrypt.aes256_gcm_encrypt key iv ad adlen plaintext len cipher tag
  else
    failwith !$"ERROR: inconsistent configuration (aes256_gcm_encrypt)"

let aes256_gcm_decrypt key iv ad adlen plaintext len cipher tag =
  if vale_and_aesni () then begin
    push_frame ();
    let expanded = B.alloca 0uy 240ul in
    Vale.old_aes256_key_expansion key expanded;
    let r = vale_aes256_gcm_decrypt expanded iv ad adlen plaintext len cipher tag in
    pop_frame ();
    r
  end
  else if openssl () then
    OpenSSL.aes256_gcm_decrypt key iv ad adlen plaintext len cipher tag
  else if bcrypt () then
    BCrypt.aes256_gcm_decrypt key iv ad adlen plaintext len cipher tag
  else
    failwith !$"ERROR: inconsistent configuration (aes256_gcm_decrypt)"


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
      if vale_and_aesni () then
        let xk = B.malloc HS.root 0uy 176ul in
        Vale.old_aes128_key_expansion k xk;
        AEAD_AES128_GCM_VALE xk
      else if bcrypt () then
        AEAD_BCRYPT (BCrypt.aead_create BCrypt.AES128_GCM k)
      else if openssl () then
        AEAD_OPENSSL (OpenSSL.aead_create OpenSSL.AES128_GCM k)
      else
        failwith !$"ERROR: inconsistent configuration (aead_create/AES128_GCM)"
    | AES256_GCM ->
      if vale_and_aesni () then
        let xk = B.malloc HS.root 0uy 240ul in
        Vale.old_aes256_key_expansion k xk;
        AEAD_AES256_GCM_VALE xk
      else if bcrypt () then
        AEAD_BCRYPT (BCrypt.aead_create BCrypt.AES256_GCM k)
      else if openssl () then
        AEAD_OPENSSL (OpenSSL.aead_create OpenSSL.AES256_GCM k)
      else
        failwith !$"ERROR: inconsistent configuration (aead_create/AES256_GCM)"
    | CHACHA20_POLY1305 ->
      if hacl () then
        let k0 = B.malloc HS.root 0uy 32ul in
        blit k 0ul k0 0ul 32ul;
        AEAD_CHACHA20_POLY1305_HACL k0
      else if openssl () then
        AEAD_OPENSSL (OpenSSL.aead_create OpenSSL.CHACHA20_POLY1305 k)
      else
        failwith !$"ERROR: inconsistent configuration (aead_create/CHACHA20_POLY1305)"
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
    Hacl.Impl.Chacha20Poly1305.aead_encrypt_chacha_poly key iv adlen ad len plaintext cipher tag
  else if SC.openssl && AEAD_OPENSSL? k then
    let key = AEAD_OPENSSL?.st k in
    OpenSSL.aead_encrypt key iv ad adlen plaintext len cipher tag
  else if SC.bcrypt && AEAD_BCRYPT? k then
    let key = AEAD_BCRYPT?.st k in
    BCrypt.aead_encrypt key iv ad adlen plaintext len cipher tag
  else
    failwith !$"ERROR: inconsistent configuration (aead_encrypt)"

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
    let r = Hacl.Impl.Chacha20Poly1305.aead_decrypt_chacha_poly key iv adlen ad len plaintext cipher tag in
    U32.(1ul -^ r)
  else if SC.openssl && AEAD_OPENSSL? k then
    let key = AEAD_OPENSSL?.st k in
    OpenSSL.aead_decrypt key iv ad adlen plaintext len cipher tag
  else if SC.bcrypt && AEAD_BCRYPT? k then
    let key = AEAD_BCRYPT?.st k in
    BCrypt.aead_decrypt key iv ad adlen plaintext len cipher tag
  else
    failwith !$"ERROR: inconsistent configuration (aead_decrypt)"

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
    failwith !$"ERROR: inconsistent configuration (aead_free)";
  B.free pk

/// DH

[@CAbstractStruct]
private noeq type _dh_state =
  | DH_OPENSSL: st:Dyn.dyn -> _dh_state
  | DH_DUMMY // Necessary placeholder or discriminators are not defined

let dh_state_s = _dh_state

let dh_load_group dh_p dh_p_len dh_g dh_g_len dh_q dh_q_len =
  let st: dh_state_s =
    if openssl () then
      DH_OPENSSL (OpenSSL.dh_load_group dh_p dh_p_len dh_g dh_g_len dh_q dh_q_len)
    else
      failwith !$"ERROR: inconsistent configuration (dh_load_group)"
  in
  B.malloc HS.root st 1ul

let dh_free_group st =
  let s : _dh_state = !*st in
  if SC.openssl && DH_OPENSSL? s then
    OpenSSL.dh_free_group (DH_OPENSSL?.st s)
  else
    failwith !$"ERROR: inconsistent configuration (dh_free_group)";
  B.free st

let dh_keygen st public =
  let s = !*st in
  if SC.openssl && DH_OPENSSL? s then
    OpenSSL.dh_keygen (DH_OPENSSL?.st s) public
  else
    failwith !$"ERROR: inconsistent configuration (dh_keygen)"

let dh_compute st public public_len out =
  let s = !*st in
  if SC.openssl && DH_OPENSSL? s then
    OpenSSL.dh_compute (DH_OPENSSL?.st s) public public_len out
  else
    failwith !$"ERROR: inconsistent configuration (dh_compute)"

/// DH

[@CAbstractStruct]
private noeq type _ecdh_state =
  | ECDH_OPENSSL: st:Dyn.dyn -> _ecdh_state
  | ECDH_DUMMY // Necessary placeholder or discriminators are not defined

let ecdh_state_s = _ecdh_state

let ecdh_load_curve g =
  let st: ecdh_state_s =
    if openssl () then
      let g' = match g with
        | ECC_P256 -> OpenSSL.ECC_P256
        | ECC_P384 -> OpenSSL.ECC_P384
        | ECC_P521 -> OpenSSL.ECC_P521
        | ECC_X25519 -> OpenSSL.ECC_X25519
        | ECC_X448 -> OpenSSL.ECC_X448 in
      ECDH_OPENSSL (OpenSSL.ecdh_load_curve g')
    else
      failwith !$"ERROR: inconsistent configuration (ecdh_load_curve)"
  in
  B.malloc HS.root st 1ul

let ecdh_free_curve st =
  let s : _ecdh_state = !*st in
  if SC.openssl && ECDH_OPENSSL? s then
    OpenSSL.ecdh_free_curve (ECDH_OPENSSL?.st s)
  else
    failwith !$"ERROR: inconsistent configuration (ecdh_free_curve)";
  B.free st

let ecdh_keygen st outx outy =
  let s = !*st in
  if SC.openssl && ECDH_OPENSSL? s then
    OpenSSL.ecdh_keygen (ECDH_OPENSSL?.st s) outx outy
  else
    failwith !$"ERROR: inconsistent configuration (ecdh_keygen)"

let ecdh_compute st inx iny out =
  let s = !*st in
  if SC.openssl && ECDH_OPENSSL? s then
    OpenSSL.ecdh_compute (ECDH_OPENSSL?.st s) inx iny out
  else
    failwith !$"ERROR: inconsistent configuration (ecdh_compute)"

