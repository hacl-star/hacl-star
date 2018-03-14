module CSpec.AE

open FStar.Map
open FStar.Seq

open Crypto.Symmetric.Bytes

abstract noeq type encryption_scheme (key_length:nat) (nonce_length:nat) =
  | ES:
    gen: (unit -> lbytes key_length) ->
    enc: (n:lbytes nonce_length -> k:lbytes key_length -> p:bytes -> c:bytes) ->
    dec: (n:lbytes nonce_length -> k:lbytes key_length -> c:bytes -> option (p:bytes)) ->
    correctness: (n:lbytes nonce_length -> k:lbytes key_length -> p:bytes -> Lemma
    (requires True)
    (ensures (
      let dec_result = dec n k (enc n k p) in
      Some? dec_result
      /\ Some?.v dec_result == p
    ))
    ) ->
    encryption_scheme key_length nonce_length

abstract noeq type game_parameters =
  | GP:
    nonce_length:nat ->
    key_length:nat ->
    scheme: (encryption_scheme key_length nonce_length) ->
    b:bool ->
    game_parameters

// Here, we define some types for keys, nonces, plain- and ciphertext depending on a specific set of game parameters.
let key (gp:game_parameters) = lbytes gp.key_length
let nonce (gp:game_parameters) = lbytes gp.nonce_length
let plaintext = bytes
let ciphertext = bytes

let message_log (gp:game_parameters) = t (nonce gp * ciphertext) (plaintext)
let initialize_message_log = const Seq.createEmpty

let zero_bytes (n:nat) = Seq.create n (UInt8.uint_to_t 0)

//val encrypt: #gp:game_parameters -> log_pre:message_log gp -> n:nonce gp -> k:key gp -> p:plaintext
//  -> c:ciphertext*log_post:message_log gp
let encrypt #gp log_pre n k p =
  let c =
    if gp.b then
      let p' = zero_bytes (length p) in
      gp.scheme.enc n k p'
    else
      gp.scheme.enc n k p
  in
  let log_post = Map.upd log_pre (n,c) p in
  c,log_post

//val decrypt: #gp:game_parameters -> log:message_log gp -> n:nonce gp -> k:key gp -> c:ciphertext -> p:option plaintext
let decrypt #gp log n k c =
  if gp.b then
    let p = Map.sel log (n,c) in
    if p = Seq.createEmpty then
      None
    else
      Some p
  else
    gp.scheme.dec n k c
