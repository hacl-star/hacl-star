module Spec.SecretBox2

open FStar.Seq
open FStar.UInt32

open Spec.HSalsa20
open Spec.Poly1305
open Spec.Salsa20


#reset-options "--max_fuel 0 --z3rlimit 20"

let bytes = seq UInt8.t
let nonce = b:bytes{length b = 24}
let key   = b:bytes{length b = 32}


let secretbox (msg:bytes{length msg < pow2 32 - 32}) (n:nonce) (k:key) =
  let n_hsalsa, n_salsa = split n 16 in
  let subkey = hsalsa20 k n_hsalsa in
  let zeros  = create 32 0uy in
  let cipher = salsa20_encrypt_bytes subkey n_salsa 0 (zeros @| msg) in
  let k_poly, c = split cipher 32 in
  let mac    = poly1305 c k_poly in
  (mac, c)


let secretbox_open (mac:bytes{length mac = 16}) (cipher:bytes{length cipher < pow2 32 - 32}) (n:nonce) (k:key) =
  let n_hsalsa, n_salsa = split n 16 in
  let subkey = hsalsa20 k n_hsalsa in
  let zeros  = create 32 0uy in
  let k_poly = salsa20_encrypt_bytes subkey n_salsa 0 zeros in
  let cmac   = poly1305 cipher k_poly in
  if cmac = mac then 
    let plain = salsa20_encrypt_bytes subkey n_salsa 0 (zeros @| cipher) in
    Some (zeros @| slice plain 32 (length plain))
  else None #bytes
