module Spec.SecretBox

open FStar.Seq
open FStar.UInt32
open FStar.Endianness
open Spec.Lib

let keylen =   32 (* in bytes *)
let noncelen = 24 (* in bytes *)

type key = lbytes keylen
type nonce = lbytes noncelen
type bytes = seq UInt8.t

#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 30"
val secretbox_detached: m:bytes{length m / Spec.Salsa20.blocklen < pow2 32} ->
    k:key -> n:nonce -> Tot (lbytes (length m) * Spec.Poly1305.tag) 
let secretbox_detached m k n = 
    let (n1,n2) = split n 16 in
    let subkey:Spec.Salsa20.key = Spec.HSalsa20.hsalsa20 k n1 in
    let b0 = Spec.Salsa20.salsa20_block k n2 0 in
    let mackey = slice b0 0 32 in
    let mlen = length m in
    let mlen0 = if mlen < 32 then mlen else 32 in
    let (m0,rest) = split m mlen0 in
    let b0 = create 32 0uy @| m0 in
    let c0 = Spec.Salsa20.salsa20_encrypt_bytes subkey n2 0 b0 in
    let c0 = slice c0 32 64 in
    let crest = Spec.Salsa20.salsa20_encrypt_bytes subkey n2 1 rest in
    let cipher = c0 @| crest in
    let mac = Spec.Poly1305.poly1305 cipher mackey in
    (cipher, mac)
            
val secretbox_open_detached: c:bytes{length c / Spec.Salsa20.blocklen < pow2 32} ->
    mac:Spec.Poly1305.tag -> k:key -> n:nonce -> Tot (option (lbytes (length c)))
let secretbox_open_detached cipher mac k n = 
    let (n1,n2) = split n 16 in
    let subkey = Spec.HSalsa20.hsalsa20 k n1 in
    let b0 = Spec.Salsa20.salsa20_block k n2 0 in
    let mackey = slice b0 0 32 in
    let xmac = Spec.Poly1305.poly1305 cipher mackey in
    if xmac = mac then 
      let clen = length cipher in
      let clen0 = if clen < 32 then clen else 32 in
      let c0,crest = split cipher clen0 in
      let b0 = create 32 0uy @| c0 in
      let m0 = Spec.Salsa20.salsa20_encrypt_bytes subkey n2 0 b0 in
      let m0 = slice m0 32 (32+clen0) in
      let mrest = Spec.Salsa20.salsa20_encrypt_bytes subkey n2 1 crest in
      Some (m0 @| mrest)
    else None

let test() = true