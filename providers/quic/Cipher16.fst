module Cipher16

module G = FStar.Ghost
module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer
module U8 = FStar.UInt8
module U32 = FStar.UInt32

open FStar.HyperStack.ST
open EverCrypt.Helpers
open EverCrypt.Error

module AC = EverCrypt.AutoConfig2
module SC = EverCrypt.StaticConfig
module SC16 = Spec.Cipher16

// FIXME: integrate CTR spec and impl
#set-options "--admit_smt_queries true"

let create a k =
  match a with
  | SC16.AES128 ->
    let b = B.malloc HS.root 0uy 432ul in
    B.blit k 0ul b 0ul 16ul;
//    EverCrypt.Hacl.aes128_keyExpansion (B.sub b 0ul 176ul);
//    EverCrypt.Hacl.aes128_mk_sbox (B.sub b 176ul 256ul);
    b
  | SC16.AES256 ->
    let b = B.malloc HS.root 0uy 496ul in
    B.blit k 0ul b 0ul 32ul;
//    EverCrypt.Hacl.aes128_keyExpansion (B.sub b 0ul 176ul);
//    EverCrypt.Hacl.aes128_mk_sbox (B.sub b 176ul 256ul);
    b
  | SC16.CHACHA20 ->
    let b = B.malloc HS.root 0uy 32ul in
    B.blit k 0ul b 0ul 32ul; b

(* FIXME(adl) this should be done in EverCrypt.Cipher *)
let compute #a #gk st input output =
  let open FStar.Endianness in
  let open LowStar.Endianness in
  match a with
  | SC16.AES128 ->
    let st = EverCrypt.aes128_create (B.sub st 0ul 16ul) in
    EverCrypt.aes128_compute st input output;
    EverCrypt.aes128_free st
  | SC16.AES256 ->
    let st = EverCrypt.aes256_create (B.sub st 0ul 32ul) in
    EverCrypt.aes256_compute st input output;
    EverCrypt.aes256_free st
  | SC16.CHACHA20 ->
    let zb = B.alloca 0uy 16ul in
    let ctr = load32_le_i input 0ul in
    EverCrypt.Cipher.chacha20 16ul output zb st (B.sub input 4ul 12ul) ctr

(*
let 

let block a k ib ob =
  match a with
  | AES128 ->
    let 
