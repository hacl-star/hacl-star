module Hacl.Constants

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

(* Type abbreviations *)
type u8  = FStar.UInt8.t
type u32 = FStar.UInt32.t
type u64 = FStar.UInt64.t

type h8  = Hacl.UInt8.t
type h32  = Hacl.UInt32.t
type h64  = Hacl.UInt64.t

type uint8_p = FStar.Buffer.buffer h8

(* Size constants (for specifications) *)
let crypto_box_NONCEBYTES     = 24
let crypto_box_PUBLICKEYBYTES = 32
let crypto_box_SECRETKEYBYTES = 32
let crypto_box_MACBYTES       = 16

let crypto_secretbox_NONCEBYTES = 24
let crypto_secretbox_KEYBYTES   = 32
let crypto_secretbox_MACBYTES   = 16
