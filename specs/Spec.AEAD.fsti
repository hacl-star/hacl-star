module Spec.AEAD
open FStar.Integers
module S = FStar.Seq
type aead_alg =
  | AES128_GCM
  | AES256_GCM
  | CHACHA20_POLY1305
  // the algorithms below are used in TLS 1.3 but not yet supported by
  // EverCrypt or miTLS; they are included e.g. for parsing
  | AES128_CCM  // "Counter with CBC-Message Authentication Code"
  | AES256_CCM
  | AES128_CCM8 // variant with truncated 8-byte tags
  | AES256_CCM8

let supported_aead_alg (a:aead_alg): GTot bool =
  match a with
  | AES128_GCM
  | AES256_GCM
  | CHACHA20_POLY1305 -> true
  | _ -> false

let aead_keyLen : aead_alg -> nat =
  function
  | AES128_GCM        -> 16
  | AES256_GCM        -> 32
  | CHACHA20_POLY1305 -> 32
  | AES128_CCM        -> 16
  | AES128_CCM8       -> 16
  | AES256_CCM        -> 32
  | AES256_CCM8       -> 32

let aead_tagLen : aead_alg -> nat =
  function
  | AES128_CCM8       ->  8
  | AES256_CCM8       ->  8
  | AES128_GCM        -> 16
  | AES256_GCM        -> 16
  | CHACHA20_POLY1305 -> 16
  | AES128_CCM        -> 16
  | AES256_CCM        -> 16

module U32 = FStar.UInt32
let aead_key (a:aead_alg) = Seq.lseq uint_8 (aead_keyLen a)
let aead_ivLen (a:aead_alg) : nat = 12
let aead_cipher (a:aead_alg) (plainlen:nat) = Seq.lseq uint_8 (plainlen + aead_tagLen a)

(* TODO! Move this to some shared place *)
let lbytes (l:nat) = b:Seq.seq UInt8.t {Seq.length b = l}

val state (a:aead_alg) : Type0

val aead_init (#a:aead_alg) (key:aead_key a) : GTot (state a)

val aead_encrypt (#a:aead_alg) (s:state a)
                 (iv:lbytes (aead_ivLen a))
                 (#adlen:nat) (ad:lbytes adlen)
                 (#plainlen:nat) (plain:lbytes plainlen) (* ?? should specs respect confidentiality of plain? *)
   : GTot (aead_cipher a plainlen)


val aead_decrypt (#a:aead_alg) (s:state a)
                 (iv:lbytes (aead_ivLen a))
                 (#adlen:nat) (ad:lbytes adlen)
                 (#plainlen:nat) (cipher:aead_cipher a plainlen)
   : GTot (option (lbytes plainlen))
