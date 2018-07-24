module Spec.External

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence


(** Random *)
assume val random_generate: len:size_nat -> Tot (lbytes len)
assume val random_generate_public: len:size_nat -> Tot (lseq FStar.UInt8.t len)

(** AES GCM *)
inline_for_extraction
let vsize_aes_gcm_key: size_nat = 16

inline_for_extraction
let vsize_aes_gcm_iv: size_nat = 12

type aes_gcm_key = lbytes 16
type aes_gcm_iv = lbytes 12

assume val aes_gcm_encrypt:
    #olen:size_nat
  -> key:lbytes vsize_aes_gcm_key
  -> iv:lbytes vsize_aes_gcm_iv
  -> adlen:size_nat
  -> ad:lbytes adlen
  -> len:size_nat
  -> plaintext:lbytes len ->
  Tot (lbytes olen)

assume val aes_gcm_decrypt:
    #olen:size_nat
  -> key:lbytes vsize_aes_gcm_key
  -> iv:lbytes vsize_aes_gcm_iv
  -> adlen:size_nat
  -> ad:lbytes adlen
  -> len:size_nat
  -> ciphertext:lbytes len ->
  Tot (lbytes olen)

