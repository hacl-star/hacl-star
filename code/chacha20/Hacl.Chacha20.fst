module Hacl.Chacha20

open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer


[@@ Comment "Encrypt a message `text` with key `key` and nonce `n`, starting from counter `ctr`.

Encryption can be performed in-place, i.e., `out` and `text` can point to the same memory.

@param len Length of the message and ciphertext.
@param out Pointer to `len` bytes of memory where the ciphertext is written to.
@param text Pointer to `len` bytes of memory where the message is read from.
@param key Pointer to 32 bytes of memory where the key is read from.
@param n Pointer to 12 bytes of memory where the nonce is read from.
@param ctr Initial block counter."]
val chacha20_encrypt:
    len:size_t
  -> out:lbuffer uint8 len
  -> text:lbuffer uint8 len
  -> key:lbuffer uint8 32ul
  -> n:lbuffer uint8 12ul
  -> ctr:size_t ->
  Stack unit
  (requires fun h ->
    live h key /\ live h n /\ live h text /\ live h out /\ eq_or_disjoint text out)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_seq h1 out == Spec.Chacha20.chacha20_encrypt_bytes (as_seq h0 key) (as_seq h0 n) (v ctr) (as_seq h0 text))

let chacha20_encrypt len out text key n ctr =
  Hacl.Impl.Chacha20.chacha20_encrypt len out text key n ctr


[@@ Comment "Decrypt a ciphertext `cipher` with key `key` and nonce `n`, starting from counter `ctr`.

Decryption can be performed in-place, i.e., `out` and `cipher` can point to the same memory.

@param len Length of the ciphertext and message.
@param out Pointer to `len` bytes of memory where the message is written to.
@param cipher Pointer to `len` bytes of memory where the ciphertext is read from.
@param key Pointer to 32 bytes of memory where the key is read from.
@param n Pointer to 12 bytes of memory where the nonce is read from.
@param ctr Initial block counter."]
val chacha20_decrypt:
    len:size_t
  -> out:lbuffer uint8 len
  -> cipher:lbuffer uint8 len
  -> key:lbuffer uint8 32ul
  -> n:lbuffer uint8 12ul
  -> ctr:size_t ->
  Stack unit
  (requires fun h ->
    live h key /\ live h n /\ live h cipher /\ live h out /\ eq_or_disjoint cipher out)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_seq h1 out == Spec.Chacha20.chacha20_decrypt_bytes (as_seq h0 key) (as_seq h0 n) (v ctr) (as_seq h0 cipher))

let chacha20_decrypt len out cipher key n ctr =
  Hacl.Impl.Chacha20.chacha20_decrypt len out cipher key n ctr
