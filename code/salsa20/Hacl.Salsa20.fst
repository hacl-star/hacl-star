module Hacl.Salsa20

open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer

module Spec = Spec.Salsa20


[@@ Comment "Encrypt a message `text` with key `key` and nonce `n`, starting from counter `ctr`.

Encryption can be performed in-place, i.e., `out` and `text` can point to the same memory.

Note: Salsa20 uses an 8-byte nonce (unlike Chacha20 which uses 12 bytes).

@param len Length of the message and ciphertext.
@param out Pointer to `len` bytes of memory where the ciphertext is written to.
@param text Pointer to `len` bytes of memory where the message is read from.
@param key Pointer to 32 bytes of memory where the key is read from.
@param n Pointer to 8 bytes of memory where the nonce is read from.
@param ctr Initial block counter."]
val salsa20_encrypt:
    len:size_t
  -> out:lbuffer uint8 len
  -> text:lbuffer uint8 len
  -> key:lbuffer uint8 32ul
  -> n:lbuffer uint8 8ul
  -> ctr:size_t ->
  Stack unit
  (requires fun h -> live h key /\ live h n /\ live h text /\ live h out /\ eq_or_disjoint text out)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_seq h1 out == Spec.salsa20_encrypt_bytes (as_seq h0 key) (as_seq h0 n) (v ctr) (as_seq h0 text))

let salsa20_encrypt len out text key n ctr =
  Hacl.Impl.Salsa20.salsa20_encrypt len out text key n ctr


[@@ Comment "Decrypt a ciphertext `cipher` with key `key` and nonce `n`, starting from counter `ctr`.

Decryption can be performed in-place, i.e., `out` and `cipher` can point to the same memory.

Note: Salsa20 uses an 8-byte nonce (unlike Chacha20 which uses 12 bytes).

@param len Length of the ciphertext and message.
@param out Pointer to `len` bytes of memory where the message is written to.
@param cipher Pointer to `len` bytes of memory where the ciphertext is read from.
@param key Pointer to 32 bytes of memory where the key is read from.
@param n Pointer to 8 bytes of memory where the nonce is read from.
@param ctr Initial block counter."]
val salsa20_decrypt:
    len:size_t
  -> out:lbuffer uint8 len
  -> cipher:lbuffer uint8 len
  -> key:lbuffer uint8 32ul
  -> n:lbuffer uint8 8ul
  -> ctr:size_t ->
  Stack unit
  (requires fun h -> live h key /\ live h n /\ live h cipher /\ live h out /\ eq_or_disjoint cipher out)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_seq h1 out == Spec.salsa20_decrypt_bytes (as_seq h0 key) (as_seq h0 n) (v ctr) (as_seq h0 cipher))

let salsa20_decrypt len out cipher key n ctr =
  Hacl.Impl.Salsa20.salsa20_decrypt len out cipher key n ctr


[@@ Comment "Compute the first Salsa20 keystream block for key `key` and nonce `n`.

@param out Pointer to 64 bytes of memory where the keystream block is written to.
@param key Pointer to 32 bytes of memory where the key is read from.
@param n Pointer to 8 bytes of memory where the nonce is read from."]
val salsa20_key_block0:
    out:lbuffer uint8 64ul
  -> key:lbuffer uint8 32ul
  -> n:lbuffer uint8 8ul ->
  Stack unit
  (requires fun h -> live h key /\ live h n /\ live h out)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_seq h1 out == Spec.Salsa20.salsa20_key_block0 (as_seq h0 key) (as_seq h0 n))

let salsa20_key_block0 out key n =
  Hacl.Impl.Salsa20.salsa20_key_block0 out key n


[@@ Comment "Compute the HSalsa20 subkey for key `key` and nonce `n`.

Note: HSalsa20 uses a 16-byte nonce (unlike Salsa20 which uses 8 bytes).

@param out Pointer to 32 bytes of memory where the subkey is written to.
@param key Pointer to 32 bytes of memory where the key is read from.
@param n Pointer to 16 bytes of memory where the nonce is read from."]
val hsalsa20:
    out:lbuffer uint8 32ul
  -> key:lbuffer uint8 32ul
  -> n:lbuffer uint8 16ul ->
  Stack unit
  (requires fun h -> live h key /\ live h n /\ live h out)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_seq h1 out == Spec.hsalsa20 (as_seq h0 key) (as_seq h0 n))

let hsalsa20 out key n =
  Hacl.Impl.HSalsa20.hsalsa20 out key n
