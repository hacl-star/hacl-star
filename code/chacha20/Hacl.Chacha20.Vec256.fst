module Hacl.Chacha20.Vec256

open Hacl.Meta.Chacha20.Vec

[@CInline]
private
let double_round_256 = Hacl.Impl.Chacha20.Core32xN.double_round #8
[@CInline]
private
let chacha20_core_256 = vec_chacha20_core_higher #8 True double_round_256
[@CInline]
private
let chacha20_init_256 = Hacl.Impl.Chacha20.Vec.chacha20_init #8

[@@ Comment "Encrypt a message `text` with key `key` and nonce `n`, starting from counter `ctr`.

Encryption can be performed in-place, i.e., `out` and `text` can point to the same memory.

@param len Length of the message and ciphertext.
@param out Pointer to `len` bytes of memory where the ciphertext is written to.
@param text Pointer to `len` bytes of memory where the message is read from.
@param key Pointer to 32 bytes of memory where the key is read from.
@param n Pointer to 12 bytes of memory where the nonce is read from.
@param ctr Initial block counter."]
let chacha20_encrypt_256 = vec_chacha20_encrypt_higher #8 True chacha20_init_256 chacha20_core_256

[@@ Comment "Decrypt a ciphertext `cipher` with key `key` and nonce `n`, starting from counter `ctr`.

Decryption can be performed in-place, i.e., `out` and `cipher` can point to the same memory.

@param len Length of the ciphertext and message.
@param out Pointer to `len` bytes of memory where the message is written to.
@param cipher Pointer to `len` bytes of memory where the ciphertext is read from.
@param key Pointer to 32 bytes of memory where the key is read from.
@param n Pointer to 12 bytes of memory where the nonce is read from.
@param ctr Initial block counter."]
let chacha20_decrypt_256 = vec_chacha20_decrypt_higher #8 True chacha20_init_256 chacha20_core_256
