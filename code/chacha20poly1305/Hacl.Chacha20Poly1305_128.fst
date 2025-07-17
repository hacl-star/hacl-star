module Hacl.Chacha20Poly1305_128


open Hacl.Meta.Chacha20Poly1305
open Hacl.Impl.Chacha20Poly1305
open Hacl.Impl.Poly1305.Fields
open Hacl.Poly1305_128

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

[@CInline]
private
let poly1305_padded_128 = Hacl.Impl.Chacha20Poly1305.PolyCore.poly1305_padded #M128
[@CInline]
private
let poly1305_do_128 = chacha20poly1305_poly1305_do_higher #M128 True poly1305_finish poly1305_init poly1305_padded_128

[@@ Comment "Encrypt a message `input` with key `key`.

The arguments `key`, `nonce`, `data`, and `data_len` are same in encryption/decryption.
Note: Encryption and decryption can be executed in-place, i.e., `input` and `output` can point to the same memory.

@param output Pointer to `input_len` bytes of memory where the ciphertext is written to.
@param tag Pointer to 16 bytes of memory where the mac is written to.
@param input Pointer to `input_len` bytes of memory where the message is read from.
@param input_len Length of the message.
@param data Pointer to `data_len` bytes of memory where the associated data is read from.
@param data_len Length of the associated data.
@param key Pointer to 32 bytes of memory where the AEAD key is read from.
@param nonce Pointer to 12 bytes of memory where the AEAD nonce is read from."]
let encrypt : aead_encrypt_st M128 =
  chacha20poly1305_aead_encrypt_higher #M128 True poly1305_do_128 Hacl.Chacha20.Vec128.chacha20_encrypt_128

[@@ Comment "Decrypt a ciphertext `input` with key `key`.

The arguments `key`, `nonce`, `data`, and `data_len` are same in encryption/decryption.
Note: Encryption and decryption can be executed in-place, i.e., `input` and `output` can point to the same memory.

If decryption succeeds, the resulting plaintext is stored in `output` and the function returns the success code 0.
If decryption fails, the array `output` remains unchanged and the function returns the error code 1.

@param output Pointer to `input_len` bytes of memory where the message is written to.
@param input Pointer to `input_len` bytes of memory where the ciphertext is read from.
@param input_len Length of the ciphertext.
@param data Pointer to `data_len` bytes of memory where the associated data is read from.
@param data_len Length of the associated data.
@param key Pointer to 32 bytes of memory where the AEAD key is read from.
@param nonce Pointer to 12 bytes of memory where the AEAD nonce is read from.
@param tag Pointer to 16 bytes of memory where the mac is read from.

@returns 0 on succeess; 1 on failure."]
let decrypt : aead_decrypt_st M128 =
  chacha20poly1305_aead_decrypt_higher #M128 True Hacl.Chacha20.Vec128.chacha20_encrypt_128 poly1305_do_128
