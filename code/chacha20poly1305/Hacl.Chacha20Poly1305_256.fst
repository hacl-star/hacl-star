module Hacl.Chacha20Poly1305_256

open Hacl.Meta.Chacha20Poly1305
open Hacl.Impl.Chacha20Poly1305
open Hacl.Impl.Poly1305.Fields
open Hacl.Poly1305_256

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

[@CInline]
private
let poly1305_padded_256 = Hacl.Impl.Chacha20Poly1305.PolyCore.poly1305_padded #M256

[@CInline]
private
let poly1305_do_256 = chacha20poly1305_poly1305_do_higher #M256 True poly1305_finish poly1305_init poly1305_padded_256

[@@ Comment "Encrypt a message `m` with key `k`.

The arguments `k`, `n`, `aadlen`, and `aad` are same in encryption/decryption.
Note: Encryption and decryption can be executed in-place, i.e., `m` and `cipher` can point to the same memory.

@param k Pointer to 32 bytes of memory where the AEAD key is read from.
@param n Pointer to 12 bytes of memory where the AEAD nonce is read from.
@param aadlen Length of the associated data.
@param aad Pointer to `aadlen` bytes of memory where the associated data is read from.

@param mlen Length of the message.
@param m Pointer to `mlen` bytes of memory where the message is read from.
@param cipher Pointer to `mlen` bytes of memory where the ciphertext is written to.
@param mac Pointer to 16 bytes of memory where the mac is written to."]
let aead_encrypt : aead_encrypt_st M256 =
  chacha20poly1305_aead_encrypt_higher #M256 True poly1305_do_256 Hacl.Chacha20.Vec256.chacha20_encrypt_256

[@@ Comment "Decrypt a ciphertext `cipher` with key `k`.

The arguments `k`, `n`, `aadlen`, and `aad` are same in encryption/decryption.
Note: Encryption and decryption can be executed in-place, i.e., `m` and `cipher` can point to the same memory.

If decryption succeeds, the resulting plaintext is stored in `m` and the function returns the success code 0.
If decryption fails, the array `m` remains unchanged and the function returns the error code 1.

@param k Pointer to 32 bytes of memory where the AEAD key is read from.
@param n Pointer to 12 bytes of memory where the AEAD nonce is read from.
@param aadlen Length of the associated data.
@param aad Pointer to `aadlen` bytes of memory where the associated data is read from.

@param mlen Length of the ciphertext.
@param m Pointer to `mlen` bytes of memory where the message is written to.
@param cipher Pointer to `mlen` bytes of memory where the ciphertext is read from.
@param mac Pointer to 16 bytes of memory where the mac is read from.

@returns 0 on succeess; 1 on failure."]
let aead_decrypt : aead_decrypt_st M256 =
  chacha20poly1305_aead_decrypt_higher #M256 True Hacl.Chacha20.Vec256.chacha20_encrypt_256 poly1305_do_256
