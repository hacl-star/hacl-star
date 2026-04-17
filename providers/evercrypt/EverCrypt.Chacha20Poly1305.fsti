module EverCrypt.Chacha20Poly1305

open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
module Seq = Lib.Sequence
open FStar.Mul

module Spec = Spec.Chacha20Poly1305

[@@ Comment "Encrypt and authenticate a message with Chacha20-Poly1305.

Note: `m` and `cipher` can point to the same memory for in-place encryption.

@param k Pointer to 32 bytes of memory where the key is read from.
@param n Pointer to 12 bytes of memory where the nonce is read from.
@param aadlen Length of the associated data.
@param aad Pointer to `aadlen` bytes of memory where the associated data is read from.
@param mlen Length of the message.
@param m Pointer to `mlen` bytes of memory where the message is read from.
@param cipher Pointer to `mlen` bytes of memory where the ciphertext is written to.
@param tag Pointer to 16 bytes of memory where the authentication tag is written to."]
(** @type: true
*)
val aead_encrypt:
  k:lbuffer uint8 32ul -> // key
  n:lbuffer uint8 12ul -> // nonce
  aadlen:size_t ->
  aad:lbuffer uint8 aadlen ->
  (mlen:size_t{v mlen + 16 <= max_size_t /\ v aadlen + v mlen / 64 <= max_size_t}) ->
  m:lbuffer uint8 mlen -> // input: plaintext
  cipher:lbuffer uint8 mlen -> // output: buffer for cipher + mac
  tag:lbuffer uint8 16ul -> // output: buffer for cipher + mac
  Stack unit
    (requires (fun h ->
      disjoint k cipher /\ disjoint n cipher /\
      disjoint k tag /\ disjoint n tag /\
      disjoint cipher tag /\
      eq_or_disjoint m cipher /\
      disjoint aad cipher /\
      live h k /\ live h n /\ live h aad /\ live h m /\ live h cipher /\ live h tag))
    (ensures  (fun h0 _ h1 -> modifies (loc cipher |+| loc tag) h0 h1 /\
      Seq.equal
        (Seq.concat (as_seq h1 cipher) (as_seq h1 tag))
        (Spec.aead_encrypt (as_seq h0 k) (as_seq h0 n) (as_seq h0 m) (as_seq h0 aad))))

[@@ Comment "Verify and decrypt a ciphertext produced with Chacha20-Poly1305.

Note: `m` and `c` can point to the same memory for in-place decryption.

@param k Pointer to 32 bytes of memory where the key is read from.
@param n Pointer to 12 bytes of memory where the nonce is read from.
@param aadlen Length of the associated data.
@param aad Pointer to `aadlen` bytes of memory where the associated data is read from.
@param mlen Length of the ciphertext.
@param m Pointer to `mlen` bytes of memory where the decrypted message is written to.
@param c Pointer to `mlen` bytes of memory where the ciphertext is read from.
@param mac Pointer to 16 bytes of memory where the authentication tag is read from.

@returns 0 on success (MAC verified); 1 on failure."]
(** @type: true
*)
val aead_decrypt:
  k:lbuffer uint8 32ul -> // key
  n:lbuffer uint8 12ul -> // nonce
  aadlen:size_t -> 
  aad:lbuffer uint8 aadlen ->
  (mlen:size_t{v mlen + 16 <= max_size_t /\ v aadlen + v mlen / 64 <= max_size_t}) ->
  m:lbuffer uint8 mlen -> // output: buffer for decrypted plaintext
  c:lbuffer uint8 mlen -> // input: cipher
  mac:lbuffer uint8 16ul -> // input: mac
  Stack UInt32.t
    (requires (fun h ->
      eq_or_disjoint m c /\
      live h k /\ live h n /\ live h aad /\ live h m /\ live h c /\ live h mac))
    (ensures  (fun h0 z h1 -> modifies (loc m) h0 h1 /\
      (let plain = Spec.aead_decrypt (as_seq h0 k) (as_seq h0 n) (as_seq h0 c) (as_seq h0 mac) (as_seq h0 aad) in
      match z with
      | 0ul -> Some? plain /\ as_seq h1 m == Some?.v plain // decryption succeeded
      | 1ul -> None? plain
      | _ -> false)  // decryption failed
      )
    )
