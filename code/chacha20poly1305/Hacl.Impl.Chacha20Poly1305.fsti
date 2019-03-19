module Hacl.Impl.Chacha20Poly1305

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
module Seq = Lib.Sequence
open FStar.Mul

module Spec = Spec.Chacha20Poly1305

val aead_encrypt_chacha_poly:
  k:lbuffer uint8 32ul -> // key
  n:lbuffer uint8 12ul -> // nonce
  aadlen:size_t ->
  aad:lbuffer uint8 aadlen ->
  (mlen:size_t{v mlen + 16 <= max_size_t /\ v aadlen + v mlen / 64 <= max_size_t}) ->
  m:lbuffer uint8 mlen -> // input: plaintext
  out:lbuffer uint8 (UInt32.add mlen 16ul) -> // output: buffer for cipher + mac
  Stack unit
    (requires (fun h ->
      disjoint k out /\
      disjoint n out /\
      eq_or_disjoint m out /\
      disjoint aad out /\
      live h k /\ live h n /\ live h aad /\ live h m /\ live h out))
    (ensures  (fun h0 _ h1 -> modifies (loc out) h0 h1 /\
      Seq.equal
        (as_seq h1 out)
        (Spec.aead_encrypt (as_seq h0 k) (as_seq h0 n) (as_seq h0 m) (as_seq h0 aad))
    ))

val aead_decrypt_chacha_poly:
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
      (z == 0ul ==> (Some? plain /\ (as_seq h1 m == Some?.v plain))) /\ // decryption succeeded
      (z == 1ul ==> (None? plain))  // decryption failed
      )
    ))
