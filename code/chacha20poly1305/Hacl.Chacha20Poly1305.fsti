module Hacl.Chacha20Poly1305

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer

module LSeq = Lib.Sequence
module ST = FStar.HyperStack.ST
module Spec = Spec.Chacha20Poly1305


val aead_encrypt:
    key: lbuffer uint8 32ul
  -> nonce: lbuffer uint8 12ul
  -> alen: size_t
  -> aad: lbuffer uint8 alen
  -> len: size_t{v len + 16 <= max_size_t /\ v alen + v len / 64 <= max_size_t}
  -> input: lbuffer uint8 len
  -> output: lbuffer uint8 len
  -> tag: lbuffer uint8 16ul ->
  Stack unit
    (requires (fun h ->
      disjoint key output /\ disjoint nonce output /\
      disjoint key tag /\ disjoint nonce tag /\
      disjoint output tag /\
      eq_or_disjoint input output /\
      disjoint aad output /\
      live h key /\ live h nonce /\ live h aad /\ live h input /\ live h output /\ live h tag))
    (ensures  (fun h0 _ h1 -> modifies (loc output |+| loc tag) h0 h1 /\
      LSeq.equal
        (LSeq.concat (as_seq h1 output) (as_seq h1 tag))
        (Spec.aead_encrypt (as_seq h0 key) (as_seq h0 nonce) (as_seq h0 input) (as_seq h0 aad))))


val aead_decrypt:
    key: lbuffer uint8 32ul
  -> nonce: lbuffer uint8 12ul
  -> alen: size_t
  -> aad: lbuffer uint8 alen
  -> len: size_t{v len + 16 <= max_size_t /\ v alen + v len / 64 <= max_size_t}
  -> input: lbuffer uint8 len
  -> output: lbuffer uint8 len
  -> mac: lbuffer uint8 16ul ->
  Stack UInt32.t
    (requires (fun h ->
      eq_or_disjoint input output /\
      live h key /\ live h nonce /\ live h aad /\ live h input /\ live h output /\ live h mac))
    (ensures  (fun h0 z h1 -> modifies (loc input) h0 h1 /\
      (let plain = Spec.aead_decrypt (as_seq h0 key) (as_seq h0 nonce) (as_seq h0 output) (as_seq h0 mac) (as_seq h0 aad) in
      match z with
      | 0ul -> Some? plain /\ as_seq h1 input == Some?.v plain // decryption succeeded
      | 1ul -> None? plain
      | _ -> false)  // decryption failed
      )
    )
