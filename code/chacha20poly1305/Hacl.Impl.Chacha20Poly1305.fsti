module Hacl.Impl.Chacha20Poly1305

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module Spec = Spec.Chacha20Poly1305

open Hacl.Impl.Poly1305.Fields


#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 1"

inline_for_extraction noextract
let aead_encrypt_st (w:field_spec) =
    key:lbuffer uint8 32ul
  -> nonce:lbuffer uint8 12ul
  -> alen:size_t
  -> aad:lbuffer uint8 alen
  -> len:size_t
  -> input:lbuffer uint8 len
  -> output:lbuffer uint8 len
  -> tag:lbuffer uint8 16ul ->
  Stack unit
  (requires fun h ->
    live h key /\ live h nonce /\ live h aad /\
    live h input /\ live h output /\ live h tag /\
    disjoint key output /\ disjoint nonce output /\
    disjoint key tag /\ disjoint nonce tag /\
    disjoint output tag /\ eq_or_disjoint input output /\
    disjoint aad output)
  (ensures  fun h0 _ h1 -> modifies2 output tag h0 h1 /\
    Seq.append (as_seq h1 output) (as_seq h1 tag) ==
    Spec.aead_encrypt (as_seq h0 key) (as_seq h0 nonce) (as_seq h0 input) (as_seq h0 aad))


inline_for_extraction noextract
val aead_encrypt: #w:field_spec -> aead_encrypt_st w


inline_for_extraction noextract
let aead_decrypt_st (w:field_spec) =
    key:lbuffer uint8 32ul
  -> nonce:lbuffer uint8 12ul
  -> alen:size_t
  -> aad:lbuffer uint8 alen
  -> len:size_t
  -> input:lbuffer uint8 len
  -> output:lbuffer uint8 len
  -> mac:lbuffer uint8 16ul ->
  Stack UInt32.t
  (requires fun h ->
    live h key /\ live h nonce /\ live h aad /\
    live h input /\ live h output /\ live h mac /\
    eq_or_disjoint input output)
  (ensures  fun h0 z h1 -> modifies1 input h0 h1 /\
   (let plain = Spec.aead_decrypt (as_seq h0 key) (as_seq h0 nonce) (as_seq h0 output) (as_seq h0 mac) (as_seq h0 aad) in
    match z with
    | 0ul -> Some? plain /\ as_seq h1 input == Some?.v plain // decryption succeeded
    | 1ul -> None? plain
    | _ -> false)  // decryption failed
  )


inline_for_extraction noextract
val aead_decrypt: #w:field_spec -> aead_decrypt_st w
