module Hacl.Impl.Generic.AEAD

open FStar.HyperStack
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer

module S = Spec.Agile.HPKE
module AEAD = Spec.Agile.AEAD

inline_for_extraction noextract
let kv (a:AEAD.alg) = lbuffer uint8 (size (AEAD.key_length a))
inline_for_extraction noextract
let iv (a:AEAD.alg) = lbuffer uint8 12ul
inline_for_extraction noextract
let tag (a:AEAD.alg) = lbuffer uint8 (size (AEAD.tag_length a))

inline_for_extraction noextract
let aead_encrypt_st (a:AEAD.supported_alg) =
     key:kv a
  -> nonce:iv a
  -> alen:size_t{v alen <= AEAD.max_length a}
  -> aad:lbuffer uint8 alen
  -> len:size_t{v len + 16 <= max_size_t}
  -> input:lbuffer uint8 len
  -> output:lbuffer uint8 (size (v len + 16)) ->
  Stack unit
  (requires fun h ->
    live h key /\ live h nonce /\ live h aad /\
    live h input /\ live h output /\
    disjoint key output /\ disjoint nonce output /\
    eq_or_disjoint input output /\ disjoint aad output)
  (ensures  fun h0 _ h1 -> modifies (loc output) h0 h1 /\
    (as_seq h1 output) `Seq.equal`
    AEAD.encrypt #a (as_seq h0 key) (as_seq h0 nonce) (as_seq h0 aad) (as_seq h0 input))

inline_for_extraction noextract
let aead_decrypt_st (a:AEAD.supported_alg) =
    key:kv a
  -> nonce:iv a
  -> alen:size_t{v alen <= AEAD.max_length a}
  -> aad:lbuffer uint8 alen
  -> len:size_t{v len <= AEAD.max_length a /\ v len + 16 <= max_size_t}
  -> input:lbuffer uint8 len
  -> output:lbuffer uint8 (size (v len  + 16)) ->
  Stack UInt32.t
  (requires fun h ->
    live h key /\ live h nonce /\ live h aad /\
    live h input /\ live h output /\
    eq_or_disjoint input output)
  (ensures  fun h0 z h1 -> modifies1 input h0 h1 /\
   (let plain = AEAD.decrypt #a (as_seq h0 key) (as_seq h0 nonce) (as_seq h0 aad) (as_seq h0 output) in
    match z with
    | 0ul -> Some? plain /\ as_seq h1 input `Seq.equal` Some?.v plain // decryption succeeded
    | 1ul -> None? plain
    | _ -> false)  // decryption failed
  )

[@ Meta.Attribute.specialize]
assume val aead_encrypt: #cs:S.ciphersuite -> aead_encrypt_st (S.aead_of_cs cs)

[@ Meta.Attribute.specialize]
assume val aead_decrypt: #cs:S.ciphersuite -> aead_decrypt_st (S.aead_of_cs cs)
