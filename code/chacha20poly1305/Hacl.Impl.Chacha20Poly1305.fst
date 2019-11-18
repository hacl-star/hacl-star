module Hacl.Impl.Chacha20Poly1305

open FStar.HyperStack.All
open FStar.HyperStack
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.Impl.Chacha20Poly1305.PolyCore
open Hacl.Impl.Poly1305.Fields

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence

module Spec = Spec.Chacha20Poly1305
module SpecPoly = Spec.Poly1305
module Poly = Hacl.Impl.Poly1305

#reset-options "--z3rlimit 150 --max_fuel 0 --max_ifuel 1 --record_options"

val poly1305_do_:
    #w:field_spec
  -> k:lbuffer uint8 32ul // key
  -> aadlen:size_t
  -> aad:lbuffer uint8 aadlen // authenticated additional data
  -> mlen:size_t
  -> m:lbuffer uint8 mlen // plaintext
  -> ctx:Poly.poly1305_ctx w
  -> block:lbuffer uint8 16ul ->
  Stack unit
  (requires fun h ->
    live h k /\ live h aad /\ live h m /\ live h ctx /\ live h block /\
    disjoint ctx k /\ disjoint ctx aad /\ disjoint ctx m /\ disjoint ctx block /\
    disjoint block k /\ disjoint block aad /\ disjoint block m)
  (ensures fun h0 _ h1 ->
    modifies (loc ctx |+| loc block) h0 h1 /\
    (let acc, r = SpecPoly.poly1305_init (as_seq h0 k) in
    let acc = Spec.poly1305_padded r (as_seq h0 aad) acc in
    let acc = Spec.poly1305_padded r (as_seq h0 m) acc in
    let block_s = LSeq.concat (BSeq.uint_to_bytes_le #U64 (u64 (length aad)))
      (BSeq.uint_to_bytes_le #U64 (u64 (length m))) in
    let acc = SpecPoly.poly1305_update1 r 16 block_s acc in
    Poly.as_get_acc h1 ctx == acc /\ as_seq h1 block == block_s /\
    Poly.state_inv_t h1 ctx))
[@Meta.Attribute.inline_]
let poly1305_do_ #w k aadlen aad mlen m ctx block =
  Poly.poly1305_init ctx k;
  poly1305_padded ctx aadlen aad;
  poly1305_padded ctx mlen m;
  let h0 = ST.get () in
  update_sub_f h0 block 0ul 8ul
    (fun h -> BSeq.uint_to_bytes_le #U64 (to_u64 aadlen))
    (fun _ -> uint_to_bytes_le (sub block 0ul 8ul) (to_u64 aadlen));
  let h1 = ST.get () in
  //assert (LSeq.sub (as_seq h1 block) 0 8 == BSeq.uint_to_bytes_le #U64 (to_u64 aadlen));
  Poly.reveal_ctx_inv ctx h0 h1;
  update_sub_f h1 block 8ul 8ul
    (fun h -> BSeq.uint_to_bytes_le #U64 (to_u64 mlen))
    (fun _ -> uint_to_bytes_le (sub block 8ul 8ul) (to_u64 mlen));
  let h2 = ST.get () in
  //assert (LSeq.sub (as_seq h2 block) 8 8 == BSeq.uint_to_bytes_le #U64 (to_u64 mlen));
  LSeq.eq_intro (LSeq.sub (as_seq h2 block) 0 8) (BSeq.uint_to_bytes_le #U64 (to_u64 aadlen));
  LSeq.lemma_concat2 8 (BSeq.uint_to_bytes_le #U64 (to_u64 aadlen)) 8 (BSeq.uint_to_bytes_le #U64 (to_u64 mlen)) (as_seq h2 block);
  //assert (as_seq h2 block == LSeq.concat (BSeq.uint_to_bytes_le #U64 (to_u64 aadlen)) (BSeq.uint_to_bytes_le #U64 (to_u64 mlen)));
  Poly.reveal_ctx_inv ctx h1 h2;
  Poly.poly1305_update1 ctx block


// Implements the actual poly1305_do operation
inline_for_extraction noextract
let poly1305_do_core_st (w:field_spec) =
    k:lbuffer uint8 32ul // key
  -> aadlen:size_t
  -> aad:lbuffer uint8 aadlen // authenticated additional data
  -> mlen:size_t
  -> m:lbuffer uint8 mlen // plaintext
  -> out:lbuffer uint8 16ul -> // output: tag
  Stack unit
  (requires fun h ->
    live h k /\ live h aad /\ live h m /\ live h out /\
    disjoint k out)
  (ensures fun h0 _ h1 ->
    modifies (loc out) h0 h1 /\
    as_seq h1 out == Spec.poly1305_do (as_seq h0 k) (as_seq h0 m) (as_seq h0 aad))


noextract
val poly1305_do: #w:field_spec -> poly1305_do_core_st w
[@Meta.Attribute.specialize]
let poly1305_do #w k aadlen aad mlen m out =
  push_frame();
  let ctx = create (nlimb w +! precomplen w) (limb_zero w) in
  let block = create 16ul (u8 0) in
  poly1305_do_ #w k aadlen aad mlen m ctx block;
  Poly.poly1305_finish out k ctx;
  pop_frame()


unfold noextract
let width_chacha20 (s:field_spec) : Hacl.Spec.Chacha20.Vec.lanes =
  match s with
  | M32  -> 1
  | M128 -> 4
  | M256 -> 8

[@ Meta.Attribute.specialize ]
assume val chacha20_encrypt: #w:field_spec ->
  Hacl.Impl.Chacha20.Vec.chacha20_encrypt_st (width_chacha20 w)

// Derives the key, and then perform poly1305
val derive_key_poly1305_do:
    #w:field_spec
  -> k:lbuffer uint8 32ul
  -> n:lbuffer uint8 12ul
  -> aadlen:size_t
  -> aad:lbuffer uint8 aadlen
  -> mlen:size_t
  -> m:lbuffer uint8 mlen
  -> out:lbuffer uint8 16ul ->
  Stack unit
  (requires fun h ->
    live h k /\ live h n /\ live h aad /\ live h m /\ live h out)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    (let key:LSeq.lseq uint8 64 = Spec.Chacha20.chacha20_encrypt_bytes (as_seq h0 k) (as_seq h0 n) 0 (LSeq.create 64 (u8 0)) in
    as_seq h1 out == Spec.poly1305_do (LSeq.sub key 0 32) (as_seq h0 m) (as_seq h0 aad)))
[@ Meta.Attribute.inline_ ]
let derive_key_poly1305_do #w k n aadlen aad mlen m out =
  push_frame ();
  // Create a new buffer to derive the key
  let tmp = create 64ul (u8 0) in
  chacha20_encrypt #w 64ul tmp tmp k n 0ul;
  // The derived key should only be the first 32 bytes
  let key = sub tmp 0ul 32ul in
  poly1305_do #w key aadlen aad mlen m out;
  pop_frame()

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

noextract
val aead_encrypt: #w:field_spec -> aead_encrypt_st w

[@ Meta.Attribute.specialize ]
let aead_encrypt #w k n aadlen aad mlen m cipher mac =
  chacha20_encrypt #w mlen cipher m k n 1ul;
  derive_key_poly1305_do #w k n aadlen aad mlen cipher mac



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


noextract
val aead_decrypt: #w:field_spec -> aead_decrypt_st w

[@ Meta.Attribute.specialize ]
let aead_decrypt #w k n aadlen aad mlen m cipher mac =
  push_frame();
  let h0 = get() in
  // Create a buffer to store the temporary mac
  let computed_mac = create 16ul (u8 0) in
  // Compute the expected mac using Poly1305
  derive_key_poly1305_do #w k n aadlen aad mlen cipher computed_mac;
  let h1 = get() in
  let res =
    if lbytes_eq computed_mac mac then (
      assert (BSeq.lbytes_eq (as_seq h1 computed_mac) (as_seq h1 mac));
      // If the computed mac matches the mac given, decrypt the ciphertext and return 0
      chacha20_encrypt #w mlen m cipher k n 1ul;
      0ul
    ) else 1ul // Macs do not agree, do not decrypt
  in
  pop_frame();
  res
