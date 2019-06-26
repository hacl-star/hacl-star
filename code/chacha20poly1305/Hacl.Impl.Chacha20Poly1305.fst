module Hacl.Impl.Chacha20Poly1305

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All
open FStar.HyperStack
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.Impl.Chacha20Poly1305.PolyCore
open Hacl.Impl.Poly1305.Fields

module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence

module Spec = Spec.Chacha20Poly1305
module SpecPoly = Spec.Poly1305
module ChachaVec = Hacl.Impl.Chacha20.Vec
module Poly = Hacl.Impl.Poly1305

#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

inline_for_extraction noextract
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
      as_seq h1 out ==
      Spec.poly1305_do (as_seq h0 k) (as_seq h0 m) (as_seq h0 aad))

inline_for_extraction noextract
val poly1305_do_core: #w:field_spec -> poly1305_do_core_st w
let poly1305_do_core #w k aadlen aad mlen m out =
  push_frame();
  let ctx = create (nlimb w +! precomplen w) (limb_zero w) in
  let block = create 16ul (u8 0) in
  poly1305_do_ #w k aadlen aad mlen m ctx block;
  Poly.poly1305_finish out k ctx;
  pop_frame()

[@CInline]
let poly1305_do_32 : poly1305_do_core_st M32 = poly1305_do_core
[@CInline]
let poly1305_do_128 : poly1305_do_core_st M128 = poly1305_do_core
[@CInline]
let poly1305_do_256 : poly1305_do_core_st M256 = poly1305_do_core

inline_for_extraction noextract
val poly1305_do: #w:field_spec -> poly1305_do_core_st w
let poly1305_do #w =
  match w with
  | M32 -> poly1305_do_32
  | M128 -> poly1305_do_128
  | M256 -> poly1305_do_256

unfold noextract
let width_chacha20 (s:field_spec) : Hacl.Spec.Chacha20.Vec.lanes =
  match s with
  | M32  -> 1
  | M128 -> 4
  | M256 -> 8

// Derives the key, and then perform poly1305
inline_for_extraction noextract
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
      let poly_k = LSeq.sub key 0 32 in
      as_seq h1 out == Spec.poly1305_do poly_k (as_seq h0 m) (as_seq h0 aad)))
let derive_key_poly1305_do #w k n aadlen aad mlen m out =
  push_frame ();
  // Create a new buffer to derive the key
  let tmp = create 64ul (u8 0) in
  ChachaVec.chacha20_encrypt #(width_chacha20 w) 64ul tmp tmp k n 0ul;
  // The derived key should only be the first 32 bytes
  let key = sub tmp 0ul 32ul in
  poly1305_do #w key aadlen aad mlen m out;
  pop_frame()

let aead_encrypt #w k n aadlen aad mlen m cipher mac =
  ChachaVec.chacha20_encrypt #(width_chacha20 w) mlen cipher m k n 1ul;
  derive_key_poly1305_do #w k n aadlen aad mlen cipher mac

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
      assert (Lib.ByteSequence.lbytes_eq (as_seq h1 computed_mac) (as_seq h1 mac));
      // If the computed mac matches the mac given, decrypt the ciphertext and return 0
      ChachaVec.chacha20_encrypt #(width_chacha20 w) mlen m cipher k n 1ul;
      0ul
    ) else 1ul // Macs do not agree, do not decrypt
  in
  pop_frame();
  res
