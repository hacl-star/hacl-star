module Hacl.Impl.Chacha20Poly1305.Poly

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
module Chacha = Hacl.Impl.Chacha20
module ChachaCore = Hacl.Impl.Chacha20.Core32

module SpecPoly = Spec.Poly1305
module Poly = Hacl.Impl.Poly1305

#set-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 0"

val derive_key:
    k:lbuffer uint8 32ul
  -> n:lbuffer uint8 12ul
  -> out:lbuffer uint8 64ul ->
  Stack unit
    (requires fun h -> live h k /\ live h out /\ live h n /\
      disjoint k out /\ disjoint n out)
    (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\
      as_seq h1 out == Spec.Chacha20.chacha20_key_block0 (as_seq h0 k) (as_seq h0 n))
let derive_key k n out =
  push_frame();
  let ctx = ChachaCore.create_state () in
  let ctx_core = ChachaCore.create_state () in
  Chacha.chacha20_init ctx k n 0ul;
  Chacha.chacha20_core ctx_core ctx 0ul;
  ChachaCore.store_state out ctx_core;
  pop_frame()

val poly1305_do_core_padded:
    aadlen:size_t
  -> aad:lbuffer uint8 aadlen // authenticated additional data
  -> mlen:size_t{v mlen + 16 <= max_size_t /\ v aadlen + v mlen / 64 <= max_size_t}
  -> m:lbuffer uint8 mlen // plaintext
  -> ctx:Poly.poly1305_ctx M32 ->
  Stack unit
    (requires fun h ->
      live h aad /\ live h m /\ live h ctx /\
      disjoint ctx aad /\ disjoint ctx m /\
      Poly.state_inv_t h ctx)
    (ensures fun h0 _ h1 -> modifies (loc ctx) h0 h1 /\
      Poly.state_inv_t h1 ctx /\
      // Additional framing for r_elem
      Poly.as_get_r h0 ctx == Poly.as_get_r h1 ctx /\
      (let r = Poly.as_get_r h0 ctx in
      let acc = Poly.as_get_acc h0 ctx in
      let acc = Spec.poly1305_padded r (v aadlen) (as_seq h0 aad) (LSeq.create 16 (u8 0)) acc in
      let acc = Spec.poly1305_padded r (v mlen) (as_seq h0 m) (LSeq.create 16 (u8 0)) acc in
      Poly.as_get_acc h1 ctx == acc))
let poly1305_do_core_padded aadlen aad mlen m ctx =
  let h_pre = ST.get() in
  push_frame();
  let h0 = ST.get() in
  Poly.reveal_ctx_inv ctx h_pre h0;
  // TODO: This should use the temporary buffer from the main function, but adding it to the modifies clause blows up verification
  let block = create 16ul (u8 0) in
  let h1 = get() in
  Poly.reveal_ctx_inv ctx h_pre h1;
  poly1305_padded ctx aadlen aad block;
  let h2 = ST.get() in
  // Reset block, as it is modified in stateful code but not in the spec
  mapT 16ul block (fun _ -> u8 0) block;
  let h3 = ST.get() in
  LSeq.eq_intro (as_seq h3 block) (LSeq.create 16 (u8 0));
  //assert (as_seq h3 block == LLSeq.create 16 (u8 0));
  Poly.reveal_ctx_inv ctx h2 h3;
  poly1305_padded ctx mlen m block;
  let h4 = ST.get() in
  pop_frame();
  let h_pop = ST.get() in
  Poly.reveal_ctx_inv ctx h4 h_pop

val poly1305_do_core_to_bytes:
    aadlen:size_t
  -> mlen:size_t{v mlen + 16 <= max_size_t /\ v aadlen + v mlen / 64 <= max_size_t}
  -> block:lbuffer uint8 16ul ->
  Stack unit
    (requires fun h -> live h block)
    (ensures  fun h0 _ h1 -> modifies (loc block) h0 h1 /\
     (let gaad_len8 = BSeq.uint_to_bytes_le #U64 (u64 (v aadlen)) in
      let gciphertext_len8 = BSeq.uint_to_bytes_le #U64 (u64 (v mlen)) in
      let gblock = LSeq.update_sub (as_seq h0 block) 0 8 gaad_len8 in
      let gblock = LSeq.update_sub gblock 8 8 gciphertext_len8 in
      LSeq.equal (as_seq h1 block) gblock))
let poly1305_do_core_to_bytes aadlen mlen block =
  // Encode the length of the aad into bytes,
  // and store it in the first eight bytes of the temporary block
  let h0 = ST.get() in
  let aad_len8 = sub block 0ul 8ul in
  uint_to_bytes_le #U64 aad_len8 (to_u64 aadlen);

  // Repeat with the length of the input, and store it in the second eight bytes
  let cipher_len8 = sub block 8ul 8ul in
  uint_to_bytes_le #U64 cipher_len8 (to_u64 mlen);
  let h2 = ST.get() in
  let aux (i:nat{i < 16}) : Lemma
    (let gaad_len8 = BSeq.uint_to_bytes_le #U64 (u64 (v aadlen)) in
     let gciphertext_len8 = BSeq.uint_to_bytes_le #U64 (u64 (v mlen)) in
     let gblock = LSeq.update_sub (as_seq h0 block) 0 8 gaad_len8 in
     let gblock = LSeq.update_sub gblock 8 8 gciphertext_len8 in
     LSeq.index (as_seq h2 block) i == LSeq.index gblock i)
  = uintv_extensionality (to_u64 aadlen) (u64 (v aadlen));
    uintv_extensionality (to_u64 mlen) (u64 (v mlen));
    let gaad_len8 = BSeq.uint_to_bytes_le #U64 (to_u64 aadlen) in
    let gciphertext_len8 = BSeq.uint_to_bytes_le #U64 (to_u64 mlen) in
    let s1 = LSeq.update_sub (as_seq h0 block) 0 8 gaad_len8 in
    let s2 = LSeq.update_sub s1 8 8 gciphertext_len8 in
    let s_final = LSeq.index (as_seq h2 block) in
    if i < 8 then
       assert (LSeq.index s2 i == LSeq.index gaad_len8 i)
    else
      assert (LSeq.index s2 i == LSeq.index gciphertext_len8 (i-8))
  in
  Classical.forall_intro aux

val poly1305_do_core_finish:
    k:lbuffer uint8 32ul // key
  -> out:lbuffer uint8 16ul // output: tag
  -> ctx:Poly.poly1305_ctx M32
  -> block:lbuffer uint8 16ul ->
  Stack unit
    (requires fun h ->
      live h k /\ live h out /\ live h ctx /\ live h block /\
      disjoint out k /\
      disjoint ctx k /\ disjoint ctx out /\ disjoint ctx block /\
      disjoint block k /\ disjoint block out /\
      Poly.state_inv_t h ctx)
    (ensures fun h0 _ h1 -> modifies (loc out |+| loc ctx) h0 h1 /\
      (let r = Poly.as_get_r h0 ctx in
       let acc = Poly.as_get_acc h0 ctx in
       let acc = SpecPoly.update1 r 16 (as_seq h0 block) acc in
       let tag = SpecPoly.finish (as_seq h0 k) acc in
       as_seq h1 out == tag))
let poly1305_do_core_finish k out ctx block =
  update1 ctx 16ul block;
  finish ctx k out

val poly1305_do_core_:
    k:lbuffer uint8 32ul // key
  -> aadlen:size_t
  -> aad:lbuffer uint8 aadlen // authenticated additional data
  -> mlen:size_t{v mlen + 16 <= max_size_t /\ v aadlen + v mlen / 64 <= max_size_t}
  -> m:lbuffer uint8 mlen  // plaintext
  -> out:lbuffer uint8 16ul // output: tag
  -> ctx:Poly.poly1305_ctx M32
  -> block:lbuffer uint8 16ul ->
  Stack unit
    (requires fun h ->
      live h k /\ live h aad /\ live h m /\ live h out /\ live h ctx /\ live h block /\
      disjoint k out /\
      disjoint ctx k /\ disjoint ctx aad /\ disjoint ctx m /\ disjoint ctx out /\ disjoint ctx block /\
      disjoint block k /\ disjoint block aad /\ disjoint block m /\ disjoint block out /\
      as_seq h block == LSeq.create 16 (u8 0))
    (ensures fun h0 _ h1 -> modifies (loc out |+| loc ctx |+| loc block) h0 h1 /\
      as_seq h1 out ==
      Spec.poly1305_do (as_seq h0 k) (v mlen) (as_seq h0 m) (v aadlen) (as_seq h0 aad))
let poly1305_do_core_ k aadlen aad mlen m out ctx block =
  poly1305_init ctx k;

  poly1305_do_core_padded aadlen aad mlen m ctx;

  let h3 = ST.get() in
  poly1305_do_core_to_bytes aadlen mlen block;
  let h4 = ST.get () in
  Poly.reveal_ctx_inv ctx h3 h4;

  poly1305_do_core_finish k out ctx block

//#set-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 1"

// Implements the actual poly1305_do operation

val poly1305_do_core:
    k:lbuffer uint8 32ul // key
  -> aadlen:size_t
  -> aad:lbuffer uint8 aadlen // authenticated additional data
  -> mlen:size_t{v mlen + 16 <= max_size_t /\ v aadlen + v mlen / 64 <= max_size_t}
  -> m:lbuffer uint8 mlen // plaintext
  -> out:lbuffer uint8 16ul -> // output: tag
  Stack unit
    (requires fun h ->
      live h k /\ live h aad /\ live h m /\ live h out /\
      disjoint k out)
    (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\
      as_seq h1 out ==
      Spec.poly1305_do (as_seq h0 k) (v mlen) (as_seq h0 m) (v aadlen) (as_seq h0 aad))

let poly1305_do_core k aadlen aad mlen m out =
  push_frame();
  let ctx = create (nlimb M32 +. precomplen M32) (limb_zero M32) in
  let block = create 16ul (u8 0) in
  poly1305_do_core_ k aadlen aad mlen m out ctx block;
  pop_frame()

// Derives the key, and then perform poly1305

val poly1305_do:
    k:lbuffer uint8 32ul
  -> n:lbuffer uint8 12ul
  -> aadlen:size_t
  -> aad:lbuffer uint8 aadlen
  -> mlen:size_t{v mlen + 16 <= max_size_t /\ v aadlen + v mlen / 64 <= max_size_t}
  -> m:lbuffer uint8 mlen
  -> out:lbuffer uint8 16ul ->
  Stack unit
    (requires fun h ->
      live h k /\ live h n /\ live h aad /\ live h m /\ live h out)
    (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
     (let key = Spec.Chacha20.chacha20_key_block0 (as_seq h0 k) (as_seq h0 n) in
      let poly_k = LSeq.sub key 0 32 in
      as_seq h1 out == Spec.poly1305_do poly_k (v mlen) (as_seq h0 m) (v aadlen) (as_seq h0 aad)))
let poly1305_do k n aadlen aad mlen m out =
  push_frame ();
  // Create a new buffer to derive the key
  let tmp = create 64ul (u8 0) in
  derive_key k n tmp;
  // The derived key should only be the first 32 bytes
  let key = sub tmp 0ul 32ul in
  // M32 can be abstracted away for a vectorized AEAD
  poly1305_do_core key aadlen aad mlen m out;
  pop_frame()
