module Hacl.Streaming.Poly1305_32

module HS = FStar.HyperStack
module B = LowStar.Buffer
module G = FStar.Ghost
module S = FStar.Seq
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module F = Hacl.Streaming.Functor
module I = Hacl.Streaming.Interface
module P = Hacl.Impl.Poly1305
module F32xN = Hacl.Spec.Poly1305.Field32xN
module ST = FStar.HyperStack.ST

open LowStar.BufferOps
open FStar.Mul

/// Opening a bunch of modules for Poly1305
/// =======================================

inline_for_extraction noextract
let uint8 = Lib.IntTypes.uint8

inline_for_extraction noextract
let uint32 = Lib.IntTypes.uint32

open Hacl.Impl.Poly1305.Fields

/// An instance of the stateful type class for poly1305 state
/// =========================================================
///
/// We use a custom view that separates r and acc, to respect abstraction boundaries established by Poly1305.

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

inline_for_extraction noextract
let t = b:B.buffer (limb M32) { B.length b == 25 }

inline_for_extraction noextract
let as_raw (x: t): B.buffer (limb M32) = x

inline_for_extraction noextract
let as_lib (x: t): P.poly1305_ctx M32 =
  assert_norm (Lib.IntTypes.(v (add #U32 (nlimb M32) (precomplen M32))) == 25);
  x

inline_for_extraction noextract
let k = I.stateful_buffer uint8 32ul (Lib.IntTypes.u8 0)

inline_for_extraction noextract
let as_lib_k (x: B.buffer uint8 { B.length x = 32 }): Lib.Buffer.lbuffer uint8 32ul =
  x

inline_for_extraction noextract
let stateful_poly1305_ctx32: I.stateful unit =
  I.Stateful
    (fun () -> t)
    (fun #_ _ s -> B.loc_addr_of_buffer (as_raw s))
    (fun #_ _ s -> B.freeable (as_raw s))
    (fun #_ h s -> B.live h (as_raw s) /\ P.state_inv_t h (as_lib s))
    (fun () -> Spec.Poly1305.felem & Spec.Poly1305.felem)
    (fun () h s -> P.as_get_acc h (as_lib s), P.as_get_r h (as_lib s))
    (fun #_ _ _ -> ())
    (fun #_ l s h0 h1 ->
      P.reveal_ctx_inv (as_lib s) h0 h1;
      B.modifies_buffer_elim (as_raw s) l h0 h1)
    (fun #_ _ _ _ _ -> ())
    (fun () ->
      let h0 = ST.get () in
      let dummy_key = B.alloca (Lib.IntTypes.u8 0) 32ul in
      let r = B.alloca (F32xN.zero 1) 25ul in
      Hacl.Poly1305_32.poly1305_init (as_lib r) (as_lib_k dummy_key);
      let h1 = ST.get () in
      B.modifies_only_not_unused_in B.loc_none h0 h1;
      r)
    (fun () r ->
      let h0 = ST.get () in
      ST.push_frame ();
      let h1 = ST.get () in
      let dummy_key = B.alloca (Lib.IntTypes.u8 0) 32ul in
      let h11 = ST.get () in
      let r = B.malloc r (F32xN.zero 1) 25ul in
      let h12 = ST.get () in
      Hacl.Poly1305_32.poly1305_init (as_lib r) (as_lib_k dummy_key);
      let h2 = ST.get () in
      B.modifies_only_not_unused_in B.loc_none h1 h11;
      B.modifies_only_not_unused_in B.loc_none h11 h12;
      B.modifies_only_not_unused_in B.(loc_buffer r) h12 h12;
      ST.pop_frame ();
      let h3 = ST.get () in
      B.modifies_fresh_frame_popped h0 h1 B.(loc_buffer r) h2 h3;
      B.modifies_only_not_unused_in B.loc_none h0 h3;
      P.reveal_ctx_inv (as_lib r) h2 h3;
      r)
    (fun _ s -> B.free s)
    (fun _ src dst ->
      let h0 = ST.get () in
      B.blit src 0ul dst 0ul 25ul;
      let h1 = ST.get () in
      P.reveal_ctx_inv' (as_lib src) (as_lib dst) h0 h1
    )

/// Interlude for painful spec equivalence proofs
/// =============================================

inline_for_extraction noextract
let block = (block: S.seq uint8 { S.length block = Spec.Poly1305.size_block })

inline_for_extraction noextract
let update_ (acc, r) (block: block) =
  Spec.Poly1305.poly1305_update1 r Spec.Poly1305.size_block block acc, r

inline_for_extraction noextract
let update' r acc (block: block) =
  Spec.Poly1305.poly1305_update1 r Spec.Poly1305.size_block block acc

inline_for_extraction noextract
let update_multi =
  Spec.UpdateMulti.mk_update_multi Spec.Poly1305.size_block update_

inline_for_extraction noextract
let update_multi' r =
  Spec.UpdateMulti.mk_update_multi Spec.Poly1305.size_block (update' r)

#push-options "--fuel 1"
inline_for_extraction noextract
let rec with_or_without_r (acc r: Spec.Poly1305.felem) (blocks: S.seq uint8):
  Lemma
    (requires
      S.length blocks % Spec.Poly1305.size_block = 0)
    (ensures
      update_multi (acc, r) blocks == (update_multi' r acc blocks, r))
    (decreases (S.length blocks))
=
  if S.length blocks = 0 then
    ()
  else
    let block, rem = Spec.UpdateMulti.split_block Spec.Poly1305.size_block blocks 1 in
    let acc = update' r acc block in
    with_or_without_r acc r rem
#pop-options

inline_for_extraction noextract
let update_last (acc, r) (input: S.seq uint8 { S.length input < Spec.Poly1305.size_block }) =
  if S.length input = 0 then
    acc, r
  else
    Spec.Poly1305.poly1305_update1 r (S.length input) input acc, r

inline_for_extraction noextract
let update_last' r acc (input: S.seq uint8 { S.length input < Spec.Poly1305.size_block }) =
  if S.length input = 0 then
    acc
  else
    Spec.Poly1305.poly1305_update1 r (S.length input) input acc

inline_for_extraction noextract
let finish_ k (acc, r) =
  Spec.Poly1305.poly1305_finish k acc

inline_for_extraction noextract
let spec k input =
  Spec.Poly1305.poly1305_mac input k

val update_last_is_update
  (input: S.seq uint8)
  (acc: Spec.Poly1305.felem)
  (r: Spec.Poly1305.felem):
  Lemma
    (requires (S.length input < Spec.Poly1305.size_block))
    (ensures (update_last (acc, r) input == (Spec.Poly1305.poly1305_update input acc r, r)))

let update_last_is_update input acc r =
  let open Hacl.Streaming.Lemmas in
  let block_length = Spec.Poly1305.size_block in
  assert_norm (block_length < pow2 32);
  calc (==) {
    update_last (acc, r) input;
  (==) { }
    update_last' r acc input, r;
  (==) { Spec.UpdateMulti.update_multi_zero Spec.Poly1305.size_block (update' r) acc }
    update_last' r (update_multi' r acc S.empty) input, r;
  (==) { update_full_is_repeat_blocks block_length (update' r) (update_last' r) acc input input }
    Lib.Sequence.repeat_blocks #uint8 #Spec.Poly1305.felem block_length input
      (repeat_f block_length (update' r))
      (repeat_l block_length (update_last' r) input)
      acc, r;
  (==) { repeat_blocks_extensionality block_length input
      (repeat_f block_length (update' r))
      Spec.Poly1305.(poly1305_update1 r size_block)
      (repeat_l block_length (update_last' r) input)
      Spec.Poly1305.(poly1305_update_last r)
      acc
  }
    Lib.Sequence.repeat_blocks #uint8 #Spec.Poly1305.felem block_length input
      Spec.Poly1305.(poly1305_update1 r size_block)
      Spec.Poly1305.(poly1305_update_last r)
      acc, r;
  }

val update_multi_is_update
  (input: S.seq uint8)
  (acc: Spec.Poly1305.felem)
  (r: Spec.Poly1305.felem):
  Lemma
    (requires (S.length input % Spec.Poly1305.size_block = 0))
    (ensures (update_multi (acc, r) input == (Spec.Poly1305.poly1305_update input acc r, r)))

let update_multi_is_update input acc r =
  let open Hacl.Streaming.Lemmas in
  let block_length = Spec.Poly1305.size_block in
  assert_norm (block_length < pow2 32);
  calc (==) {
    update_multi (acc, r) input;
  (==) { with_or_without_r acc r input }
    update_multi' r acc input, r;
  (==) { }
    update_last' r (update_multi' r acc input) S.empty, r;
  (==) { update_full_is_repeat_blocks block_length (update' r) (update_last' r) acc input input }
    Lib.Sequence.repeat_blocks #uint8 #Spec.Poly1305.felem block_length input
      (repeat_f block_length (update' r))
      (repeat_l block_length (update_last' r) input)
      acc, r;
  (==) { repeat_blocks_extensionality block_length input
      (repeat_f block_length (update' r))
      Spec.Poly1305.(poly1305_update1 r size_block)
      (repeat_l block_length (update_last' r) input)
      Spec.Poly1305.(poly1305_update_last r)
      acc
  }
    Lib.Sequence.repeat_blocks #uint8 #Spec.Poly1305.felem block_length input
      Spec.Poly1305.(poly1305_update1 r size_block)
      Spec.Poly1305.(poly1305_update_last r)
      acc, r;
  }

val poly_is_incremental:
  key: S.seq uint8 { S.length key = 32 } ->
  input:S.seq uint8 { S.length input <= pow2 32 - 1 } ->
  Lemma (ensures (
    let open FStar.Mul in
    let block_length = Spec.Poly1305.size_block in
    let n = S.length input / block_length in
    let bs, l = S.split input (n * block_length) in
    FStar.Math.Lemmas.multiple_modulo_lemma n block_length;
    let hash = update_multi (Spec.Poly1305.poly1305_init key) bs in
    let hash = update_last hash l in
    finish_ key hash `S.equal` spec key input))

let poly_is_incremental key input =
  let open Hacl.Streaming.Lemmas in
  let block_length = Spec.Poly1305.size_block in
  assert_norm (block_length < pow2 32);
  let n = S.length input / block_length in
  let bs, l = S.split input (n * block_length) in
  FStar.Math.Lemmas.multiple_modulo_lemma n block_length;
  let acc, r = Spec.Poly1305.poly1305_init key in
  calc (S.equal) {
    finish_ key (update_last (update_multi (acc, r) bs) l);
  (S.equal) { with_or_without_r acc r bs }
    Spec.Poly1305.poly1305_finish key (update_last' r (update_multi' r acc bs) l);
  (S.equal) { update_full_is_repeat_blocks block_length (update' r) (update_last' r) acc input input }
    Spec.Poly1305.poly1305_finish key (Lib.Sequence.repeat_blocks #uint8 #Spec.Poly1305.felem block_length input
      (repeat_f block_length (update' r))
      (repeat_l block_length (update_last' r) input)
      acc);
  (S.equal) { repeat_blocks_extensionality block_length input
      (repeat_f block_length (update' r))
      Spec.Poly1305.(poly1305_update1 r size_block)
      (repeat_l block_length (update_last' r) input)
      Spec.Poly1305.(poly1305_update_last r)
      acc
  }
    Spec.Poly1305.poly1305_finish key (Lib.Sequence.repeat_blocks #uint8 #Spec.Poly1305.felem block_length input
      Spec.Poly1305.(poly1305_update1 r size_block)
      Spec.Poly1305.(poly1305_update_last r)
      acc);
  }

/// The block instance for poly1305!
/// ================================

inline_for_extraction noextract
let poly1305_32: I.block unit =
  I.Block
    I.Runtime

    stateful_poly1305_ctx32
    k

    (fun () -> pow2 32 - 1)
    (fun () -> 16ul)
    (fun () -> 16ul)

    (fun () -> Spec.Poly1305.poly1305_init)
    (fun () x y -> update_multi x y)
    (fun () x _ y -> update_last x y)
    (fun () -> finish_)

    (fun () -> spec)

    (fun () -> Spec.UpdateMulti.update_multi_zero Spec.Poly1305.size_block update_)
    (fun () -> Spec.UpdateMulti.update_multi_associative Spec.Poly1305.size_block update_)
    (fun () -> poly_is_incremental)

    (fun _ _ -> ())
    (fun _ k s -> Hacl.Poly1305_32.poly1305_init s k)
    (fun _ s blocks len ->
      let h0 = ST.get () in
      begin
        let acc, r = P.as_get_acc h0 (as_lib s), P.as_get_r h0 (as_lib s) in
        update_multi_is_update (B.as_seq h0 blocks) acc r
      end;
      Hacl.Poly1305_32.poly1305_update s len blocks
    )
    (fun _ s last total_len ->
      let h0 = ST.get () in
      begin
        let acc, r = P.as_get_acc h0 (as_lib s), P.as_get_r h0 (as_lib s) in
        update_last_is_update (B.as_seq h0 last) acc r
      end;
      let len = FStar.Int.Cast.Full.uint64_to_uint32 (total_len `U64.rem` 16UL) in
      if len <> 0ul then
        Hacl.Poly1305_32.poly1305_update s len last)
    (fun _ k s dst ->
      let h0 = ST.get () in
      ST.push_frame ();
      let h1 = ST.get () in
      let tmp = B.alloca (F32xN.zero 1) 25ul in
      let h2 = ST.get () in
      B.modifies_only_not_unused_in B.loc_none h1 h2;
      B.blit s 0ul tmp 0ul 25ul;
      let h3 = ST.get () in
      B.modifies_only_not_unused_in B.loc_none h1 h3;
      P.reveal_ctx_inv' (as_lib s) (as_lib tmp) h0 h3;
      Hacl.Poly1305_32.poly1305_finish dst k tmp;
      let h4 = ST.get () in
      ST.pop_frame ();
      let h5 = ST.get () in
      B.modifies_only_not_unused_in B.(loc_buffer dst) h1 h4;
      B.modifies_fresh_frame_popped h0 h1 B.(loc_buffer dst) h4 h5;
      assert B.(loc_disjoint (loc_buffer s) (loc_buffer dst));
      P.reveal_ctx_inv (as_lib s) h0 h5
    )

/// The hardest part is done, just the instantiations now
/// =====================================================

let create_in = F.create_in poly1305_32 () t (k.I.s ())
let init = F.init poly1305_32 (G.hide ()) t (k.I.s ())
let update = F.update poly1305_32 (G.hide ()) t (k.I.s ())
let finish = F.mk_finish poly1305_32 () t (k.I.s ())
let free = F.free poly1305_32 (G.hide ()) t (k.I.s ())
