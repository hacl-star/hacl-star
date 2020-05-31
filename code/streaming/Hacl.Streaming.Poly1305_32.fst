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
      let r = B.alloca (F32xN.zero 1) 25ul in
      let h1 = ST.get () in
      P.ctx_inv_zeros #M32 r h1;
      r)
    (fun () r ->
      let r = B.malloc r (F32xN.zero 1) 25ul in
      let h1 = ST.get () in
      P.ctx_inv_zeros #M32 r h1;
      r)
    (fun _ s -> B.free s)
    (fun _ src dst ->
      let h0 = ST.get () in
      B.blit src 0ul dst 0ul 25ul;
      let h1 = ST.get () in
      P.reveal_ctx_inv' (as_lib src) (as_lib dst) h0 h1
    )

/// Interlude for spec equivalence proofs
/// =====================================
///
/// A quick explanation about this proof of equivalence. At the spec level,
/// ``poly1305_update`` needs both ``r`` and the accumulator ``acc``. This thus
/// makes poly1305 update a function of two arguments. However, the streaming
/// facility is constructed over specifications that take one single argument.
/// Not a problem! We carry the pair ``(r, acc)`` as our "streaming functor
/// accumulator", and we now have to show that a specification in terms of
/// ``update (update (r, acc) init)`` is the same as poly1305. For that, we need
/// to do a little proof of equivalence to show first that this is the same as
/// ``(update r) ((update r) acc)`` (note that the update function now becomes a
/// partial application), then use the update-multi-repeat conversion lemma to
/// get the original specification of poly1305.

inline_for_extraction noextract
let block = (block: S.seq uint8 { S.length block = Spec.Poly1305.size_block })

inline_for_extraction noextract
let update_ (acc, r) (block: block) =
  Spec.Poly1305.poly1305_update1 r Spec.Poly1305.size_block block acc, r

/// Same as [update_], but with the input not necessarily a block (can be smaller)
inline_for_extraction noextract
let update__ (acc, r) (input: S.seq uint8{S.length input <= Spec.Poly1305.size_block}) =
  Spec.Poly1305.poly1305_update1 r Spec.Poly1305.size_block input acc, r

inline_for_extraction noextract
let update' r acc (block: block) =
  Spec.Poly1305.poly1305_update1 r Spec.Poly1305.size_block block acc

inline_for_extraction noextract
let update_multi =
  Lib.UpdateMulti.mk_update_multi Spec.Poly1305.size_block update_

inline_for_extraction noextract
let update_multi' r =
  Lib.UpdateMulti.mk_update_multi Spec.Poly1305.size_block (update' r)

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
    let block, rem = Lib.UpdateMulti.split_block Spec.Poly1305.size_block blocks 1 in
    let acc = update' r acc block in
    with_or_without_r acc r rem
#pop-options

inline_for_extraction noextract
let update_last (acc, r) (input: S.seq uint8 { S.length input <= Spec.Poly1305.size_block }) =
  if S.length input = 0 then
    acc, r
  else
    Spec.Poly1305.poly1305_update1 r (S.length input) input acc, r

inline_for_extraction noextract
let update_last' r acc (input: S.seq uint8 { S.length input <= Spec.Poly1305.size_block }) =
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

val update_last_not_block_is_update
  (input: S.seq uint8)
  (acc: Spec.Poly1305.felem)
  (r: Spec.Poly1305.felem):
  Lemma
    (requires (S.length input < Spec.Poly1305.size_block))
    (ensures (update_last (acc, r) input == (Spec.Poly1305.poly1305_update input acc r, r)))

let update_last_not_block_is_update input acc r =
  let open Lib.UpdateMulti.Lemmas in
  let block_length = Spec.Poly1305.size_block in
  assert_norm (block_length < pow2 32);
  calc (==) {
    update_last (acc, r) input;
  (==) { }
    update_last' r acc input, r;
  (==) { Lib.UpdateMulti.update_multi_zero Spec.Poly1305.size_block (update' r) acc }
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

val update_last_block_is_update
  (input: S.seq uint8)
  (acc: Spec.Poly1305.felem)
  (r: Spec.Poly1305.felem):
  Lemma
    (requires (S.length input = Spec.Poly1305.size_block))
    (ensures (update_last (acc, r) input == (Spec.Poly1305.poly1305_update input acc r, r)))

#push-options "--fuel 1"
let update_last_block_is_update input acc r =
  let open Lib.UpdateMulti.Lemmas in
  let block_length = Spec.Poly1305.size_block in
  assert_norm (block_length < pow2 32);
  assert(input `S.equal` S.append input S.empty);
  let acc1 = update' r acc input in
  let acc1' = update_multi' r acc input in
  assert(
    let block, rem = Lib.UpdateMulti.split_block block_length input 1 in
    block `S.equal` input /\ rem `S.equal` S.empty);
  assert(
    Lib.UpdateMulti.mk_update_multi block_length (update' r) acc1 S.empty ==
    acc1');
  assert(acc1 == acc1');
  calc (==) {
    update_last (acc, r) input;
  (==) { }
    update_last' r acc input, r;
  (==) { }
    update_last' r (update' r acc input) S.empty, r;
  (==) {  }
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
#pop-options

val update_last_is_update
  (input: S.seq uint8)
  (acc: Spec.Poly1305.felem)
  (r: Spec.Poly1305.felem):
  Lemma
    (requires (S.length input <= Spec.Poly1305.size_block))
    (ensures (update_last (acc, r) input == (Spec.Poly1305.poly1305_update input acc r, r)))

let update_last_is_update input acc r =
  if S.length input = Spec.Poly1305.size_block
  then update_last_block_is_update input acc r
  else update_last_not_block_is_update input acc r

val update_multi_is_update
  (input: S.seq uint8)
  (acc: Spec.Poly1305.felem)
  (r: Spec.Poly1305.felem):
  Lemma
    (requires (S.length input % Spec.Poly1305.size_block = 0))
    (ensures (update_multi (acc, r) input == (Spec.Poly1305.poly1305_update input acc r, r)))

let update_multi_is_update input acc r =
  let open Lib.UpdateMulti.Lemmas in
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
    let hash = Lib.UpdateMulti.update_full Spec.Poly1305.size_block update_ update_last (Spec.Poly1305.poly1305_init key) input in
    finish_ key hash `S.equal` spec key input))

let poly_is_incremental key input =
  let open Lib.UpdateMulti.Lemmas in
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
  (S.equal) { update_full_is_repeat_blocks block_length (update' r) (update_last' r)
              acc input input }
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

/// Same lemma as above, but we take into account the fact that the hash stream
/// processes the buffer lazily.
val poly_is_incremental_lazy:
  key: S.seq uint8 { S.length key = 32 } ->
  input:S.seq uint8 { S.length input <= pow2 32 - 1 } ->
  Lemma (ensures (
    let hash = Lib.UpdateMulti.update_full_lazy Spec.Poly1305.size_block update_ update_last (Spec.Poly1305.poly1305_init key) input in
    finish_ key hash `S.equal` spec key input))

#push-options "--fuel 1"
let poly_is_incremental_lazy key input =
  let open Lib.UpdateMulti.Lemmas in
  let block_length = Spec.Poly1305.size_block in
  assert_norm (block_length < pow2 32);
  let n = S.length input / block_length in
  let rem = S.length input % block_length in
  let n', rem' = if rem = 0 && n > 0 then n - 1, block_length else n, rem in (**)
  let bs, l = S.split input (n' * block_length) in
  let acc, r = Spec.Poly1305.poly1305_init key in
  let acc1 = update_multi (acc, r) bs in
  let acc_f = update_last acc1 l in
  if rem = 0 && n > 0 then
    begin
    assert(acc_f == update__ acc1 l);
    assert(
      let block, rem = Lib.UpdateMulti.split_block Spec.Poly1305.size_block l 1 in
      block `S.equal` l /\ rem `S.equal` S.empty);
    let acc2 = update__ acc1 l in
    assert_norm(Lib.UpdateMulti.mk_update_multi Spec.Poly1305.size_block update_ acc2 S.empty
           == acc2);
    assert(acc_f == update_multi acc1 l);
    Lib.UpdateMulti.update_multi_associative Spec.Poly1305.size_block update_ (acc, r) bs l;
    assert(input `S.equal` S.append bs l);
    assert(acc_f = update_multi (acc, r) input);
    assert(update_last acc_f S.empty == acc_f);
    assert(input `S.equal` S.append input S.empty);
    poly_is_incremental key input
    end
  else poly_is_incremental key input
#pop-options

/// The block instance for poly1305!
/// ================================

#push-options "--z3rlimit 300"
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

    (fun () -> Lib.UpdateMulti.update_multi_zero Spec.Poly1305.size_block update_)
    (fun () -> Lib.UpdateMulti.update_multi_associative Spec.Poly1305.size_block update_)
    (fun () -> poly_is_incremental_lazy)

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
    (fun _ s last len total_len ->
      let h0 = ST.get () in
      begin
        let acc, r = P.as_get_acc h0 (as_lib s), P.as_get_r h0 (as_lib s) in
        update_last_is_update (B.as_seq h0 last) acc r
      end;
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
#pop-options

/// The hardest part is done, just the instantiations now
/// =====================================================

let create_in = F.create_in poly1305_32 () t (k.I.s ())
let init = F.init poly1305_32 (G.hide ()) t (k.I.s ())
let update = F.update poly1305_32 (G.hide ()) t (k.I.s ())
let finish = F.mk_finish poly1305_32 () t (k.I.s ())
let free = F.free poly1305_32 (G.hide ()) t (k.I.s ())
