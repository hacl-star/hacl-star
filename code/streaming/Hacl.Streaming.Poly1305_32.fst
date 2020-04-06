module Hacl.Streaming.Poly1305_32

module HS = FStar.HyperStack
module B = LowStar.Buffer
module G = FStar.Ghost
module S = FStar.Seq
module U32 = FStar.UInt32
module U64 = FStar.UInt64
//module F = Hacl.Streaming.Functor
module I = Hacl.Streaming.Interface
module P = Hacl.Impl.Poly1305
module F32xN = Hacl.Spec.Poly1305.Field32xN
module ST = FStar.HyperStack.ST

open LowStar.BufferOps
open FStar.Mul

/// Opening a bunch of modules for Poly1305

inline_for_extraction noextract
let uint8 = Lib.IntTypes.uint8

inline_for_extraction noextract
let uint32 = Lib.IntTypes.uint32

open Hacl.Impl.Poly1305.Fields

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

let update (acc, r) (block: S.seq uint8 { S.length block = Spec.Poly1305.size_block }) =
  Spec.Poly1305.poly1305_update1 r Spec.Poly1305.size_block block acc, r

inline_for_extraction noextract
let k = I.stateful_buffer uint8 32

inline_for_extraction noextract
let as_lib_k (x: B.buffer uint8 { B.length x = 32 }): Lib.Buffer.lbuffer uint8 32ul =
  x

inline_for_extraction noextract
let poly1305_32: I.block unit =
  I.Block
    I.Runtime

    stateful_poly1305_ctx32
    k

    (fun () -> pow2 32 - 1)
    (fun () -> 16ul)
    (fun () -> 16ul)

    (fun () k -> Spec.Poly1305.poly1305_init k)
    (fun () acc blocks -> Spec.UpdateMulti.mk_update_multi Spec.Poly1305.size_block update acc blocks)
    (fun () (acc, r) _ input -> Spec.Poly1305.poly1305_update1 r (S.length input) input acc, r)
    (fun () k (acc, r) -> Spec.Poly1305.poly1305_finish k acc)

    (fun () k input -> Spec.Poly1305.poly1305_mac input k)

    (fun () -> Spec.UpdateMulti.update_multi_zero Spec.Poly1305.size_block update)
    (fun () -> Spec.UpdateMulti.update_multi_associative Spec.Poly1305.size_block update)
    (fun () _ _ -> admit ())

    (fun _ _ -> ())
    (fun () ->
      let h0 = ST.get () in
      let dummy_key = B.alloca (Lib.IntTypes.u8 0) 32ul in
      let r = B.alloca (F32xN.zero 1) 25ul in
      P.poly1305_init #M32 (as_lib r) (as_lib_k dummy_key);
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
      P.poly1305_init #M32 (as_lib r) (as_lib_k dummy_key);
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
    (fun _ k s -> P.poly1305_init #M32 s k)
    (fun _ s blocks len -> P.poly1305_update #M32 s len blocks; admit ())
    (fun _ s last total_len ->
      admit ();
      let len = FStar.Int.Cast.Full.uint64_to_uint32 (total_len `U64.rem` 16UL) in
      P.poly1305_update #M32 s len last)
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
      P.poly1305_finish #M32 dst k tmp;
      let h4 = ST.get () in
      ST.pop_frame ();
      let h5 = ST.get () in
      B.modifies_only_not_unused_in B.(loc_buffer dst) h1 h4;
      B.modifies_fresh_frame_popped h0 h1 B.(loc_buffer dst) h4 h5;
      assert B.(loc_disjoint (loc_buffer s) (loc_buffer dst));
      P.reveal_ctx_inv (as_lib s) h0 h5
    )
    (fun _ s -> B.free s)
    (fun _ src dst ->
      let h0 = ST.get () in
      B.blit src 0ul dst 0ul 25ul;
      let h1 = ST.get () in
      P.reveal_ctx_inv' (as_lib src) (as_lib dst) h0 h1
    )

// Make sure SHA256 update last works
// Update functor to deal with key
// Do proof of spec equivalence lemma
