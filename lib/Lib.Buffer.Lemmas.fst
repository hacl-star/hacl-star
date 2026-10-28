module Lib.Buffer.Lemmas

open Lib.IntTypes
open Lib.Buffer

module B = LowStar.Buffer
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let fresh_buffer_disjoint (#a #b:Type0) (h:HS.mem)
  (p:buffer a) (fresh:buffer b) : Lemma
  (requires live #MUT #a h p /\ B.loc_not_in
    (B.loc_addr_of_buffer (fresh <: B.buffer b)) h)
  (ensures disjoint #MUT #MUT #a #b p fresh) =
  let p = p <: B.buffer a in
  let fresh = fresh <: B.buffer b in
  B.live_loc_not_unused_in p h;
  B.unused_in_not_unused_in_disjoint_2
    (B.loc_addr_of_buffer fresh) (B.loc_addr_of_buffer p)
    (B.loc_buffer fresh) (B.loc_buffer p) h;
  B.loc_disjoint_sym (B.loc_buffer fresh) (B.loc_buffer p)

let unused_buffer_disjoint (#a #b:Type0) (h:HS.mem)
  (p:B.buffer a) (fresh:B.buffer b) : Lemma
  (requires B.live h p /\ B.unused_in fresh h)
  (ensures B.disjoint p fresh /\ B.disjoint fresh p) =
  B.unused_in_loc_unused_in fresh h;
  fresh_buffer_disjoint #a #b h p fresh;
  B.loc_disjoint_sym (B.loc_buffer p) (B.loc_buffer fresh)

let buffer_fresh_frame_disjoint (#n:size_t) (h0 h1:HS.mem) (p:lbuffer uint64 n) : Lemma
  (requires live h0 p /\ HS.fresh_frame h0 h1)
  (ensures B.loc_disjoint (loc p)
    (B.loc_region_only false (HS.get_tip h1))) =
  let p = p <: B.buffer uint64 in
  B.live_loc_not_unused_in p h0;
  B.loc_includes_addresses_buffer false (B.frameOf p)
    (FStar.Set.singleton (B.as_addr p)) p;
  B.loc_includes_trans (B.loc_not_unused_in h0)
    (B.loc_addr_of_buffer p) (B.loc_buffer p);
  B.fresh_frame_loc_not_unused_in_disjoint h0 h1;
  B.loc_disjoint_includes_r
    (B.loc_region_only false (HS.get_tip h1))
    (B.loc_not_unused_in h0) (B.loc_buffer p);
  B.loc_disjoint_sym
    (B.loc_region_only false (HS.get_tip h1))
    (B.loc_buffer p)

let buffer_fresh_frame_popped (#n:size_t)
  (h0 h_frame h_body h_final:HS.mem) (p:lbuffer uint64 n) : Lemma
  (requires live h0 p /\ live h_body p /\ HS.fresh_frame h0 h_frame /\
    HS.get_tip h_body == HS.get_tip h_frame /\ HS.popped h_body h_final)
  (ensures live h_final p /\ as_seq h_final p == as_seq h_body p) =
  buffer_fresh_frame_disjoint h0 h_frame p;
  B.modifies_buffer_elim (p <: B.buffer uint64)
    (B.loc_region_only false (HS.get_tip h_frame)) h_body h_final

let inline_stack_inv_trans (h0 h1 h2:HS.mem) : Lemma
  (requires ST.inline_stack_inv h0 h1 /\
    (ST.inline_stack_inv h1 h2 \/ ST.equal_domains h1 h2))
  (ensures ST.inline_stack_inv h0 h2) = ()

let stack_frame_equal_domains (h0 h_alloc h_table h1 h2:HS.mem) : Lemma
  (requires HS.fresh_frame h0 h_alloc /\
    ST.inline_stack_inv h_alloc h_table /\
    ST.equal_domains h_table h1 /\ HS.popped h1 h2)
  (ensures ST.equal_domains h0 h2) = ()
