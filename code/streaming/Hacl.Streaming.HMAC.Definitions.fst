module Hacl.Streaming.HMAC.Definitions

/// Helper definitions with an interface so as to friend Spec.Agile.HMAC

open FStar.HyperStack.ST
open LowStar.BufferOps

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module B = LowStar.Buffer
module M = LowStar.Modifies
module G = FStar.Ghost
module S = FStar.Seq
module D = Hacl.Hash.Definitions

open Hacl.Agile.Hash
open Hacl.Streaming.Interface

let _sync_decl = ()

friend Spec.Agile.HMAC
friend Spec.HMAC.Incremental
friend Hacl.HMAC

#set-options "--fuel 0 --ifuel 0 --z3rlimit 400"

noextract inline_for_extraction
val alloca_block (#a: Type0) (i: G.erased impl) (init: a):
  ST.StackInline (B.buffer a)
    (requires (fun h ->
      HS.is_stack_region (HS.get_tip h)))
    (ensures (fun h0 s h1 ->
      M.(modifies M.loc_none h0 h1) /\
      B.frameOf s == HS.get_tip h0 /\
      B.length s == Spec.Agile.Hash.block_length (alg_of_impl i) /\
      B.as_seq h1 s == Seq.create (Spec.Agile.Hash.block_length (alg_of_impl i)) init /\
      B.live h1 s /\
      B.fresh_loc (M.loc_buffer s) h0 h1))

// This extracts in C without a VLA.
let alloca_block i init =
  let b = B.alloca init 168ul in
  assert (D.block_len (alg_of_impl i) `FStar.UInt32.lte` 168ul);
  let r = B.sub b 0ul (block_len (alg_of_impl i)) in
  let h = ST.get () in
  assert (B.as_seq h r `S.equal` S.create (Spec.Agile.Hash.block_length (alg_of_impl i)) init);
  r

noextract inline_for_extraction
val alloca_block_and_hash (#a: Type0) (i: G.erased impl) (init: a):
  ST.StackInline (B.buffer a)
    (requires (fun h ->
      HS.is_stack_region (HS.get_tip h)))
    (ensures (fun h0 s h1 ->
      let l = Spec.Agile.Hash.block_length (alg_of_impl i) + Spec.Agile.Hash.hash_length (alg_of_impl i) in
      M.(modifies M.loc_none h0 h1) /\
      B.frameOf s == HS.get_tip h0 /\
      B.length s == l /\
      B.as_seq h1 s == Seq.create l init /\
      B.live h1 s /\
      B.fresh_loc (M.loc_buffer s) h0 h1))

// This extracts in C without a VLA.
let alloca_block_and_hash i init =
  let b = B.alloca init (168ul `FStar.UInt32.add` 64ul) in
  assert (D.block_len (alg_of_impl i) `FStar.UInt32.lte` 168ul);
  assert (D.hash_len (alg_of_impl i) `FStar.UInt32.lte` 64ul);
  let r = B.sub b 0ul (block_len (alg_of_impl i) `FStar.UInt32.add` hash_len (alg_of_impl i)) in
  let h = ST.get () in
  assert (B.as_seq h r `S.equal` S.create (Spec.Agile.Hash.block_length (alg_of_impl i) + Spec.Agile.Hash.hash_length (alg_of_impl i)) init);
  r

// TODO: copy-paste from Hacl.HMAC, but can deal with NULL keys
inline_for_extraction noextract
let wrap_key_st (a: Spec.Agile.Hash.fixed_len_alg) =
  output: B.buffer uint8 { B.length output == Spec.Agile.Hash.block_length a } ->
  key: B.buffer uint8 {B.length key `Spec.Agile.Hash.less_than_max_input_length` a} ->
  len: UInt32.t {UInt32.v len = B.length key} ->
  Stack unit
    (requires fun h0 ->
      (B.length key > 0 ==>  B.live h0 key /\ B.disjoint output key) /\
      B.live h0 output /\
      B.as_seq h0 output == Seq.create (Spec.Agile.Hash.block_length a) (Lib.IntTypes.u8 0))
    (ensures fun h0 _ h1 ->
      B.(modifies (loc_buffer output) h0 h1) /\
      B.as_seq h1 output == Spec.Agile.HMAC.wrap a (B.as_seq h0 key))

// TODO: copy-paste from Hacl.HMAC, but does not rely on inline_for_extraction helpers (which generates poor code)
inline_for_extraction
let helper_smtpat (a: Spec.Agile.Hash.fixed_len_alg) (len: UInt32.t{ UInt32.v len `Spec.Agile.Hash.less_than_max_input_length` a }):
  x:UInt32.t { x `FStar.UInt32.lte` D.block_len a } =
  if len `FStar.UInt32.lte` block_len a then len else hash_len a

// TODO: copy-paste from Hacl.HMAC, but calling impl-agile hash
let wrap_key (impl: impl): wrap_key_st (alg_of_impl impl) =
fun output key len ->
  [@inline_let]
  let a = alg_of_impl impl in
  [@inline_let] //18-08-02 does *not* prevents unused-but-set-variable warning in C
  let i = helper_smtpat a len in
  let nkey = B.sub output 0ul i in
  let zeroes = B.sub output i (block_len a `FStar.UInt32.sub` i) in
  (**) assert B.(loc_disjoint (loc_buffer nkey) (loc_buffer zeroes));
  (**) let h0 = ST.get () in
  (**) assert (Seq.equal (B.as_seq h0 zeroes) (Seq.create (UInt32.v (D.block_len a `FStar.UInt32.sub` i)) (Lib.IntTypes.u8 0)));
  if len `FStar.UInt32.lte` block_len a then begin
    if len `FStar.UInt32.gt` 0ul then
      B.blit key 0ul nkey 0ul len;
    let h1 = ST.get () in
    (**) assert (Seq.equal (B.as_seq h1 zeroes) (B.as_seq h0 zeroes));
    (**) assert (Seq.equal (B.as_seq h1 nkey) (B.as_seq h0 key));
    (**) assert (Seq.equal (B.as_seq h1 output) (S.append (B.as_seq h1 nkey) (B.as_seq h1 zeroes)));
    (**) Seq.lemma_eq_elim (B.as_seq h1 output) (S.append (B.as_seq h1 nkey) (B.as_seq h1 zeroes));
    (**) assert (B.as_seq h1 output == Spec.Agile.HMAC.wrap a (B.as_seq h0 key))
  end else begin
    Hacl.Agile.Hash.hash impl nkey key len;
    (**) let h1 = ST.get () in
    (**) assert (Seq.equal (B.as_seq h1 zeroes) (B.as_seq h0 zeroes));
    (**) assert (Seq.equal (B.as_seq h1 nkey) (Spec.Agile.Hash.hash a (B.as_seq h0 key)));
    (**) assert (Seq.equal (B.as_seq h1 output) (S.append (B.as_seq h1 nkey) (B.as_seq h1 zeroes)));
    (**) Seq.lemma_eq_elim (B.as_seq h1 output) (S.append (B.as_seq h1 nkey) (B.as_seq h1 zeroes));
    (**) assert (B.as_seq h1 output == Spec.Agile.HMAC.wrap a (B.as_seq h0 key))
  end

let init (i: G.erased index) k buf s =
  (**) assert_norm (pow2 32 < pow2 61);
  (**) assert_norm (pow2 32 < pow2 64);
  (**) assert_norm (pow2 32 < pow2 125);
  let s1, s2 = s in
  (**) let h000 = ST.get () in
  Hacl.Agile.Hash.init s1;
  (**) let h001 = ST.get () in
  (**) Hacl.Agile.Hash.(frame_invariant (footprint s1 h000) s2 h000 h001);
  Hacl.Agile.Hash.init s2;
  (**) let h002 = ST.get () in
  (**) Hacl.Agile.Hash.(frame_invariant (footprint s2 h001) s1 h001 h002);
  (**) assert Hacl.Agile.Hash.(invariant s1 h002);
  (**) assert Hacl.Agile.Hash.(invariant s2 h002);
  let i = Hacl.Agile.Hash.impl_of_state (dfst i) s1 in
  let a = alg_of_impl i in
  (**) let h00 = ST.get () in
  (**) assert Hacl.Agile.Hash.(invariant s1 h00);
  (**) assert Hacl.Agile.Hash.(invariant s2 h00);
  let k0 = k in
  let k, k_len = k in
  (**) assert (B.as_seq h000 k `S.equal` B.as_seq h00 k);
  push_frame ();
  (**) let h0 = ST.get () in
  (**) assert (B.as_seq h000 k `S.equal` B.as_seq h0 k);
  (**) assert Hacl.Agile.Hash.(footprint s2 h000 == footprint s2 h0);
  (**) assert Hacl.Agile.Hash.(footprint s2 h00 == footprint s2 h0);
  // (**) Hacl.Agile.Hash.frame_invariant (B.loc_region_only false (HS.get_tip h0)) s1 h00 h0;
  (**) Hacl.Agile.Hash.frame_invariant (B.loc_region_only false (HS.get_tip h0)) s2 h00 h0;
  // (**) assert Hacl.Agile.Hash.(invariant s1 h0);
  (**) assert Hacl.Agile.Hash.(invariant s2 h0);
  let block = alloca_block i (Lib.IntTypes.u8 0) in

  (**) let h1 = ST.get () in
  (**) assert (B.fresh_loc (B.loc_buffer block) h0 h1);
  // (**) B.loc_unused_in_not_unused_in_disjoint h0;
  // (**) B.loc_unused_in_not_unused_in_disjoint h1;
  // (**) B.(modifies_only_not_unused_in loc_none h0 h1);
  wrap_key i block k k_len;
  (**) let h10 = ST.get () in
  let ipad = alloca_block i (Lib.IntTypes.u8 0x36) in
  let h11 = ST.get () in
  let opad = alloca_block i (Lib.IntTypes.u8 0x5c) in
  let h12 = ST.get () in
  (**) assert (B.fresh_loc (B.loc_buffer ipad) h1 h11);
  (**) assert (B.fresh_loc (B.loc_buffer opad) h11 h12);
  (**) B.loc_unused_in_not_unused_in_disjoint h0;
  (**) B.loc_unused_in_not_unused_in_disjoint h1;
  (**) B.loc_unused_in_not_unused_in_disjoint h10;
  (**) B.loc_unused_in_not_unused_in_disjoint h11;
  (**) B.loc_unused_in_not_unused_in_disjoint h12;
  (**) B.(modifies_only_not_unused_in loc_none h10 h12);
  (**) assert B.(loc_disjoint (loc_buffer opad) (loc_buffer ipad));
  (**) assert (B.as_seq h12 block `S.equal` (Spec.Agile.HMAC.wrap a (B.as_seq h000 k)));
  C.Loops.map2 buf ipad block (block_len a) Lib.IntTypes.( (^.) );
  (**) let h13 = ST.get () in
  (**) assert (B.as_seq h13 buf `S.equal` Spec.HMAC.Incremental.init_input a (B.as_seq h0 k));
  C.Loops.in_place_map2 opad block (block_len a) Lib.IntTypes.( (^.) );
  (**) let h2 = ST.get () in
  (**) assert (B.as_seq h2 buf `S.equal` Spec.HMAC.Incremental.init_input a (B.as_seq h0 k));
  (**) assert (B.as_seq h2 opad `S.equal` (
    let k = Spec.Agile.HMAC.wrap a (B.as_seq h000 k) in
    Spec.Agile.HMAC.xor (Lib.IntTypes.u8 0x5c) k));
  (**) (B.modifies_only_not_unused_in (B.loc_buffer buf) h0 h2);
  // (**) Hacl.Agile.Hash.(frame_invariant (B.loc_buffer buf) s1 h0 h2);
  (**) Hacl.Agile.Hash.(frame_invariant (B.loc_buffer buf) s2 h0 h2);
  (**) assert (Hacl.Agile.Hash.repr s2 h2 `S.equal` Spec.Agile.Hash.init a);
  Hacl.Agile.Hash.update_multi s2 0UL opad (block_len a);
  (**) let h20 = ST.get () in
  (**) assert (Hacl.Agile.Hash.repr s2 h20 `S.equal` (
    let k = Spec.Agile.HMAC.wrap a (B.as_seq h000 k) in
    let opad = Spec.Agile.HMAC.xor (Lib.IntTypes.u8 0x5c) k in
    Spec.Agile.Hash.(update_multi a (init a) (init_extra_state a) opad)));
  (**) assert B.(modifies (Hacl.Agile.Hash.footprint s2 h0) h2 h20);
  (**) assert (B.as_seq h20 buf `S.equal` Spec.HMAC.Incremental.init_input a (B.as_seq h000 k));
  (**) B.modifies_trans (B.loc_buffer buf) h0 h2 (Hacl.Agile.Hash.footprint s2 h0) h20;
  pop_frame ();
  (**) let h3 = ST.get () in
  (**) B.modifies_fresh_frame_popped h00 h0 (B.loc_buffer buf `B.loc_union` Hacl.Agile.Hash.footprint s2 h00) h20 h3;
  (**) B.popped_modifies h20 h3;
  (**) assert (B.modifies (B.loc_buffer buf `B.loc_union` (Hacl.Agile.Hash.footprint s2 h00)) h00 h3);
  (**) B.modifies_loc_includes (B.loc_buffer buf `B.loc_union` (two_footprint h00 s)) h00 h3
    (B.loc_buffer buf `B.loc_union` (Hacl.Agile.Hash.footprint s2 h00));
  (**) B.modifies_trans (two_footprint h000 s) h000 h00 (B.loc_buffer buf `B.loc_union` (two_footprint h00 s)) h3;
  (**) Hacl.Agile.Hash.frame_invariant (B.loc_buffer buf `B.loc_union` Hacl.Agile.Hash.footprint s2 h00) s1 h00 h3;
  (**) assert (Hacl.Agile.Hash.repr s1 h3 `S.equal` Spec.Agile.Hash.init a);
  (**) Hacl.Agile.Hash.frame_invariant (B.loc_region_only false (HS.get_tip h20)) s2 h20 h3;
  (**) assert (Hacl.Agile.Hash.repr s2 h3 `S.equal` (
    let k = Spec.Agile.HMAC.wrap a (B.as_seq h000 k) in
    let opad = Spec.Agile.HMAC.xor (Lib.IntTypes.u8 0x5c) k in
    Spec.Agile.Hash.(update_multi a (init a) (init_extra_state a) opad)));
  (**) frame_invariant (B.loc_buffer buf `B.loc_union` Hacl.Agile.Hash.footprint s2 h00) k0 h00 h3;
  ()

let finish (i: G.erased index) k s dst _ =
  (**) Hacl.HMAC.hash_lt_block (alg_of_impl (dfst i));
  (**) assert_norm (pow2 32 < pow2 61);
  (**) assert_norm (pow2 32 < pow2 64);
  (**) assert_norm (pow2 32 < pow2 125);
  let s1, s2 = s in
  let i = Hacl.Agile.Hash.impl_of_state (dfst i) s1 in
  let a = alg_of_impl i in
  (**) let h0 = ST.get () in
  Hacl.Agile.Hash.finish s1 dst;
  (**) let h1 = ST.get () in
  (**) Hacl.Agile.Hash.(frame_invariant (B.loc_buffer dst `B.loc_union` footprint s1 h0) s2 h0 h1);
  Hacl.Agile.Hash.update_last s2 (FStar.Int.Cast.Full.uint32_to_uint64 (block_len a)) dst (hash_len a);
  (**) let h2 = ST.get () in
  (**) Hacl.Agile.Hash.(frame_invariant (footprint s2 h0) s1 h1 h2);
  Hacl.Agile.Hash.finish s2 dst;
  (**) let h3 = ST.get () in
  (**) Hacl.Agile.Hash.(frame_invariant (B.loc_buffer dst `B.loc_union` footprint s2 h0) s1 h2 h3)
