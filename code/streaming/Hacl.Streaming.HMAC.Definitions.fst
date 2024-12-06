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

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

friend Spec.Agile.HMAC
friend Spec.HMAC.Incremental
friend Hacl.HMAC

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
  Hacl.Agile.Hash.init s;
  let i = Hacl.Agile.Hash.impl_of_state (dfst i) s in
  let a = alg_of_impl i in
  (**) let h00 = ST.get () in
  push_frame ();
  (**) let h0 = ST.get () in
  let block = alloca_block i (Lib.IntTypes.u8 0) in

  (**) let h1 = ST.get () in
  (**) assert (B.fresh_loc (B.loc_buffer block) h0 h1);
  let k, k_len = k in
  (**) B.loc_unused_in_not_unused_in_disjoint h0;
  (**) B.loc_unused_in_not_unused_in_disjoint h1;
  (**) B.(modifies_only_not_unused_in loc_none h0 h1);
  wrap_key i block k k_len;
  let ipad = alloca_block i (Lib.IntTypes.u8 0x36) in
  C.Loops.map2 buf ipad block (block_len a) Lib.IntTypes.( (^.) );
  (**) let h2 = ST.get () in
  (**) assert (B.as_seq h2 buf `S.equal` Spec.HMAC.Incremental.init_input a (B.as_seq h0 k));
  pop_frame ();
  (**) let h3 = ST.get () in
  assert (B.modifies (B.loc_buffer buf) h00 h3);
  Hacl.Agile.Hash.frame_invariant (B.loc_buffer buf) s h00 h3;
  ()

let finish (i: G.erased index) k s dst _ =
  (**) Hacl.HMAC.hash_lt_block (alg_of_impl (dfst i));
  (**) assert_norm (pow2 32 < pow2 61);
  (**) assert_norm (pow2 32 < pow2 64);
  (**) assert_norm (pow2 32 < pow2 125);
  let i = Hacl.Agile.Hash.impl_of_state (dfst i) s in
  let a = alg_of_impl i in
  (**) let h00 = ST.get () in
  push_frame ();
  (**) let h0 = ST.get () in
  let k, k_len = k in
  let wrapped_key = alloca_block i (Lib.IntTypes.u8 0) in
  (**) let h01 = ST.get () in
  wrap_key i wrapped_key k k_len;
  (**) let h1 = ST.get () in
  (**) assert (B.fresh_loc (B.loc_buffer wrapped_key) h0 h1);
  (**) B.loc_unused_in_not_unused_in_disjoint h00;
  (**) B.loc_unused_in_not_unused_in_disjoint h0;
  (**) B.loc_unused_in_not_unused_in_disjoint h01;
  (**) B.loc_unused_in_not_unused_in_disjoint h1;
  (**) B.(modifies_only_not_unused_in loc_none h00 h0);
  (**) B.(modifies_only_not_unused_in loc_none h0 h1);
  (**) B.(modifies_only_not_unused_in loc_none h0 h01);
  (**) assert (Hacl.Agile.Hash.footprint s h00 == Hacl.Agile.Hash.footprint s h1);
  (**) assert (B.modifies B.loc_none h0 h01);
  (**) assert (B.length k > 0 ==> B.as_seq h01 k == B.as_seq h00 k);
  (**) assert (B.length k == 0 ==> B.as_seq h01 k `S.equal` B.as_seq h00 k);
  (**) assert (B.length k == 0 ==> B.as_seq h01 k == B.as_seq h00 k);
  (**) assert (B.as_seq h1 wrapped_key == Spec.Agile.HMAC.wrap a (B.as_seq h00 k));

  let opad_and_tmp_hash = alloca_block_and_hash i (Lib.IntTypes.u8 0x5c) in
  let opad = B.sub opad_and_tmp_hash 0ul (block_len a) in
  (**) let h2 = ST.get () in
  (**) assert (B.fresh_loc (B.loc_buffer opad_and_tmp_hash) h1 h2);
  (**) B.loc_unused_in_not_unused_in_disjoint h2;
  (**) B.(modifies_only_not_unused_in loc_none h1 h2);
  (**) assert (Hacl.Agile.Hash.footprint s h00 == Hacl.Agile.Hash.footprint s h2);
  C.Loops.in_place_map2 opad wrapped_key (block_len a) Lib.IntTypes.( (^.) );
  (**) let h20 = ST.get () in
  (**) assert (B.as_seq h20 opad `S.equal` Spec.Agile.HMAC.xor (Lib.IntTypes.u8 0x5c) (Spec.Agile.HMAC.wrap a (B.as_seq h00 k)));

  let tmp_hash = B.sub opad_and_tmp_hash (block_len a) (hash_len a) in
  (**) assert (B.disjoint opad tmp_hash);
  (**) let h3 = ST.get () in
  (**) assert (Hacl.Agile.Hash.footprint s h00 == Hacl.Agile.Hash.footprint s h3);

  (**) assert B.(modifies loc_none h00 h3);
  (**) Hacl.Agile.Hash.frame_invariant B.loc_none s h00 h3;
  Hacl.Agile.Hash.finish s tmp_hash;
  (**) let h4 = ST.get () in
  (**) assert (B.as_seq h4 tmp_hash `S.equal` Spec.Agile.Hash.finish a (Hacl.Agile.Hash.repr s h00) ());
  (**) assert (B.as_seq h4 opad_and_tmp_hash `S.equal` (
    S.append
      (Spec.Agile.HMAC.xor (Lib.IntTypes.u8 0x5c) (Spec.Agile.HMAC.wrap a (B.as_seq h00 k)))
      (Spec.Agile.Hash.finish a (Hacl.Agile.Hash.repr s h00) ())));

  Hacl.Agile.Hash.hash i dst opad_and_tmp_hash (block_len a `FStar.UInt32.add` hash_len a);
  (**) let h5 = ST.get () in
  (**) Hacl.Agile.Hash.frame_invariant B.(loc_buffer dst) s h4 h5;
  (**) assert (Hacl.Agile.Hash.footprint s h00 == Hacl.Agile.Hash.footprint s h5);
  pop_frame ();
  (**) let h6 = ST.get () in
  (**) B.modifies_fresh_frame_popped h00 h0 (B.loc_buffer dst `B.loc_union` Hacl.Agile.Hash.footprint s h00) h5 h6;
  (**) B.popped_modifies h5 h6;
  (**) Hacl.Agile.Hash.frame_invariant (B.loc_region_only false (HS.get_tip h5)) s h5 h6;
  (**) assert (Hacl.Agile.Hash.invariant s h6);
  (**) assert (Hacl.Agile.Hash.footprint s h00 == Hacl.Agile.Hash.footprint s h6);
  (**) assert (ST.equal_stack_domains h00 h6);
  (**) assert (Hacl.Agile.Hash.freeable h00 s ==> Hacl.Agile.Hash.freeable h6 s);
  ()
