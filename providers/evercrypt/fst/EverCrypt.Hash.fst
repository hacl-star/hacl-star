module EverCrypt.Hash

open FStar.HyperStack.ST

module U32  = FStar.UInt32
module HS = FStar.HyperStack
module B = LowStar.Buffer
module M = LowStar.Modifies
module G = FStar.Ghost
module T = LowStar.ToFStarBuffer

module AC = EverCrypt.AutoConfig
module SC = EverCrypt.StaticConfig
module Vale = EverCrypt.Vale
module Hacl = EverCrypt.Hacl
module ValeGlue = EverCrypt.ValeGlue

module ST = FStar.HyperStack.ST
module MP = LowStar.ModifiesPat

open LowStar.BufferOps
open FStar.Integers

let uint32_p = B.buffer uint_32
let uint64_p = B.buffer uint_64

noeq
type state_s: (G.erased alg) -> Type0 =
| SHA256_Hacl: p:uint32_p{ B.length p = U32.v Hacl.SHA2_256.size_state } -> state_s (G.hide SHA256)
| SHA256_Vale: p:uint32_p{ B.length p = U32.v ValeGlue.sha256_size_state } -> state_s (G.hide SHA256)
| SHA384_Hacl: p:uint64_p{ B.length p = U32.v Hacl.SHA2_384.size_state } -> state_s (G.hide SHA384)

let footprint_s #a (s: state_s a): GTot M.loc =
  match s with
  | SHA256_Hacl p -> M.loc_buffer p
  | SHA256_Vale p -> M.loc_buffer p
  | SHA384_Hacl p -> M.loc_buffer p

let invariant_s #a s h =
  match s with
  | SHA256_Hacl p ->
      B.live h p
  | SHA256_Vale p ->
      B.live h p
  | SHA384_Hacl p ->
      B.live h p

let repr #a s h: GTot _ =
  let s = B.get h s 0 in
  match s with
  | SHA256_Hacl p ->
      let p = T.new_to_old_ghost p in
      {
        k = Hacl.SHA2_256.slice_k h p;
        hash = Hacl.SHA2_256.slice_hash h p;
        counter = Hacl.SHA2_256.counter h p
      }
  | SHA256_Vale p ->
      {
        k = ValeGlue.sha256_slice_k h p;
        hash = ValeGlue.sha256_slice_hash h p;
        counter = ValeGlue.sha256_counter h p
      }
  | SHA384_Hacl p ->
      let p = T.new_to_old_ghost p in
      {
        k = Hacl.SHA2_384.slice_k h p;
        hash = Hacl.SHA2_384.slice_hash h p;
        counter = Hacl.SHA2_384.counter h p
      }

let repr_eq (#a:e_alg) (r1 r2: repr_t a) =
  Seq.equal r1.k r2.k /\
  Seq.equal r1.hash r2.hash /\
  r1.counter = r2.counter

let fresh_is_disjoint l1 l2 h0 h1 =
  ()

let frame_invariant #a l s h0 h1 =
  let state = deref h0 s in
  assert (repr_eq (repr s h0) (repr s h1))

let create a =
  let h0 = ST.get () in
  let i = AC.sha256_impl () in
  let s: state_s (G.hide a) =
    match a with
    | SHA256 ->
        if SC.vale && i = AC.Vale then
          let b = B.malloc HS.root 0ul ValeGlue.sha256_size_state in
          SHA256_Vale b
        else
          let b = B.malloc HS.root 0ul Hacl.SHA2_256.size_state in
          SHA256_Hacl b
    | SHA384 ->
        let b = B.malloc HS.root 0UL Hacl.SHA2_384.size_state in
        SHA384_Hacl b
  in
  let h1 = ST.get () in
  let r = B.malloc HS.root s 1ul in
  let h2 = ST.get () in
  // None of these seem to be necessary for the proof to proceed. Key bits are
  // retained.
  assert (invariant r h2);
  assert (fresh_loc (M.loc_buffer r) h1 h2);
  assert (M.(modifies loc_none h0 h1));
  assert (loc_unused_in (M.loc_buffer r) h0);
  assert (M.(modifies loc_none h0 h2));
  r

#set-options "--max_fuel 0"

let init #a s =
  match !*s with
  | SHA256_Hacl p ->
      Hacl.SHA2_256.init (T.new_to_old_st p)
  | SHA384_Hacl p ->
      Hacl.SHA2_384.init (T.new_to_old_st p)
  | SHA256_Vale p ->
      ValeGlue.sha256_init p;
      admit ()

#set-options "--z3rlimit 20"

let update #a s data =
  match !*s with
  | SHA256_Hacl p ->
      assert M.(loc_disjoint (M.loc_buffer data) (M.loc_buffer p));
      let p = T.new_to_old_st p in
      let data = T.new_to_old_st data in
      // JP: in spite of the assertion above, the transition module does not
      // seem to allow me to derive this fact
      assume (FStar.Buffer.disjoint p data);
      Hacl.SHA2_256.update p data
  | SHA384_Hacl p ->
      assert M.(loc_disjoint (M.loc_buffer data) (M.loc_buffer p));
      let p = T.new_to_old_st p in
      let data = T.new_to_old_st data in
      // JP: in spite of the assertion above, the transition module does not
      // seem to allow me to derive this fact
      assume (FStar.Buffer.disjoint p data);
      Hacl.SHA2_384.update p data
  | SHA256_Vale p ->
      ValeGlue.sha256_update p data;
      admit ()

let update_multi #a s data n =
  match !*s with
  | SHA256_Hacl p ->
      assert M.(loc_disjoint (M.loc_buffer data) (M.loc_buffer p));
      let p = T.new_to_old_st p in
      let data = T.new_to_old_st data in
      // JP: in spite of the assertion above, the transition module does not
      // seem to allow me to derive this fact
      assume (FStar.Buffer.disjoint p data);
      Hacl.SHA2_256.update_multi p data n
  | SHA384_Hacl p ->
      assert M.(loc_disjoint (M.loc_buffer data) (M.loc_buffer p));
      let p = T.new_to_old_st p in
      let data = T.new_to_old_st data in
      // JP: in spite of the assertion above, the transition module does not
      // seem to allow me to derive this fact
      assume (FStar.Buffer.disjoint p data);
      Hacl.SHA2_384.update_multi p data n
  | SHA256_Vale p ->
      ValeGlue.sha256_update_multi p data n;
      admit ()

let update_last #a s data len =
  match !*s with
  | SHA256_Hacl p ->
      assert M.(loc_disjoint (M.loc_buffer data) (M.loc_buffer p));
      let p = T.new_to_old_st p in
      let data = T.new_to_old_st data in
      // JP: in spite of the assertion above, the transition module does not
      // seem to allow me to derive this fact
      assume (FStar.Buffer.disjoint p data);
      Hacl.SHA2_256.update_last p data len
  | SHA384_Hacl p ->
      assert M.(loc_disjoint (M.loc_buffer data) (M.loc_buffer p));
      let p = T.new_to_old_st p in
      let data = T.new_to_old_st data in
      // JP: in spite of the assertion above, the transition module does not
      // seem to allow me to derive this fact
      assume (FStar.Buffer.disjoint p data);
      Hacl.SHA2_384.update_last p data len
  | SHA256_Vale p ->
      ValeGlue.sha256_update_last p data len;
      admit ()

let finish #a s dst =
  match !*s with
  | SHA256_Hacl p ->
      assert M.(loc_disjoint (M.loc_buffer dst) (M.loc_buffer p));
      let p = T.new_to_old_st p in
      let dst = T.new_to_old_st dst in
      // JP: in spite of the assertion above, the transition module does not
      // seem to allow me to derive this fact
      assume (FStar.Buffer.disjoint p dst);
      Hacl.SHA2_256.finish p dst
  | SHA384_Hacl p ->
      assert M.(loc_disjoint (M.loc_buffer dst) (M.loc_buffer p));
      let p = T.new_to_old_st p in
      let dst = T.new_to_old_st dst in
      // JP: in spite of the assertion above, the transition module does not
      // seem to allow me to derive this fact
      assume (FStar.Buffer.disjoint p dst);
      Hacl.SHA2_384.finish p dst
  | SHA256_Vale p ->
      ValeGlue.sha256_finish p dst;
      admit ()

let hash a dst input len =
  match a with
  | SHA256 ->
      let i = AC.sha256_impl () in
      if SC.vale && i = AC.Vale then begin
        ValeGlue.sha256_hash dst input len;
        admit ()
      end else begin
        assert M.(loc_disjoint (M.loc_buffer dst) (M.loc_buffer input));
        let input = T.new_to_old_st input in
        let dst = T.new_to_old_st dst in
        assume (FStar.Buffer.disjoint dst input);
        Hacl.SHA2_256.hash dst input len
      end
  | SHA384 ->
      assert M.(loc_disjoint (M.loc_buffer dst) (M.loc_buffer input));
      let input = T.new_to_old_st input in
      let dst = T.new_to_old_st dst in
      assume (FStar.Buffer.disjoint dst input);
      Hacl.SHA2_384.hash dst input len
