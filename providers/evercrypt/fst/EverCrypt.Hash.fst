module EverCrypt.Hash

/// ----------agile implementation of hash specification ------------
/// must be in scope for linking the agile spec to the ad hoc algorithmic specs

let string_of_alg = function
  | MD5    -> "MD5"
  | SHA1   -> "SHA1"
  | SHA224 -> "SHA224"
  | SHA256 -> "SHA256"
  | SHA384 -> "SHA384"
  | SHA512 -> "SHA512"


let type_of a =
  match Ghost.reveal a with
  | MD5 | SHA1 | SHA224 | SHA256 -> UInt32.t // uint_32
  | SHA384 | SHA512              -> UInt64.t // uint_64

let size_of_k a: GTot nat =
  match Ghost.reveal a with
  | SHA256 -> 64
  | SHA384 -> 80
  | _      -> admit()

type acc (a: e_alg) = {
  k: Seq.lseq (type_of a) (size_of_k a);
  hash: Seq.lseq (type_of a) 8;
  counter: nat;
}

let acc0 #a =
  match Ghost.reveal a with
  | SHA256 -> {
      hash = EverCrypt.Spec.SHA2_256.h_0;
      k = EverCrypt.Spec.SHA2_256.k;
      counter = 0
    }
  | SHA384 -> {
      hash = EverCrypt.Spec.SHA2_384.h_0;
      k = EverCrypt.Spec.SHA2_384.k;
      counter = 0
    }
  | _ -> admit()

// 18-07-06 We need a fully-specified refinement: the hacl* spec
// should state that the counter is incremented by 1 and that the K
// constant is unchanged---a total spec would also save the need for
// stateful invariants.
//
// Besides, all of that could be avoided if the state was just the
// intermediate hash.

let compress #a st b = 
  match Ghost.reveal a with 
  | SHA256 -> 
     { k       = EverCrypt.Spec.SHA2_256.k; 
       hash    = EverCrypt.Spec.SHA2_256.update st.hash b;
       counter = st.counter + 1 } 
  | SHA384 -> 
     { k       = EverCrypt.Spec.SHA2_384.k; 
       hash    = EverCrypt.Spec.SHA2_384.update st.hash b;
       counter = st.counter + 1 } 
  | _ -> 
    admit()
  
(* was, partial:
let update_spec (#a:e_alg)
  (s:state a)
  (h0: HS.mem{invariant s h0})
  (h1: HS.mem{invariant s h1})
  (data: bytes{Seq.length data = block_size a}):
  GTot _
=
  let r0 = repr s h0 in
  let r1 = repr s h1 in
  match G.reveal a with
  | SHA256 -> r1.hash = EverCrypt.Spec.SHA2_256.update r0.hash data
  | SHA384 -> r1.hash = EverCrypt.Spec.SHA2_384.update r0.hash data
*)

// 18-07-06 hacl* defines finish on the raw buffer contents, so
// we'd need to define repr first.
let extract #a st = admit()
(*
  match Ghost.reveal a with 
  | SHA256 -> repr Spec.SHA2_256.finish st 
  | SHA384 -> Spec.SHA2_384.finish st 
  | _ -> admit()
*)

// 18-07-06 should be provable, despite the two specs having different
// structures.
let suffix a l = admit()
(*
  let l1 = l % blockLength a in 
  let l0 = l - l1 in
  match Ghost.reveal a with
  | SHA256 -> 
      assume(l0 % blockLength a == 0);
      assume(l < Spec.SHA2_256.max_input_len_8); 
      let pad = Spec.SHA2_256.pad l0 l1 in
      assume(Seq.length pad = suffixLength a l);
      pad
  | _ -> admit()
//| SHA384 -> Spec.SHA2_384.pad l0 l1 
//| SHA512 -> Spec.SHA2_512.pad l0 l1
*)


(*
  match G.reveal a with
  | SHA256 ->
      r1.hash = EverCrypt.Spec.SHA2_256.update r0.hash data
  | SHA384 ->
      r1.hash = EverCrypt.Spec.SHA2_384.update r0.hash data

// from update_multi_spec: 
  match G.reveal a with
  | SHA256 ->
      r1.hash = EverCrypt.Spec.SHA2_256.update_multi r0.hash data
  | SHA384 ->
      r1.hash = EverCrypt.Spec.SHA2_384.update_multi r0.hash data
*)

/// 18-04-07 postponing verified integration with HACL* for now. We
/// provide below a concise definition of the Merkle-Damgard
/// construction. The plan is to integrate it with Benjamin's
/// algorithmic specifications. At that point, we will probably hide
/// the construction behind the provider interface (since we don't
/// care about the construction when using or reasoning about them).


/// 
/// ----------agile implementation of hash specification ------------





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
  | SHA256_Hacl p -> B.live h p
  | SHA256_Vale p -> B.live h p
  | SHA384_Hacl p -> B.live h p

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
  | _ -> admit()

let repr_eq (#a:e_alg) (r1 r2: acc a) =
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


let well_formed (#a:e_alg)
  (s: state a)
  (h: HS.mem{invariant s h}):
  GTot _
=
  let r = repr s h in
  match G.reveal a with
  | SHA256 -> r.k == EverCrypt.Spec.SHA2_256.k
  | SHA384 -> r.k == EverCrypt.Spec.SHA2_384.k
  | _ -> admit()

let bounded_counter (#a:e_alg)
  (s: state a)
  (h: HS.mem{invariant s h})
  (n: nat { n <= pow2 32 }):
  GTot _
=
  let r = repr s h in
  match G.reveal a with
  | SHA256 -> r.counter < pow2 32 - n
  | SHA384 -> r.counter < pow2 32 - n
  | _ -> admit()


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
