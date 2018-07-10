module EverCrypt.Hash

/// ----------agile implementation of hash specification ------------
/// must be in scope for linking the agile spec to the ad hoc algorithmic specs

let string_of_alg = 
  let open C.String in function
  | MD5    -> !$"MD5"
  | SHA1   -> !$"SHA1"
  | SHA224 -> !$"SHA224"
  | SHA256 -> !$"SHA256"
  | SHA384 -> !$"SHA384"
  | SHA512 -> !$"SHA512"


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

// 18-07-10 in principle k would suffice.
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
  
// using the same be library as in hacl*; to be reconsidered.
// 18-07-10 why do I need type annotations? why passing the same constant 3 types? 
let extract #a st = 
  let a = Ghost.reveal a in 
  match a with 
  | SHA224 -> Spec.Lib.uint32s_to_be 7 (Seq.slice st.hash 0 7)
  | SHA256 -> Spec.Lib.uint32s_to_be 8 st.hash 
  | SHA384 -> Spec.Lib.uint64s_to_be 6 (Seq.slice st.hash 0 6)
  | SHA512 -> Spec.Lib.uint64s_to_be 8 st.hash 
  | _      -> admit()

/// ------ at this point interactive verification dies; using c-c c-l

// 18-07-06 TODO; should be provable, despite the two specs having
// different structures.
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
| SHA256_Hacl: p:uint32_p{ B.length p = U32.v Hacl.SHA2_256.size_state} -> state_s (G.hide SHA256)
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

let fresh_is_disjoint l1 l2 h0 h1 = ()

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
    | _ ->  magic()  // 18-07-09 TODO use failwith instead
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

let has_k (#a:e_alg) (st:acc a) = 
  match G.reveal a with
  | SHA256 -> st.k == EverCrypt.Spec.SHA2_256.k
  | SHA384 -> st.k == EverCrypt.Spec.SHA2_384.k
  | _ -> True

let rec lemma_hash2_has_k
  (#a:e_alg) 
  (v:acc a {has_k v})
  (b:bytes {Seq.length b % blockLength a = 0}): 
  GTot (_:unit{has_k (hash2 v b)}) (decreases (Seq.length b))
=  
  if Seq.length b = 0 then ()
  else
    let c,b = Seq.split b (blockLength a) in
    assert(Seq.length b % blockLength a = 0);
    assert(has_k (compress v c)); 
    lemma_hash2_has_k (compress v c) b

let lemma_hash0_has_k #a b = lemma_hash2_has_k (acc0 #a) b

let rec lemma_has_counter (#a:e_alg) (b:bytes {Seq.length b % blockLength a = 0}):
  GTot (_:unit{
    blockLength a <> 0 /\ 
    (hash0 #a b).counter == Seq.length b / blockLength a}) 
= 
  admit() //TODO, similar

#set-options "--max_fuel 0"
let init #a s =
  assert_norm(acc0 #a == hash0 #a (Seq.empty #UInt8.t)); 
  match !*s with
  | SHA256_Hacl p -> Hacl.SHA2_256.init (T.new_to_old_st p)
  | SHA384_Hacl p -> Hacl.SHA2_384.init (T.new_to_old_st p)
  | SHA256_Vale p -> ValeGlue.sha256_init p; admit ()

#set-options "--z3rlimit 20"
let update #a #prior s data =
  ( let h0 = ST.get() in 
    let r0 = repr s h0 in 
    let prior = Ghost.reveal prior in 
    let fresh = B.as_seq h0 data in 
    lemma_hash0_has_k #a prior;
    lemma_has_counter #a prior;
    lemma_compress r0 fresh;
    lemma_hash2 (acc0 #a) prior fresh;
    //TODO 18-07-10 weaken hacl* update to tolerate overflows; they
    // are now statically prevented in [update_last]
    assume (r0.counter < pow2 32 - 1));
    
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


let update_multi #a #prior s data len =
  let h0 = ST.get() in 
  ( let r0 = repr s h0 in 
    let prior = Ghost.reveal prior in 
    let fresh = B.as_seq h0 data in 
    lemma_hash0_has_k #a prior;
    lemma_has_counter #a prior;
    lemma_hash2 (acc0 #a) prior fresh;//==> hash0 (Seq.append prior fresh) == hash2 (hash0 prior) fresh
    //TODO 18-07-10 weaken hacl* update to tolerate overflows; they
    // are now statically prevented in [update_last]
  assume (r0.counter + v len / blockLength a < pow2 32 - 1));

  match !*s with
  | SHA256_Hacl p ->
      let n = FStar.UInt32.(len /^ blockLen SHA256) in 
      assert M.(loc_disjoint (M.loc_buffer data) (M.loc_buffer p));
      let p = T.new_to_old_st p in
      let data = T.new_to_old_st data in
      // JP: in spite of the assertion above, the transition module does not
      // seem to allow me to derive this fact
      assume (FStar.Buffer.disjoint p data);
      // let h = ST.get() in assume(bounded_counter s h (v n)); 
      Hacl.SHA2_256.update_multi p data n;

      ( let h1 = ST.get() in
        let r0 = repr s h0 in 
        let r1 = repr s h1 in 
        let fresh = Buffer.as_seq h0 data in 
        //TODO 18-07-10 extend Spec.update_multi to align it to hash2,
        //also specifying the counter update.
        assume(
          r1.hash = Spec.SHA2_256.update_multi r0.hash fresh ==>
          r1 == hash2 r0 fresh)) 

  | SHA384_Hacl p ->
      let n = len / blockLen SHA384 in 
      assert M.(loc_disjoint (M.loc_buffer data) (M.loc_buffer p));
      let p = T.new_to_old_st p in
      let data = T.new_to_old_st data in
      // JP: in spite of the assertion above, the transition module does not
      // seem to allow me to derive this fact
      assume (FStar.Buffer.disjoint p data);
      //let h = ST.get() in assume(bounded_counter s h (v n)); 
      Hacl.SHA2_384.update_multi p data n;

      ( let h1 = ST.get() in
        let r0 = repr s h0 in 
        let r1 = repr s h1 in 
        let fresh = Buffer.as_seq h0 data in 
        //TODO 18-07-10 extend Spec.update_multi to align it to hash2,
        //also specifying the counter update.
        assume(
          r1.hash = Spec.SHA2_384.update_multi r0.hash fresh ==>
          r1 == hash2 r0 fresh)) 
      
  | SHA256_Vale p ->
      let n = len / blockLen SHA256 in 
      ValeGlue.sha256_update_multi p data n;
      admit ()

//18-07-07 For SHA384 I was expecting a conversion from 32 to 64 bits

//18-07-10 WIP verification 
let update_last #a #prior s data totlen =
  let h0 = ST.get() in 
  ( let r0 = repr s h0 in 
    let pad = suffix a (v totlen) in //TODO suffix still undefined here, not really exported by hacl*
    let prior = Ghost.reveal prior in 
    let fresh = Seq.append (B.as_seq h0 data) pad in
    lemma_hash0_has_k #a prior;
    lemma_has_counter #a prior;
    // lemma_hash2 (acc0 #a) prior fresh;//==> hash0 (Seq.append prior fresh) == hash2 (hash0 prior) fresh
    //TODO 18-07-10 weaken hacl* update to tolerate overflows; they
    // are now statically prevented in [update_last]
    assume (r0.counter + 2 < pow2 32 - 1));

  match !*s with
  | SHA256_Hacl p ->
      let len = totlen % blockLen SHA256 in
      assert M.(loc_disjoint (M.loc_buffer data) (M.loc_buffer p));
      let p = T.new_to_old_st p in
      let data = T.new_to_old_st data in
      // JP: in spite of the assertion above, the transition module does not
      // seem to allow me to derive this fact
      assume (FStar.Buffer.disjoint p data);
      Hacl.SHA2_256.update_last p data len;

      ( let h1 = ST.get() in 
        let pad = suffix a (v totlen) in //TODO suffix still undefined here & underspecified by hacl*
        let prior = Ghost.reveal prior in 
        let fresh = Seq.append (Buffer.as_seq h0 data) pad in
        assume (hashing s h1 (Seq.append prior fresh));
        admit()
        )

  | SHA384_Hacl p ->
      let len = totlen % blockLen SHA384 in
      assert M.(loc_disjoint (M.loc_buffer data) (M.loc_buffer p));
      let p = T.new_to_old_st p in
      let data = T.new_to_old_st data in
      // JP: in spite of the assertion above, the transition module does not
      // seem to allow me to derive this fact
      assume (FStar.Buffer.disjoint p data);
      Hacl.SHA2_384.update_last p data len;
      admit() //18-07-07 TODO align the specs
  | SHA256_Vale p ->
      let len = totlen % blockLen SHA256 in 
      ValeGlue.sha256_update_last p data len;
      admit()

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
        Hacl.SHA2_256.hash dst input len;
        admit() //18-07-07 TODO align the specs
      end
  | SHA384 ->
      assert M.(loc_disjoint (M.loc_buffer dst) (M.loc_buffer input));
      let input = T.new_to_old_st input in
      let dst = T.new_to_old_st dst in
      assume (FStar.Buffer.disjoint dst input);
      Hacl.SHA2_384.hash dst input len;
      admit() //18-07-07 TODO align the specs
  | _ -> admit() // how to get a kremlin fatal error?

