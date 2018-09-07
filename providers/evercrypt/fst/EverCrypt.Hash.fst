module EverCrypt.Hash

/// ----------agile implementation of hash specification ------------
/// must be in scope for linking the agile spec to the ad hoc algorithmic specs

//18-08-01 required for re-typechecking the .fsti :(
#set-options "--z3rlimit 200"

let string_of_alg =
  let open C.String in function
  | MD5    -> !$"MD5"
  | SHA1   -> !$"SHA1"
  | SHA224 -> !$"SHA224"
  | SHA256 -> !$"SHA256"
  | SHA384 -> !$"SHA384"
  | SHA512 -> !$"SHA512"

let type_of a =
  match a with
  | MD5 | SHA1 | SHA224 | SHA256 -> UInt32.t // uint_32
  | SHA384 | SHA512              -> UInt64.t // uint_64

let size_of_k a: nat =
  match a with
  | SHA256 -> 64
  | SHA384 -> 80
  | _      -> 0 //TBC

type acc (a:alg) = {
  k: Seq.lseq (type_of a) (size_of_k a);
  hash: Seq.lseq (type_of a) 8;
  counter: nat;
}

// 18-07-10 in principle k would suffice.
let acc0 #a =
  match a with
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
  | _ -> {
      hash = Seq.create 8 (if a = SHA512 then 0UL else 0ul);
      k = Seq.empty;
      counter = 0
    }


// 18-07-06 We need a fully-specified refinement: the hacl* spec
// should state that the counter is incremented by 1 and that the K
// constant is unchanged---a total spec would also save the need for
// stateful invariants.
//
// Besides, all of that could be avoided if the state was just the
// intermediate hash.

let compress #a st b =
  match a with
  | SHA256 ->
     { k       = EverCrypt.Spec.SHA2_256.k;
       hash    = EverCrypt.Spec.SHA2_256.update st.hash b;
       counter = st.counter + 1 }
  | SHA384 ->
     { k       = EverCrypt.Spec.SHA2_384.k;
       hash    = EverCrypt.Spec.SHA2_384.update st.hash b;
       counter = st.counter + 1 }
  | _ -> st //TBC

// using the same be library as in hacl*; to be reconsidered.
// 18-07-10 why do I need type annotations? why passing the same constant 3 types?
let extract #a st =
  match a with
  | SHA224 -> Spec.Lib.uint32s_to_be 7 (Seq.slice st.hash 0 7)
  | SHA256 -> Spec.Lib.uint32s_to_be 8 st.hash
  | SHA384 -> Spec.Lib.uint64s_to_be 6 (Seq.slice st.hash 0 6)
  | SHA512 -> Spec.Lib.uint64s_to_be 8 st.hash
  | _      -> Seq.slice (Spec.Lib.uint32s_to_be 8 st.hash) 0 (tagLength a) //TBC

//#set-options "--z3rlimit 500"
//18-07-12 this immediately verifies from the .fsti :(
let rec lemma_hash2 #a a0 b0 b1 = admit()
(*
  if Seq.length b0 = 0 then (
    Seq.lemma_empty b0;
    Seq.append_empty_l b1 )
  else (
    let c,b0' = Seq.split b0 (blockLength a) in
    let c',b' = Seq.split (Seq.append b0 b1) (blockLength a) in
    Seq.append_assoc c b0' b1;
    Seq.lemma_split b0 (blockLength a);
    Seq.lemma_eq_intro (Seq.append b0 b1) (Seq.append c' b');
    Seq.lemma_eq_intro c c';
    Seq.lemma_eq_intro b' (Seq.append b0' b1);
    lemma_hash2 (hash2 a0 c) b0' b1)
*)

let suffix a l =
  let l1 = l % blockLength a in
  let l0 = l - l1 in
  assert(l0 % blockLength a = 0);
  match a with
  | SHA256 ->
      assert_norm(maxLength a < Spec.SHA2_256.max_input_len_8);
      let pad = Spec.SHA2_256.pad l0 l1 in
      // 18-07-06 the two specs have different structures
      assume(Seq.length pad = suffixLength a l);
      pad
  | SHA384 ->
      assume False;
      // not sure what's wrong with this branch
      //assume(maxLength a < Spec.SHA2_384.max_input_len_8);
      let pad = Spec.SHA2_384.pad l0 l1 in
      assume(Seq.length pad = suffixLength a l);
      pad
  | _ -> admit()

/// 18-04-07 postponing verified integration with HACL* for now. We
/// provide below a concise definition of the Merkle-Damgard
/// construction. The plan is to integrate it with Benjamin's
/// algorithmic specifications. At that point, we will probably hide
/// the construction behind the provider interface (since we don't
/// care about the construction when using or reasoning about them).
///
/// ----------agile implementation of hash specification ------------

open FStar.HyperStack.ST

module HS = FStar.HyperStack
module B = LowStar.Buffer
module M = LowStar.Modifies
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
open C.Failure

let uint32_p = B.buffer uint_32
let uint64_p = B.buffer uint_64

noeq
type state_s: alg -> Type0 =
| SHA256_Hacl: p:uint32_p{ B.freeable p /\ B.length p = v Hacl.SHA2_256.size_state }   -> state_s SHA256
| SHA256_Vale: p:uint32_p{ B.freeable p /\ B.length p = v ValeGlue.sha256_size_state } -> state_s SHA256
| SHA384_Hacl: p:uint64_p{ B.freeable p /\ B.length p = v Hacl.SHA2_384.size_state }   -> state_s SHA384

let footprint_s #a (s: state_s a) =
  match s with
  | SHA256_Hacl p -> M.loc_addr_of_buffer p
  | SHA256_Vale p -> M.loc_addr_of_buffer p
  | SHA384_Hacl p -> M.loc_addr_of_buffer p

#set-options "--max_fuel 0 --max_ifuel 1"

let invariant_s #a s h =
  match s with
  | SHA256_Hacl p -> B.live h p
  | SHA256_Vale p -> B.live h p
  | SHA384_Hacl p -> B.live h p

//#set-options "--z3rlimit 40"

let repr #a s h: GTot _ =
  let s = B.get h s 0 in
  // 18-08-30 regression after moving ghosts around; strange MD5 error?!
  assume False;
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

let repr_eq (#a:alg) (r1 r2: acc a) =
  Seq.equal r1.k r2.k /\
  Seq.equal r1.hash r2.hash /\
  r1.counter = r2.counter

let fresh_is_disjoint l1 l2 h0 h1 = ()

let invariant_loc_in_footprint #a s m = ()

let frame_invariant #a l s h0 h1 =
  let state = B.deref h0 s in
  assert (repr_eq (repr s h0) (repr s h1))

let create a =
  let h0 = ST.get () in
  let i = AC.sha256_impl () in
  let s: state_s a =
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
    | _ ->
        failwith !$"not implemented"
  in
  B.malloc HS.root s 1ul

let has_k (#a:alg) (st:acc a) =
  match a with
  | SHA256 -> st.k == EverCrypt.Spec.SHA2_256.k
  | SHA384 -> st.k == EverCrypt.Spec.SHA2_384.k
  | _ -> True

let rec lemma_hash2_has_k
  (#a:alg)
  (v:acc a {has_k v})
  (b:bytes {Seq.length b % blockLength a = 0}):
  GTot (_:unit{has_k (hash2 v b)}) (decreases (Seq.length b))
=
  if Seq.length b = 0 then
    assert_norm(hash2 v b == v)
  else
    let c,b' = Seq.split b (blockLength a) in
    Seq.lemma_eq_intro b (Seq.append c b');
    lemma_hash2_has_k (compress v c) b';
    lemma_hash2 v c b';
    lemma_compress v c
    // assert(Seq.length b' % blockLength a = 0);
    // assert(has_k (compress v c));
    // assert(hash2 v b == hash2 (compress v c) b')

let lemma_hash0_has_k #a b = lemma_hash2_has_k (acc0 #a) b

let rec lemma_has_counter (#a:alg) (b:bytes {Seq.length b % blockLength a = 0}):
  GTot (_:unit{
    blockLength a <> 0 /\
    (hash0 #a b).counter == Seq.length b / blockLength a}) (decreases (Seq.length b))
=
  admit() //TODO, similar, unnecessary once we get rid of the internal counter

#set-options "--max_fuel 0"
let init #a s =
  assert_norm(acc0 #(Ghost.reveal a) == hash0 #(Ghost.reveal a) (Seq.empty #UInt8.t));
  match !*s with
  | SHA256_Hacl p -> Hacl.SHA2_256.init (T.new_to_old_st p)
  | SHA384_Hacl p -> Hacl.SHA2_384.init (T.new_to_old_st p)
  | SHA256_Vale p -> ValeGlue.sha256_init p; admit ()

#set-options "--z3rlimit 20 --print_implicits"
let update #ea prior s data =
  let h0 = ST.get() in
  ( let a = Ghost.reveal ea in 
    let prior = Ghost.reveal prior in 
    let r0 = repr #a s h0 in
    let fresh = B.as_seq h0 data in
    lemma_hash0_has_k #a prior;
    lemma_has_counter #a prior;
    lemma_compress #a r0 fresh;
    lemma_hash2 #a (acc0 #a) prior fresh;
    //TODO 18-07-10 weaken hacl* update to tolerate overflows; they
    // are now statically prevented in [update_last]
    assume (r0.counter < pow2 32 - 1));

  match !*s with
  | SHA256_Hacl p ->
      let p = T.new_to_old_st p in
      let data = T.new_to_old_st data in
      Hacl.SHA2_256.update p data

  | SHA384_Hacl p ->
      let p = T.new_to_old_st p in
      let data = T.new_to_old_st data in
      Hacl.SHA2_384.update p data

  | SHA256_Vale p ->
      ValeGlue.sha256_update p data;
      admit ()

#set-options "--z3rlimit 300"
let update_multi #ea prior s data len =
  let h0 = ST.get() in
  ( let a = Ghost.reveal ea in 
    let prior = Ghost.reveal prior in
    let r0 = repr #a s h0 in
    let fresh = B.as_seq h0 data in
    lemma_hash0_has_k #a prior;
    lemma_has_counter #a prior;
    lemma_hash2 (acc0 #a) prior fresh;//==> hash0 (Seq.append prior fresh) == hash2 (hash0 prior) fresh
    //TODO 18-07-10 weaken hacl* update to tolerate overflows; they
    // are now statically prevented in [update_last]
    assume (r0.counter + v len / blockLength a < pow2 32 - 1));

  match !*s with
  | SHA256_Hacl p ->
      let n = len / blockLen SHA256 in
      let p = T.new_to_old_st p in
      let data = T.new_to_old_st data in
      // let h = ST.get() in assume(bounded_counter s h (v n));
      Hacl.SHA2_256.update_multi p data n;

      let h1 = ST.get() in
      ( let a = Ghost.reveal ea in 
        let r0 = repr #a s h0 in
        let r1 = repr #a s h1 in
        let fresh = Buffer.as_seq h0 data in
        //TODO 18-07-10 extend Spec.update_multi to align it to hash2,
        //also specifying the counter update.
        assume(
          r1.hash = Spec.SHA2_256.update_multi r0.hash fresh ==>
          r1 == hash2 r0 fresh));
      ()

  | SHA384_Hacl p ->
      let n = len / blockLen SHA384 in
      let p = T.new_to_old_st p in
      let data = T.new_to_old_st data in
      //let h = ST.get() in assume(bounded_counter s h (v n));
      Hacl.SHA2_384.update_multi p data n;

      let h1 = ST.get() in
      ( let a = Ghost.reveal ea in 
        let r0 = repr #a s h0 in
        let r1 = repr #a s h1 in
        let fresh = Buffer.as_seq h0 data in
        //TODO 18-07-10 extend Spec.update_multi to align it to hash2,
        //also specifying the counter update.
        assume(
          r1.hash = Spec.SHA2_384.update_multi r0.hash fresh ==>
          r1 == hash2 r0 fresh));
      ()

  | SHA256_Vale p ->
      let n = len / blockLen SHA256 in
      ValeGlue.sha256_update_multi p data n;
      admit ()

//18-07-07 For SHA384 I was expecting a conversion from 32 to 64 bits

//18-07-10 WIP verification; still missing proper spec for padding
let update_last #ea prior s data totlen =
  let h0 = ST.get() in
  ( 
    let a = Ghost.reveal ea in 
    let r0 = repr #a s h0 in
    let pad = suffix a (v totlen) in
    let prior = Ghost.reveal prior in
    let fresh = Seq.append (B.as_seq h0 data) pad in
    lemma_hash0_has_k #a prior;
    lemma_has_counter #a prior;
    // lemma_hash2 (acc0 #a) prior fresh;//==> hash0 (Seq.append prior fresh) == hash2 (hash0 prior) fresh
    //TODO 18-07-10 weaken hacl* update to tolerate overflows; they
    // are now statically prevented in [update_last]
    assume (r0.counter + 2 < pow2 32 - 1);
    assert(M.(loc_disjoint (footprint #a s h0) (loc_buffer data))));
  match !*s with
  | SHA256_Hacl p ->
      let len = totlen % blockLen SHA256 in
      let p = T.new_to_old_st p in
      let data = T.new_to_old_st data in
      Hacl.SHA2_256.update_last p data len;
      let h1 = ST.get() in
      ( 
        let a = Ghost.reveal ea in 
        let pad = suffix a (v totlen) in
        let prior = Ghost.reveal prior in
        let fresh = Seq.append (Buffer.as_seq h0 data) pad in
        assert(Seq.length fresh % blockLength a = 0);
        let b = Seq.append prior fresh in
        assume(repr #a s h1 == hash0 b) // Hacl.Spec misses at least the updated counter
        )
  | SHA384_Hacl p ->
      let len = totlen % blockLen SHA384 in
      let p = T.new_to_old_st p in
      let data = T.new_to_old_st data in
      admit();//18-07-12 unclear what's missing here
      Hacl.SHA2_384.update_last p data len;
      admit()

  | SHA256_Vale p ->
      let len = totlen % blockLen SHA256 in
      ValeGlue.sha256_update_last p data len;
      admit()

let finish #ea s dst =
  match !*s with
  | SHA256_Hacl p ->
      let p = T.new_to_old_st p in
      let dst = T.new_to_old_st dst in
      Hacl.SHA2_256.finish p dst
  | SHA384_Hacl p ->
      let p = T.new_to_old_st p in
      let dst = T.new_to_old_st dst in
      Hacl.SHA2_384.finish p dst
  | SHA256_Vale p ->
      ValeGlue.sha256_finish p dst;
      admit ()

let free #ea s =
  (match !* s with
  | SHA256_Hacl p -> B.free p
  | SHA384_Hacl p -> B.free p
  | SHA256_Vale p -> B.free p);
  B.free s

let hash a dst input len =
  match a with
  | SHA256 ->
      let i = AC.sha256_impl () in
      if SC.vale && i = AC.Vale then begin
        ValeGlue.sha256_hash dst input len;
        admit ()
      end else begin
        let input = T.new_to_old_st input in
        let dst = T.new_to_old_st dst in
        Hacl.SHA2_256.hash dst input len;
        admit() //18-07-07 TODO align the specs
      end
  | SHA384 ->
      let input = T.new_to_old_st input in
      let dst = T.new_to_old_st dst in
      Hacl.SHA2_384.hash dst input len;
      admit() //18-07-07 TODO align the specs
  | _ ->
      admit ();
      failwith !$"not implemented"
