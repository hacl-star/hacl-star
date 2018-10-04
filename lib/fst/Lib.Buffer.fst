module Lib.Buffer

open FStar.HyperStack
open FStar.HyperStack.ST

//open LowStar.Buffer

open Lib.IntTypes
open Lib.RawIntTypes

module B = LowStar.Buffer
module U32 = FStar.UInt32
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack

module Seq = Lib.Sequence
module ByteSeq = Lib.ByteSequence

#set-options "--z3rlimit 15"

friend Lib.Sequence

let length #a b = B.length b

let as_seq #a #len h b = B.as_seq h b

let sub #a #len #olen b start n =
  B.sub b (size_to_UInt32 start) (size_to_UInt32 n)

let index #a #len b i =
  B.index b (size_to_UInt32 i)

let upd #a #len b i v =
  B.upd b (size_to_UInt32 i) v

let create #a #len clen init =
  B.alloca init (normalize_term (size_to_UInt32 clen))

let createL #a init =
  B.alloca_of_list init

let recall #a #len b = B.recall b

let createL_global #a init =
  B.gcmalloc_of_list HyperStack.root init

let copy #a #len o clen i =
  let h0 = ST.get () in
  LowStar.BufferOps.blit i (size_to_UInt32 (size 0)) o (size_to_UInt32 (size 0)) (size_to_UInt32 clen);
  let h1 = ST.get () in
  assert (Seq.slice #a #len (B.as_seq h1 o) 0 len == Seq.slice #a #len (B.as_seq h0 i) 0 len)

let update_sub #a #len dst start n src =
  let h0 = ST.get () in
  LowStar.BufferOps.blit src 0ul dst (size_to_UInt32 start) (size_to_UInt32 n);
  let h1 = ST.get () in
  assert (forall (k:nat{k < v n}). bget h1 dst (v start + k) == bget h0 src k);
  Seq.eq_intro
    (B.as_seq h1 dst)
    (Seq.update_sub #a #len (B.as_seq h0 dst) (v start) (v n) (B.as_seq h0 src))

let loop_nospec #h0 #a #len n buf impl =
  let inv h1 j = B.modifies (B.loc_buffer buf) h0 h1 in
  Lib.Loops.for (size 0) n inv impl

let loop h0 n a_spec a_impl acc refl footprint spec impl =
  let inv h i = loop_inv h0 n a_spec a_impl acc refl footprint spec i h in
  Lib.Loops.for (size 0) n inv impl

let loop1 #b #blen h0 n acc spec impl =
  let inv h i = loop1_inv h0 n b blen acc spec i h in
  Lib.Loops.for (size 0) n inv impl

#set-options "--z3rlimit 50 --max_fuel 1 --max_ifuel 0"

let lbytes_eq #len a b = admit(); //FIXME
  push_frame();
  let res = create #bool #1 (size 1) true in
  [@ inline_let]
  let refl h _ = B.get h res 0 in
  [@ inline_let]
  let spec h0 = Seq.lbytes_eq_inner #(v len) (as_seq h0 a) (as_seq h0 b) in
  let h0 = ST.get () in
  loop h0 len (fun _ -> bool) (lbuffer bool 1) res refl
    (fun i -> B.loc_buffer res) spec
    (fun i ->
      //Seq.unfold_repeat (v len) (fun _ -> bool) (spec h0) true (v i);
      let ai = a.(i) in
      let bi = b.(i) in
      let res0 = res.(size 0) in
      res.(size 0) <- res0 && FStar.UInt8.(u8_to_UInt8 ai =^ u8_to_UInt8 bi)
    );
  let res = res.(size 0) in
  pop_frame();
  // REMARK: for some reason [lbytes_eq] isn't unfolded
  assert_norm (
    Seq.lbytes_eq #(v len) (as_seq h0 a) (as_seq h0 b) ==
    Seq.repeat (v len) (fun _ -> bool) (spec h0) true);
  res

let alloc #h0 #a #b #w #len #wlen clen init write spec impl =
  admit();
  push_frame();
  let buf = B.alloca init (normalize_term (size_to_UInt32 clen)) in
  let r = impl buf in
  let inv (h1:mem) (j:nat) = True in
  let f' (j:size_t{0 <= v j /\ v j <= len}) : Stack unit
      (requires (fun h -> inv h (v j)))
      (ensures (fun h1 _ h2 -> inv h2 (v j + 1))) =
      upd #a #len buf j init in
  Lib.Loops.for (size 0) clen inv f';
  pop_frame();
  r

let print_compare_display len a b = admit()
