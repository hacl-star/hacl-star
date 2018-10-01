module BufferViewHelpers

module  B = LowStar.Buffer
module BV = LowStar.BufferView
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
open FStar.HyperStack.ST

open LowStar.Modifies
open LowStar.ModifiesPat

let lemma_bv_equal
  (#src:Type) (#dst:Type) (view:BV.view src dst) (b:B.buffer src) (h0 h1:HS.mem)
  :Lemma (requires (B.length b % BV.View?.n view == 0 /\ B.as_seq h0 b == B.as_seq h1 b))
         (ensures  (let bv = BV.mk_buffer_view b view in BV.as_seq h0 bv == BV.as_seq h1 bv))
   [SMTPat (BV.as_seq h0 (BV.mk_buffer_view b view)); SMTPat (BV.as_seq h1 (BV.mk_buffer_view b view))]
  = let bv = BV.mk_buffer_view b view in

    BV.as_buffer_mk_buffer_view b view;

    BV.length_eq bv;

    FStar.Classical.forall_intro (BV.view_indexing bv);
    FStar.Classical.forall_intro (BV.as_seq_sel h0 bv);
    FStar.Classical.forall_intro (BV.as_seq_sel h1 bv);
    FStar.Classical.forall_intro (BV.get_sel h0 bv);
    FStar.Classical.forall_intro (BV.get_sel h1 bv);
    Seq.lemma_eq_intro (BV.as_seq h0 bv) (BV.as_seq h1 bv)


let sel_underlying_buffer_unmodified (#src:Type) (#dst:Type) (view:BV.view src dst) (b:B.buffer src) (h0 h1:HS.mem) (i:nat) : Lemma
  (requires (B.length b % BV.View?.n view == 0 /\
             B.as_seq h0 b == B.as_seq h1 b /\
             i < B.length b / BV.View?.n view))
  (ensures  (let bv = BV.mk_buffer_view b view in
             i < BV.length bv /\
             BV.sel h0 bv i == BV.sel h1 bv i))
  [SMTPat (BV.sel h0 (BV.mk_buffer_view b view) i); SMTPat (BV.sel h1 (BV.mk_buffer_view b view) i)]
  =
  let bv = BV.mk_buffer_view b view in
  BV.as_buffer_mk_buffer_view b view;
  BV.get_view_mk_buffer_view b view;
  BV.length_eq bv;

  lemma_bv_equal view b h0 h1;

  if i < BV.length bv then (
    BV.as_seq_sel h0 bv i;
    BV.as_seq_sel h1 bv i;
    ()
  ) else ();
  ()

(*

///////////////   Test 1

let test1 (#src:Type) (#dst:Type) (view:BV.view src dst) (b:B.buffer src)
  :Stack unit (requires (fun h0      -> B.length b % BV.View?.n view == 0 /\ B.live h0 b))
              (ensures  (fun h0 _ h1 -> True))
  = let h0 = ST.get () in
    push_frame ();
    let h1 = ST.get () in

    // Not needed with the SMTPat's above
    //lemma_bv_equal view b h0 h1;

    assert (let bv = BV.mk_buffer_view b view in BV.as_seq h0 bv == BV.as_seq h1 bv);

    pop_frame ()


///////////////   Test 2

module U8 = FStar.UInt8
module U32 = FStar.UInt32
let buffer_to_int (b:B.buffer U8.t { B.length b % 4 == 0 /\ B.length b > 0 }) (h:HS.mem) : GTot int =
  let b32 = BV.mk_buffer_view b Views.view32 in
  BV.as_buffer_mk_buffer_view b Views.view32;
  BV.get_view_mk_buffer_view b Views.view32;
  BV.length_eq b32;
  U32.v (BV.sel h b32 0)
  //U32.v (Seq.index (BV.as_seq h b32) 0)

let test2 (b:B.buffer U8.t)
  :Stack unit (requires (fun h0      ->
                                   B.length b > 0 /\ B.length b % 4 == 0 /\ B.live h0 b /\
                                   buffer_to_int b h0 == 7))
              (ensures  (fun h0 _ h1 -> True))
  = let h0 = ST.get () in
    push_frame ();
    let h1 = ST.get () in

    // Not needed with the SMTPat's above
    //lemma_bv_equal Views.view32 b h0 h1;
    //sel_underlying_buffer_unmodified Views.view32 b h0 h1 0;

    assert (buffer_to_int b h1 == 7);

    pop_frame ()

*)
