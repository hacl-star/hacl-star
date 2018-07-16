module Lib.Buffer

module HS  = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B   = LowStar.Buffer

module Seq = Lib.Sequence
module Int = Lib.IntTypes


type buffer (a: Type0) = b:B.buffer a{~(B.g_is_null #a b)}

let unused_in #a b h = B.unused_in #a b h

let live #a h b = B.live #a h b

let live_not_unused_in #a h b = B.live_not_unused_in #a h b

let frameOf #a b = B.frameOf #a b

let as_addr #a b = B.as_addr #a b

let unused_in_equiv #a b h = B.unused_in_equiv #a b h

let live_region_frameOf #a h b = B.live_region_frameOf #a h b

let len #a b = (Int.size (B.length #a b))

let as_seq #a h b = B.as_seq #a h b

let length_as_seq #a h b = B.length_as_seq #a h b

let includes #a larger smaller = B.includes #a larger smaller

let includes_live #a h larger smaller = B.includes_live #a h larger smaller

let includes_as_seq #a h1 h2 larger smaller = B.includes_as_seq #a h1 h2 larger smaller

let includes_refl #a x = B.includes_refl #a x

let includes_trans #a x y z = B.includes_trans #a x y z

let includes_frameOf_as_addr #a larger smaller = B.includes_frameOf_as_addr #a larger smaller

let gsub #a b i n = B.gsub #a b i n

let live_gsub #a h b i n = B.live_gsub #a h b i n

let includes_gsub #a b i n = B.includes_gsub #a b i n

let len_gsub #a b i n = B.len_gsub #a b i n

let gsub_gsub #a b i1 len1 i2 len2 = B.gsub_gsub #a b i1 len1 i2 len2

let gsub_zero_length #a b = B.gsub_zero_length #a b

let as_seq_gsub #a h b i len = B.as_seq_gsub #a h b i len

let disjoint #a1 #a2 b1 b2 = B.disjoint #a1 #a2 b1 b2

let disjoint_sym #a1 #a2 b1 b2 = B.disjoint_sym #a1 #a2 b1 b2

let disjoint_includes_l #a1 #a2 b1 b1' b2 = B.disjoint_includes_l #a1 #a2 b1 b1' b2

let disjoint_includes_r #a1 #a2 b1 b2 b2' = B.disjoint_includes_r #a1 #a2 b1 b2 b2'

let live_unused_in_disjoint #a1 #a2 h b1 b2 = B.live_unused_in_disjoint #a1 #a2 h b1 b2

let as_addr_disjoint #a1 #a2 b1 b2 = B.as_addr_disjoint #a1 #a2 b1 b2

let gsub_disjoint #a b i1 len1 i2 len2 = B.gsub_disjoint #a b i1 len1 i2 len2

let pointer_distinct_sel_disjoint #a b1 b2 h = B.pointer_distinct_sel_disjoint #a b1 b2 h

let abuffer' region addr = B.abuffer' region addr

let abuffer_preserved #r #a b h h' = B.abuffer_preserved #r #a b h h'

let abuffer_preserved_refl #r #a b h = B.abuffer_preserved_refl #r #a b h

let abuffer_preserved_trans #r #a b h1 h2 h3 = B.abuffer_preserved_trans #r #a b h1 h2 h3

let same_mreference_abuffer_preserved #r #a b h1 h2 f =
  B.same_mreference_abuffer_preserved #r #a b h1 h2 f

let addr_unused_in_abuffer_preserved #r #a b h1 h2 =
  B.addr_unused_in_abuffer_preserved #r #a b h1 h2

let abuffer_of_buffer #t b = B.abuffer_of_buffer #t b

let abuffer_preserved_elim #t b h h' = B.abuffer_preserved_elim #t b h h'

let abuffer_includes #r #a larger smaller = B.abuffer_includes #r #a larger smaller

let abuffer_includes_refl #r #a b = B.abuffer_includes_refl #r #a b

let abuffer_includes_trans #r #a b1 b2 b3 = B.abuffer_includes_trans #r #a b1 b2 b3

let abuffer_includes_abuffer_preserved #r #a larger smaller h1 h2 =
  B.abuffer_includes_abuffer_preserved #r #a larger smaller h1 h2

let abuffer_includes_intro #t larger smaller =
  B.abuffer_includes_intro #t larger smaller

let abuffer_disjoint #r #a b1 b2 = B.abuffer_disjoint #r #a b1 b2

let abuffer_disjoint_sym #r #a b1 b2 = B.abuffer_disjoint_sym #r #a b1 b2

let abuffer_disjoint_includes #r #a larger1 larger2 smaller1 smaller2 =
  B.abuffer_disjoint_includes #r #a larger1 larger2 smaller1 smaller2

let abuffer_disjoint_intro #t1 #t2 b1 b2 = B.abuffer_disjoint_intro #t1 #t2 b1 b2

let liveness_preservation_intro #t h h' b f = B.liveness_preservation_intro #t h h' b f

let modifies_0 h1 h2 = B.modifies_0 h1 h2

let modifies_0_live_region h1 h2 r = B.modifies_0_live_region h1 h2 r

let modifies_0_mreference #a #pre h1 h2 r = B.modifies_0_mreference #a #pre h1 h2 r

let modifies_0_unused_in h1 h2 r n = B.modifies_0_unused_in h1 h2 r n

let modifies_1 #a b h1 h2 = B.modifies_1 #a b h1 h2

let modifies_1_live_region #a b h1 h2 r = B.modifies_1_live_region #a b h1 h2 r

let modifies_1_liveness #a b h1 h2 #a' #pre r' =
  B.modifies_1_liveness #a b h1 h2 #a' #pre r'

let modifies_1_unused_in #t b h1 h2 r n = B.modifies_1_unused_in #t b h1 h2 r n

let modifies_1_mreference #a b h1 h2 #a' #pre r' =
  B.modifies_1_mreference #a b h1 h2 #a' #pre r'

let modifies_1_abuffer #a b h1 h2 b' = B.modifies_1_abuffer #a b h1 h2 b'

let modifies_addr_of #a b h1 h2 = B.modifies_addr_of #a b h1 h2

let modifies_addr_of_live_region #a b h1 h2 r =
  B.modifies_addr_of_live_region #a b h1 h2 r

let modifies_addr_of_mreference #a b h1 h2 #a' #pre r' =
  B.modifies_addr_of_mreference #a b h1 h2 #a' #pre r'

let modifies_addr_of_unused_in #t b h1 h2 r n =
  B.modifies_addr_of_unused_in #t b h1 h2 r n

let sub #a b i len = B.sub #a b i len

let offset #a b i = B.offset #a b i

let index #a b i = B.index #a b i

let g_upd_seq #a b s h = B.g_upd_seq #a b s h

let g_upd_seq_as_seq #a b s h = B.g_upd_seq_as_seq #a b s h

let upd #a b i w = B.upd #a b i w

let recallable #a b = B.recallable #a b

let recallable_includes #a larger smaller =
  B.recallable_includes #a larger smaller

let recall #a b = B.recall #a b

let freeable #a b = B.freeable #a b

let free #a b = B.free #a b

let gcmalloc #a r init len = B.gcmalloc #a r init len

let malloc #a r init len = B.malloc #a r init len

let alloca #a init len = B.alloca #a init len

let alloca_of_list #a init =
  let b = B.alloca_of_list #a init in
  let h = HST.get () in
  Seq.eq_intro #a #(List.Tot.length init) (B.as_seq h b) (Seq.of_list init);
  b

let gcmalloc_of_list #a r init =
  let b = B.gcmalloc_of_list #a r init in
  let h = HST.get () in
  Seq.eq_intro #a #(List.Tot.length init) (B.as_seq h b) (Seq.of_list init);
  b

let as_lseq #a b h = B.as_seq h b

let slice #a b start fin =
  sub #a b start (Int.sub fin start)

(*
let sub #a #len #olen b start n = Buf.sub b (size_to_UInt32 start) (size_to_UInt32 n)
let slice #a #len #olen b start n = Buf.sub b (size_to_UInt32 start) (size_to_UInt32 (n -. start))
let index #a #len b i = Buf.index b (size_to_UInt32 i)
let upd #a #len b i v = Buf.upd b (size_to_UInt32 i) v

let create #a #len clen init = Buf.alloca init (size_to_UInt32 clen)
let createL #a init = Buf.alloca_of_list init
let createL_global #a init = Buf.gcmalloc_of_list HyperStack.root init

let alloc #h0 #a #b #w #len #wlen clen init write spec impl =
  push_frame();
  let buf = create clen init in
  let r = impl buf in
  let inv (h1:mem) (j:nat) = True in
  let f' (j:size_t{0 <= v j /\ v j <= len}) : Stack unit
      (requires (fun h -> inv h (v j)))
      (ensures (fun h1 _ h2 -> inv h2 (v j + 1))) =
      upd #a #len buf j init in
  Lib.Loops.for (size 0) clen inv f';
  pop_frame();
  r
  // Unprotected alloc
  (* push_frame(); *)
  (* let buf = create clen init in *)
  (* let r = impl buf in *)
  (* pop_frame(); *)
  (* r *)

let alloc_with #h0 #a #b #w #len #wlen clen init_spec init write spec impl =
  push_frame();
  let buf = init () in
  let r = impl buf in
  pop_frame();
  r

let alloc_nospec #h0 #a #b #w #len #wlen clen init write impl =
  push_frame();
  let buf = create clen init in
  let r = impl buf in
  let inv (h1:mem) (j:nat) = True in
  let f' (j:size_t{0 <= v j /\ v j <= len}) : Stack unit
      (requires (fun h -> inv h (v j)))
      (ensures (fun h1 _ h2 -> inv h2 (v j + 1))) =
      upd #a #len buf j init in
  Lib.Loops.for (size 0) clen inv f';
  pop_frame();
  r

let map #a #len clen f b =
  let h0 = ST.get() in
  let inv (h1:mem) (j:nat) = True in
  let f' (j:size_t{0 <= v j /\ v j <= len}) : Stack unit
      (requires (fun h -> inv h (v j)))
      (ensures (fun h1 _ h2 -> inv h2 (v j + 1))) =
      let b_i = b.(j) in
      b.(j) <- f b_i in
  Lib.Loops.for (size 0) clen inv f'


let map2 #a1 #a2 #len clen f b1 b2 =
  let h0 = ST.get() in
  let inv (h1:mem) (j:nat) = True in
  let f' (j:size_t{0 <= v j /\ v j <= len}) : Stack unit
      (requires (fun h -> inv h (v j)))
      (ensures (fun h1 _ h2 -> inv h2 (v j + 1))) =
      let i1 = b1.(j) in
      let i2 = b2.(j) in
      b1.(j) <- f i1 i2 in
  Lib.Loops.for (size 0) clen inv f'

let copy #a #len o clen i =
  let h0 = ST.get() in
  let inv (h1:mem) (j:nat) =
    preserves_live h0 h1 /\
    modifies1 o h0 h1 /\
    LSeq.slice (as_lseq #a #len o h1) 0 j ==
    LSeq.slice (as_lseq #a #len i h0) 0 j in
  let f' (j:size_t{0 <= v j /\ v j <= len}) : Stack unit
      (requires (fun h -> inv h (v j)))
      (ensures (fun h1 _ h2 -> inv h2 (v j + 1))) =
      let src_i = i.(j) in
      o.(j) <- src_i in
  Lib.Loops.for (size 0) clen inv f'


let iter_range #a #len start fin spec impl input =
  let h0 = ST.get() in
  let inv (h1:mem) (j:nat) = True in
  let f' (j:size_t{v start <= v j /\ v j <= v fin}) : Stack unit
      (requires (fun h -> inv h (v j)))
      (ensures (fun h1 _ h2 -> inv h2 (v j + 1))) =
      impl j input in
  Lib.Loops.for start fin inv f'

let iteri #a #len n spec impl input = iter_range #a #len (size 0) n spec impl input

let iter #a #len #clen n spec impl input =
  let h0 = ST.get() in
  let inv (h1:mem) (j:nat) = True in
  let f' (j:size_t{0 <= v j /\ v j <= len}) : Stack unit
      (requires (fun h -> inv h (v j)))
      (ensures (fun h1 _ h2 -> inv h2 (v j + 1))) =
      impl input in
  Lib.Loops.for (size 0) n inv f'

inline_for_extraction let loop #h0 #a #len n buf spec impl =
  let inv (h1:mem) (j:nat) = True in
  let f' (j:size_t{0 <= v j /\ v j <= len}) : Stack unit
      (requires (fun h -> inv h (v j)))
      (ensures (fun h1 _ h2 -> inv h2 (v j + 1))) =
      impl j in
  Lib.Loops.for (size 0) n inv f'

inline_for_extraction let loop_set #a #len buf start n init =
  let inv (h1:mem) (j:nat) = True in
  let f' (j:size_t{0 <= v j /\ v j <= len}) : Stack unit
      (requires (fun h -> inv h (v j)))
      (ensures (fun h1 _ h2 -> inv h2 (v j + 1))) =
      upd buf j init in
  Lib.Loops.for start n inv f'

inline_for_extraction let loop_nospec #h0 #a #len n buf impl =
  let inv (h1:mem) (j:nat) = True in
  let f' (j:size_t{0 <= v j /\ v j <= len}) : Stack unit
      (requires (fun h -> inv h (v j)))
      (ensures (fun h1 _ h2 -> inv h2 (v j + 1))) =
      impl j in
  Lib.Loops.for (size 0) n inv f'


inline_for_extraction let map_blocks #h0 #a #bs #nb blocksize nblocks buf f_spec f =
  let inv (h1:mem) (j:nat) = True in
  let f' (j:size_t{0 <= v j /\ v j <= nb}) : Stack unit
      (requires (fun h -> inv h (v j)))
      (ensures (fun h1 _ h2 -> inv h2 (v j + 1))) =
      let bufi = sub #a #(nb*bs) #bs buf (j *. blocksize) blocksize in
      f j in
  Lib.Loops.for (size 0) nblocks inv f'


inline_for_extraction let reduce_blocks #h0 #a #r #bs #nb #rlen blocksize nblocks rbuf f_spec f buf =
  let inv (h1:mem) (j:nat) = True in
  let f' (j:size_t{0 <= v j /\ v j <= nb}) : Stack unit
      (requires (fun h -> inv h (v j)))
      (ensures (fun h1 _ h2 -> inv h2 (v j + 1))) =
      let bufi = sub buf (j *. blocksize) blocksize in
      f j bufi in
  Lib.Loops.for (size 0) nblocks inv f'
*)
