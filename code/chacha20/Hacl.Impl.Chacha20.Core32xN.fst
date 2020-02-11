module Hacl.Impl.Chacha20.Core32xN

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Lib.IntVector

module Spec = Hacl.Spec.Chacha20.Vec
module Loop = Lib.LoopCombinators
module LSeq = Lib.Sequence


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

let lanes = Spec.lanes

inline_for_extraction
let uint32xN (w:lanes) = vec_t U32 w
inline_for_extraction
let state (w:lanes) = lbuffer (uint32xN w) 16ul
inline_for_extraction
let index = (i:size_t{size_v i < 16})

inline_for_extraction noextract
val create_state: w:lanes -> StackInline (state w)
  (requires (fun h -> True))
  (ensures (fun h0 r h1 -> live h1 r /\
    as_seq h1 r == Seq.create 16 (vec_zero U32 w) /\
    stack_allocated r h0 h1 (Seq.create 16 (vec_zero U32 w))))
let create_state w = create (size 16) (vec_zero U32 w)

inline_for_extraction noextract
val add_counter:
    #w:lanes
  -> st:state w
  -> c:size_t{w * v c <= max_size_t} ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1 /\
      as_seq h1 st == Spec.add_counter #w (v c) (as_seq h0 st)))
let add_counter #w st c =
  let v = vec_load #U32 (u32 w *! size_to_uint32 c) w in
  let old_c = st.(12ul) in
  st.(size 12) <- old_c +| v

inline_for_extraction noextract
val copy_state:
    #w:lanes
  -> st:state w
  -> ost:state w ->
  Stack unit
    (requires (fun h -> live h st /\ live h ost /\ disjoint st ost))
    (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1 /\
      as_seq h1 st == as_seq h0 ost))
let copy_state #w st ost = copy st ost

inline_for_extraction noextract
val sum_state:
    #w:lanes
  -> st:state w
  -> ost:state w ->
  Stack unit
    (requires (fun h -> live h st /\ live h ost /\ eq_or_disjoint st ost))
    (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1 /\
      as_seq h1 st == Spec.sum_state (as_seq h0 st) (as_seq h0 ost)))
let sum_state #w st ost =  map2T (size 16) st ( +| ) st ost


inline_for_extraction noextract
val transposewxw_i_k: #w:lanes -> m2:size_pos -> j:size_t{v j < m2} -> k:size_t{v k < w / (2 * m2)}
  -> inp:lbuffer (vec_t U32 w) (size w) ->
  Stack unit
    (requires fun h -> live h inp /\ w % m2 = 0)
    (ensures  fun h0 _ h1 -> modifies (loc inp) h0 h1 /\
      as_seq h1 inp == Spec.transposewxw_i_k m2 (v j) (v k) (as_seq h0 inp))

let transposewxw_i_k #w m2 j k inp =
  [@inline_let]
  let m = size (2 * m2) in
  let inp_kj = inp.(k *! m +! j) in
  inp.(k *! m +! j) <- vec_interleave_low_n m2 inp_kj inp.(k *! m +! j +! size m2);
  inp.(k *! m +! j +! size m2) <- vec_interleave_high_n m2 inp_kj inp.(k *! m +! j +! size m2)


inline_for_extraction noextract
val transposewxw_i_f: #w:lanes -> m2:size_pos -> j:size_t{v j < m2}
  -> inp:lbuffer (vec_t U32 w) (size w) ->
  Stack unit
    (requires fun h -> live h inp /\ w % m2 = 0)
    (ensures  fun h0 _ h1 -> modifies (loc inp) h0 h1 /\
      as_seq h1 inp == Spec.transposewxw_i_f m2 (v j) (as_seq h0 inp))

let transposewxw_i_f #w m2 j inp =
  [@inline_let]
  let spec h0 = Spec.transposewxw_i_k m2 (v j) in
  let h0 = ST.get () in
  loop1 h0 (size (w / (2 * m2))) inp spec
  (fun k ->
    Loop.unfold_repeati (w / (2 * m2)) (spec h0) (as_seq h0 inp) (v k);
    transposewxw_i_k #w m2 j k inp
  )


inline_for_extraction noextract
val transposewxw_i: #w:lanes -> m2:size_pos -> inp:lbuffer (vec_t U32 w) (size w) ->
  Stack unit
    (requires fun h -> live h inp /\ w % m2 = 0)
    (ensures  fun h0 _ h1 -> modifies (loc inp) h0 h1 /\
      as_seq h1 inp == Loop.repeati m2 (Spec.transposewxw_i_f m2) (as_seq h0 inp))

let transposewxw_i #w m2 inp =
  [@inline_let]
  let spec h0 = Spec.transposewxw_i_f m2 in
  let h0 = ST.get () in
  loop1 h0 (size m2) inp spec
  (fun j ->
    Loop.unfold_repeati m2 (spec h0) (as_seq h0 inp) (v j);
    transposewxw_i_f #w m2 j inp
  )


inline_for_extraction noextract
val transpose4x4: inp:lbuffer (vec_t U32 4) 4ul ->
  Stack unit
    (requires fun h -> live h inp)
    (ensures  fun h0 _ h1 -> modifies (loc inp) h0 h1 /\
      as_seq h1 inp == Spec.transposewxw 2 (as_seq h0 inp))

let transpose4x4 inp =
  let h0 = ST.get () in
  Loop.unfold_repeati 2 (Spec.transposewxw_f 2) (as_seq h0 inp) 1;
  Loop.unfold_repeati 2 (Spec.transposewxw_f 2) (as_seq h0 inp) 0;
  Loop.eq_repeati0 2 (Spec.transposewxw_f 2) (as_seq h0 inp);
  transposewxw_i 1 inp;
  transposewxw_i 2 inp


inline_for_extraction noextract
val transpose8x8: inp:lbuffer (vec_t U32 8) 8ul ->
  Stack unit
    (requires fun h -> live h inp)
    (ensures  fun h0 _ h1 -> modifies (loc inp) h0 h1 /\
      as_seq h1 inp == Spec.transposewxw 3 (as_seq h0 inp))

let transpose8x8 inp =
  let h0 = ST.get () in
  Loop.unfold_repeati 3 (Spec.transposewxw_f 3) (as_seq h0 inp) 2;
  Loop.unfold_repeati 3 (Spec.transposewxw_f 3) (as_seq h0 inp) 1;
  Loop.unfold_repeati 3 (Spec.transposewxw_f 3) (as_seq h0 inp) 0;
  Loop.eq_repeati0 3 (Spec.transposewxw_f 3) (as_seq h0 inp);
  transposewxw_i 1 inp;
  transposewxw_i 2 inp;
  transposewxw_i 4 inp


inline_for_extraction noextract
val transpose16x16: inp:lbuffer (vec_t U32 16) 16ul ->
  Stack unit
    (requires fun h -> live h inp)
    (ensures  fun h0 _ h1 -> modifies (loc inp) h0 h1 /\
      as_seq h1 inp == Spec.transposewxw 4 (as_seq h0 inp))

let transpose16x16 inp =
  let h0 = ST.get () in
  Loop.unfold_repeati 4 (Spec.transposewxw_f 4) (as_seq h0 inp) 3;
  Loop.unfold_repeati 4 (Spec.transposewxw_f 4) (as_seq h0 inp) 2;
  Loop.unfold_repeati 4 (Spec.transposewxw_f 4) (as_seq h0 inp) 1;
  Loop.unfold_repeati 4 (Spec.transposewxw_f 4) (as_seq h0 inp) 0;
  Loop.eq_repeati0 4 (Spec.transposewxw_f 4) (as_seq h0 inp);
  transposewxw_i 1 inp;
  transposewxw_i 2 inp;
  transposewxw_i 4 inp;
  transposewxw_i 8 inp


inline_for_extraction noextract
val transpose1: st:state 1 ->
  Stack unit
    (requires fun h -> live h st)
    (ensures  fun h0 _ h1 -> modifies (loc st) h0 h1 /\
      as_seq h1 st == Spec.transpose1 (as_seq h0 st))
let transpose1 st = ()


inline_for_extraction noextract
val create16_st: #w:lanes -> st:state w ->
  v0:uint32xN w -> v1:uint32xN w -> v2:uint32xN w -> v3:uint32xN w ->
  v4:uint32xN w -> v5:uint32xN w -> v6:uint32xN w -> v7:uint32xN w ->
  v8:uint32xN w -> v9:uint32xN w -> v10:uint32xN w -> v11:uint32xN w ->
  v12:uint32xN w -> v13:uint32xN w -> v14:uint32xN w -> v15:uint32xN w ->
  Stack unit
    (requires fun h -> live h st)
    (ensures  fun h0 _ h1 -> modifies (loc st) h0 h1 /\
      as_seq h1 st == create16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15)

let create16_st #w st v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 =
  let h0 = ST.get () in
  st.(0ul) <- v0;
  st.(1ul) <- v1;
  st.(2ul) <- v2;
  st.(3ul) <- v3;
  st.(4ul) <- v4;
  st.(5ul) <- v5;
  st.(6ul) <- v6;
  st.(7ul) <- v7;
  let h1 = ST.get () in
  assert (modifies (loc st) h0 h1);
  assert (LSeq.equal (LSeq.sub (as_seq h1 st) 0 8) (LSeq.sub (create16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15) 0 8));

  st.(8ul) <- v8;
  st.(9ul) <- v9;
  st.(10ul) <- v10;
  st.(11ul) <- v11;
  st.(12ul) <- v12;
  st.(13ul) <- v13;
  st.(14ul) <- v14;
  st.(15ul) <- v15;
  let h2 = ST.get () in
  assert (modifies (loc st) h0 h2);
  assert (LSeq.equal (LSeq.sub (as_seq h2 st) 0 8) (LSeq.sub (as_seq h1 st) 0 8));
  assert (LSeq.equal (LSeq.sub (as_seq h2 st) 8 8) (LSeq.sub (create16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15) 8 8));
  Seq.Properties.lemma_split (as_seq h1 st) 8;
  Seq.Properties.lemma_split (as_seq h2 st) 8;
  Seq.Properties.lemma_split (create16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15) 8;
  assert (LSeq.equal (as_seq h2 st) (create16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15))


inline_for_extraction noextract
val transpose4: st:state 4 ->
  Stack unit
    (requires fun h -> live h st)
    (ensures  fun h0 _ h1 -> modifies (loc st) h0 h1 /\
      as_seq h1 st == Spec.transpose4 (as_seq h0 st))

let transpose4 st =
  let h0 = ST.get () in
  update_sub_f h0 st 0ul 4ul
    (fun h -> Spec.transposewxw 2 (LSeq.sub (as_seq h0 st) 0 4))
    (fun _ -> transpose4x4 (sub st 0ul 4ul));

  let (v0,v2,v1,v3) = (st.(0ul),st.(1ul),st.(2ul),st.(3ul)) in
  LSeq.eq_intro (create4 v0 v2 v1 v3) (Spec.transposewxw 2 (LSeq.sub (as_seq h0 st) 0 4));
  assert (create4 v0 v2 v1 v3 == Spec.transposewxw 2 (LSeq.sub (as_seq h0 st) 0 4));

  let h1 = ST.get () in
  update_sub_f h1 st 4ul 4ul
    (fun h -> Spec.transposewxw 2 (LSeq.sub (as_seq h1 st) 4 4))
    (fun _ -> transpose4x4 (sub st 4ul 4ul));

  let (v4,v6,v5,v7) = (st.(4ul),st.(5ul),st.(6ul),st.(7ul)) in
  LSeq.eq_intro (create4 v4 v6 v5 v7) (Spec.transposewxw 2 (LSeq.sub (as_seq h1 st) 4 4));
  LSeq.eq_intro (LSeq.sub (as_seq h1 st) 4 4) (LSeq.sub (as_seq h0 st) 4 4);
  assert (create4 v4 v6 v5 v7 == Spec.transposewxw 2 (LSeq.sub (as_seq h0 st) 4 4));

  let h2 = ST.get () in
  update_sub_f h2 st 8ul 4ul
    (fun h -> Spec.transposewxw 2 (LSeq.sub (as_seq h2 st) 8 4))
    (fun _ -> transpose4x4 (sub st 8ul 4ul));

  let (v8,v10,v9,v11) = (st.(8ul),st.(9ul),st.(10ul),st.(11ul)) in
  LSeq.eq_intro (create4 v8 v10 v9 v11) (Spec.transposewxw 2 (LSeq.sub (as_seq h2 st) 8 4));
  LSeq.eq_intro (LSeq.sub (as_seq h2 st) 8 4) (LSeq.sub (as_seq h0 st) 8 4);
  assert (create4 v8 v10 v9 v11 == Spec.transposewxw 2 (LSeq.sub (as_seq h0 st) 8 4));

  let h3 = ST.get () in
  update_sub_f h3 st 12ul 4ul
    (fun h -> Spec.transposewxw 2 (LSeq.sub (as_seq h3 st) 12 4))
    (fun _ -> transpose4x4 (sub st 12ul 4ul));

  let (v12,v14,v13,v15) = (st.(12ul),st.(13ul),st.(14ul),st.(15ul)) in
  LSeq.eq_intro (create4 v12 v14 v13 v15) (Spec.transposewxw 2 (LSeq.sub (as_seq h3 st) 12 4));
  LSeq.eq_intro (LSeq.sub (as_seq h3 st) 12 4) (LSeq.sub (as_seq h0 st) 12 4);
  assert (create4 v12 v14 v13 v15 == Spec.transposewxw 2 (LSeq.sub (as_seq h0 st) 12 4));

  create16_st st v0 v4 v8 v12 v1 v5 v9 v13 v2 v6 v10 v14 v3 v7 v11 v15


inline_for_extraction noextract
val transpose8: st:state 8 ->
  Stack unit
    (requires fun h -> live h st)
    (ensures  fun h0 _ h1 -> modifies (loc st) h0 h1 /\
      as_seq h1 st == Spec.transpose8 (as_seq h0 st))

let transpose8 st =
  let h0 = ST.get () in
  update_sub_f h0 st 0ul 8ul
    (fun h -> Spec.transposewxw 3 (LSeq.sub (as_seq h0 st) 0 8))
    (fun _ -> transpose8x8 (sub st 0ul 8ul));

  let (v0,v2,v1,v3,v4,v6,v5,v7) = (st.(0ul),st.(1ul),st.(2ul),st.(3ul),st.(4ul),st.(5ul),st.(6ul),st.(7ul)) in
  LSeq.eq_intro (create8 v0 v2 v1 v3 v4 v6 v5 v7) (Spec.transposewxw 3 (LSeq.sub (as_seq h0 st) 0 8));
  LSeq.eq_intro (create8 v0 v1 v2 v3 v4 v5 v6 v7) (Spec.transpose8x8 (LSeq.sub (as_seq h0 st) 0 8));
  //assert (create8 v0 v2 v1 v3 v4 v6 v5 v7 == Spec.transposewxw 3 (LSeq.sub (as_seq h0 st) 0 8));

  let h1 = ST.get () in
  update_sub_f h1 st 8ul 8ul
    (fun h -> Spec.transposewxw 3 (LSeq.sub (as_seq h1 st) 8 8))
    (fun _ -> transpose8x8 (sub st 8ul 8ul));

  let (v8,v10,v9,v11,v12,v14,v13,v15) = (st.(8ul),st.(9ul),st.(10ul),st.(11ul),st.(12ul),st.(13ul),st.(14ul),st.(15ul)) in
  LSeq.eq_intro (create8 v8 v10 v9 v11 v12 v14 v13 v15) (Spec.transposewxw 3 (LSeq.sub (as_seq h1 st) 8 8));
  LSeq.eq_intro (LSeq.sub (as_seq h1 st) 8 8) (LSeq.sub (as_seq h0 st) 8 8);
  LSeq.eq_intro (create8 v8 v9 v10 v11 v12 v13 v14 v15) (Spec.transpose8x8 (LSeq.sub (as_seq h0 st) 8 8));
  //assert (create8 v8 v10 v9 v11 v12 v14 v13 v15 == Spec.transposewxw 3 (LSeq.sub (as_seq h0 st) 8 8));

  create16_st st v0 v8 v1 v9 v2 v10 v3 v11 v4 v12 v5 v13 v6 v14 v7 v15


inline_for_extraction noextract
val transpose16: st:state 16 ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1 /\
      as_seq h1 st == Spec.transpose16 (as_seq h0 st)))

let transpose16 st =
  transpose16x16 st;
  let (v0,v2,v1,v3,v4,v6,v5,v7) = (st.(0ul),st.(1ul),st.(2ul),st.(3ul),st.(4ul),st.(5ul),st.(6ul),st.(7ul)) in
  let (v8,v10,v9,v11,v12,v14,v13,v15) = (st.(8ul),st.(9ul),st.(10ul),st.(11ul),st.(12ul),st.(13ul),st.(14ul),st.(15ul)) in

  create16_st st v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15


inline_for_extraction noextract
val transpose:
    #w:lanes
  -> st:state w ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1 /\
      as_seq h1 st == Spec.transpose (as_seq h0 st)))
let transpose #w st =
  match w with
  | 1 -> transpose1 st
  | 4 -> transpose4 st
  | 8 -> transpose8 st
  | 16 -> transpose16 st


inline_for_extraction noextract
val xor_block:
    #w:lanes
  -> o:lbuffer uint8 ((4ul *! size w) *! 16ul)
  -> st:state w
  -> b:lbuffer uint8 ((4ul *! size w) *! 16ul) ->
  Stack unit
    (requires (fun h -> live h o /\ live h st /\ live h b /\
      disjoint st b /\ disjoint st o /\ eq_or_disjoint b o))
    (ensures (fun h0 _ h1 -> modifies (loc st |+| loc o) h0 h1 /\
      as_seq h1 o == Spec.xor_block #w (as_seq h0 st) (as_seq h0 b)))
let xor_block #w o st b =
  let h0 = ST.get () in
  map_blocks_multi h0 (size w *! 4ul) 16ul b o
  (fun h -> Spec.xor_block_f #w (as_seq h0 st))
  (fun i ->
    [@inline_let]
    let bs = normalize_term (size w *! 4ul) in
    let x = vec_load_le U32 w (sub b (i *! bs) bs) in
    let y = x ^| st.(i) in
    vec_store_le #U32 #w (sub o (i *! bs) bs) y
  )

inline_for_extraction noextract
val line:
    #w:lanes
  -> st:state w
  -> a:index -> b:index -> d:index
  -> r:rotval U32 ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1 /\
      as_seq h1 st == Spec.line (v a) (v b) (v d) r (as_seq h0 st)))
let line #w st a b d r =
  st.(a) <- st.(a) +| st.(b);
  let std = st.(d) ^| st.(a) in
  st.(d) <- std <<<| r

inline_for_extraction noextract
val quarter_round:
    #w:lanes
  -> st:state w
  -> a:index -> b:index -> c:index -> d:index ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1 /\
      as_seq h1 st == Spec.quarter_round (v a) (v b) (v c) (v d) (as_seq h0 st)))
let quarter_round #w st a b c d =
  line st a b d (size 16);
  line st c d b (size 12);
  line st a b d (size 8);
  line st c d b (size 7)


inline_for_extraction noextract
val double_round:
    #w:lanes
  -> st:state w ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1 /\
      as_seq h1 st == Spec.double_round (as_seq h0 st)))
[@ Meta.Attribute.specialize ]
let double_round #w st =
  quarter_round st (size 0) (size 4) (size 8) (size 12);
  quarter_round st (size 1) (size 5) (size 9) (size 13);
  quarter_round st (size 2) (size 6) (size 10) (size 14);
  quarter_round st (size 3) (size 7) (size 11) (size 15);

  quarter_round st (size 0) (size 5) (size 10) (size 15);
  quarter_round st (size 1) (size 6) (size 11) (size 12);
  quarter_round st (size 2) (size 7) (size 8) (size 13);
  quarter_round st (size 3) (size 4) (size 9) (size 14)
