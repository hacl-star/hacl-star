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
val transpose1: st:state 1 ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1 /\
      as_seq h1 st == Spec.transpose1 (as_seq h0 st)))
let transpose1 st = ()


inline_for_extraction noextract
val transposewxw_i: w:width -> m2:size_pos -> m:size_t -> km:size_t -> inp:lbuffer (vec_t U32 w) (size w) ->
  Stack unit
  (requires fun h -> live h inp /\ w % m2 = 0 /\ v m == 2 * m2 /\ v km == w / v m)
  (ensures  fun h0 _ h1 -> modifies (loc inp) h0 h1)
let transposewxw_i w m2 m km inp =
  let h1 = ST.get () in
  loop_nospec #h1 (size m2) inp
  (fun j ->
    let h2 = ST.get () in
    loop_nospec #h2 km inp
    (fun k ->
      let inp_kj = inp.(k *! m +! j) in
      inp.(k *! m +! j) <- vec_interleave_low_n m2 inp_kj inp.(k *! m +! j +! size m2);
      inp.(k *! m +! j +! size m2) <- vec_interleave_high_n m2 inp_kj inp.(k *! m +! j +! size m2)
    )
  )



inline_for_extraction noextract
val transpose4x4: inp:lbuffer (vec_t U32 4) 4ul ->
  Stack unit
  (requires fun h -> live h inp)
  (ensures  fun h0 _ h1 -> modifies (loc inp) h0 h1)
let transpose4x4 inp =
  transposewxw_i 4 1 2ul 2ul inp;
  transposewxw_i 4 2 4ul 1ul inp


inline_for_extraction noextract
val transpose8x8: inp:lbuffer (vec_t U32 8) 8ul ->
  Stack unit
  (requires fun h -> live h inp)
  (ensures  fun h0 _ h1 -> modifies (loc inp) h0 h1)
let transpose8x8 inp =
  transposewxw_i 8 1 2ul 4ul inp;
  transposewxw_i 8 2 4ul 2ul inp;
  transposewxw_i 8 4 8ul 1ul inp


inline_for_extraction noextract
val transpose16x16: inp:lbuffer (vec_t U32 16) 16ul ->
  Stack unit
  (requires fun h -> live h inp)
  (ensures  fun h0 _ h1 -> modifies (loc inp) h0 h1)
let transpose16x16 inp =
  transposewxw_i 16 1 2ul 8ul inp;
  transposewxw_i 16 2 4ul 4ul inp;
  transposewxw_i 16 4 8ul 2ul inp;
  transposewxw_i 16 8 16ul 1ul inp



inline_for_extraction noextract
val transpose4: st:state 4 ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1 /\
      as_seq h1 st == Spec.transpose4 (as_seq h0 st)))
let transpose4 st =
  push_frame ();
  let st1 = create 16ul (vec_zero U32 4) in
  copy st1 st;
  let h0 = ST.get() in
  transpose4x4 (sub st1 0ul 4ul);
  transpose4x4 (sub st1 4ul 4ul);
  transpose4x4 (sub st1 8ul 4ul);
  transpose4x4 (sub st1 12ul 4ul);

  let (v0,v2,v1,v3) = (st1.(0ul),st1.(1ul),st1.(2ul),st1.(3ul)) in
  let (v4,v6,v5,v7) = (st1.(4ul),st1.(5ul),st1.(6ul),st1.(7ul)) in
  let (v8,v10,v9,v11) = (st1.(8ul),st1.(9ul),st1.(10ul),st1.(11ul)) in
  let (v12,v14,v13,v15) = (st1.(12ul),st1.(13ul),st1.(14ul),st1.(15ul)) in
  admit();
  st.(0ul) <- v0;
  st.(1ul) <- v4;
  st.(2ul) <- v8;
  st.(3ul) <- v12;
  st.(4ul) <- v1;
  st.(5ul) <- v5;
  st.(6ul) <- v9;
  st.(7ul) <- v13;
  let h1 = ST.get() in
  assert (modifies (loc st) h0 h1);
  st.(8ul) <- v2;
  st.(9ul) <- v6;
  st.(10ul) <- v10;
  st.(11ul) <- v14;
  st.(12ul) <- v3;
  st.(13ul) <- v7;
  st.(14ul) <- v11;
  st.(15ul) <- v15;
  let h1 = ST.get() in
  assert (modifies (loc st) h0 h1);
  assert (Lib.Sequence.equal (as_seq h1 st) (Spec.transpose4 (as_seq h0 st)))

inline_for_extraction noextract
val transpose8: st:state 8 ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1 /\
      as_seq h1 st == Spec.transpose8 (as_seq h0 st)))
let transpose8 st =
  push_frame ();
  let st1 = create 16ul (vec_zero U32 8) in
  copy st1 st;
  let h0 = ST.get() in

  transpose8x8 (sub st1 0ul 8ul);
  transpose8x8 (sub st1 8ul 8ul);
  let (v0,v2,v1,v3,v4,v6,v5,v7) = (st1.(0ul),st1.(1ul),st1.(2ul),st1.(3ul),st1.(4ul),st1.(5ul),st1.(6ul),st1.(7ul)) in
  let (v8,v10,v9,v11,v12,v14,v13,v15) = (st1.(8ul),st1.(9ul),st1.(10ul),st1.(11ul),st1.(12ul),st1.(13ul),st1.(14ul),st1.(15ul)) in
  let h1 = ST.get() in admit();
  assert (modifies (loc st)  h0 h1);
  st.(0ul) <- v0;
  st.(1ul) <- v8;
  st.(2ul) <- v1;
  st.(3ul) <- v9;
  st.(4ul) <- v2;
  st.(5ul) <- v10;
  st.(6ul) <- v3;
  st.(7ul) <- v11;
  st.(8ul) <- v4;
  let h1 = ST.get() in
  assert (modifies (loc st)  h0 h1);
  st.(9ul) <- v12;
  st.(10ul) <- v5;
  st.(11ul) <- v13;
  st.(12ul) <- v6;
  st.(13ul) <- v14;
  st.(14ul) <- v7;
  st.(15ul) <- v15;
  let h1 = ST.get() in
  assert (modifies (loc st)  h0 h1);
  assert (Lib.Sequence.equal (as_seq h1 st) (create16 v0 v8 v1 v9 v2 v10 v3 v11 v4 v12 v5 v13 v6 v14 v7 v15));
  assert (Lib.Sequence.equal (as_seq h1 st) (Spec.transpose8 (as_seq h0 st)));
  pop_frame ()


inline_for_extraction noextract
val transpose16: st:state 16 ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1 /\
      as_seq h1 st == Spec.transpose16 (as_seq h0 st)))
let transpose16 st =
  push_frame ();
  let st1 = create 16ul (vec_zero U32 16) in
  copy st1 st;
  let h0 = ST.get() in

  transpose16x16 st1;
  let (v0,v4,v1,v5,v2,v6,v3,v7) = (st1.(0ul),st1.(1ul),st1.(2ul),st1.(3ul),st1.(4ul),st1.(5ul),st1.(6ul),st1.(7ul)) in
  let (v8,v12,v9,v13,v10,v14,v11,v15) = (st1.(8ul),st1.(9ul),st1.(10ul),st1.(11ul),st1.(12ul),st1.(13ul),st1.(14ul),st1.(15ul)) in
  let h1 = ST.get() in admit();
  assert (modifies (loc st)  h0 h1);
  st.(0ul) <- v0;
  st.(1ul) <- v1;
  st.(2ul) <- v2;
  st.(3ul) <- v3;
  st.(4ul) <- v4;
  st.(5ul) <- v5;
  st.(6ul) <- v6;
  st.(7ul) <- v7;
  st.(8ul) <- v8;
  let h1 = ST.get() in
  assert (modifies (loc st)  h0 h1);
  st.(9ul) <- v9;
  st.(10ul) <- v10;
  st.(11ul) <- v11;
  st.(12ul) <- v12;
  st.(13ul) <- v13;
  st.(14ul) <- v14;
  st.(15ul) <- v15;
  let h1 = ST.get() in
  assert (modifies (loc st)  h0 h1);
  pop_frame ()


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
