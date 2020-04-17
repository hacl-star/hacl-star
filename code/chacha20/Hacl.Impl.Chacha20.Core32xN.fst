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
module VecTranspose = Lib.IntVector.Transpose
module LSeq = Lib.Sequence

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

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
  st.(8ul) <- v8;
  st.(9ul) <- v9;
  st.(10ul) <- v10;
  st.(11ul) <- v11;
  st.(12ul) <- v12;
  st.(13ul) <- v13;
  st.(14ul) <- v14;
  st.(15ul) <- v15;
  let h1 = ST.get () in
  assert (LSeq.equal (as_seq h1 st) (create16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15))


inline_for_extraction noextract
val transpose1: st:state 1 ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1 /\
      as_seq h1 st == Spec.transpose1 (as_seq h0 st)))
let transpose1 st = ()

inline_for_extraction noextract
val transpose4: st:state 4 ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1 /\
      as_seq h1 st == Spec.transpose4 (as_seq h0 st)))
let transpose4 st =
  let (v0,v1,v2,v3) = VecTranspose.transpose4x4 (st.(0ul),st.(1ul),st.(2ul),st.(3ul)) in
  let (v4,v5,v6,v7) = VecTranspose.transpose4x4 (st.(4ul),st.(5ul),st.(6ul),st.(7ul)) in
  let (v8,v9,v10,v11) = VecTranspose.transpose4x4 (st.(8ul),st.(9ul),st.(10ul),st.(11ul)) in
  let (v12,v13,v14,v15) = VecTranspose.transpose4x4 (st.(12ul),st.(13ul),st.(14ul),st.(15ul)) in
  create16_st st v0 v4 v8 v12 v1 v5 v9 v13 v2 v6 v10 v14 v3 v7 v11 v15


inline_for_extraction noextract
val transpose8: st:state 8 ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1 /\
      as_seq h1 st == Spec.transpose8 (as_seq h0 st)))
let transpose8 st =
  let (v0,v1,v2,v3,v4,v5,v6,v7) = VecTranspose.transpose8x8 (st.(0ul),st.(1ul),st.(2ul),st.(3ul),st.(4ul),st.(5ul),st.(6ul),st.(7ul)) in
  let (v8,v9,v10,v11,v12,v13,v14,v15) = VecTranspose.transpose8x8 (st.(8ul),st.(9ul),st.(10ul),st.(11ul),st.(12ul),st.(13ul),st.(14ul),st.(15ul)) in
  create16_st st v0 v8 v1 v9 v2 v10 v3 v11 v4 v12 v5 v13 v6 v14 v7 v15

inline_for_extraction noextract
val transpose16: st:state 16 ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1 /\
      as_seq h1 st == Spec.transpose16 (as_seq h0 st)))
let transpose16 st =
  let (v0,v1,v2,v3,v4,v5,v6,v7) = (st.(0ul),st.(1ul),st.(2ul),st.(3ul),st.(4ul),st.(5ul),st.(6ul),st.(7ul)) in
  let (v8,v9,v10,v11,v12,v13,v14,v15) = (st.(8ul),st.(9ul),st.(10ul),st.(11ul),st.(12ul),st.(13ul),st.(14ul),st.(15ul)) in
  let ((r0,r1,r2,r3,r4,r5,r6,r7),(r8,r9,r10,r11,r12,r13,r14,r15)) =
    VecTranspose.transpose16x16 ((v0,v1,v2,v3,v4,v5,v6,v7), (v8,v9,v10,v11,v12,v13,v14,v15)) in
  create16_st st r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15


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
