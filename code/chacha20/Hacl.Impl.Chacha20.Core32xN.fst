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

#reset-options "--using_facts_from '* -FStar.Seq'"

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
val load_state:
    #w:lanes
  -> st:state w
  -> b:lbuffer uint8 (size w *! 64ul) ->
  Stack unit
    (requires (fun h -> live h st /\ live h b /\ disjoint st b))
    (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1 /\
      as_seq h1 st == Spec.load_blocks #w (as_seq h0 b)))
let load_state #w st b =
  let h0 = ST.get() in
  fill h0 16ul st
    (fun h -> let b0 = as_seq h0 b in (Spec.load_blocks_inner #w b0))
    (fun i -> vec_load_le U32 w (sub b (i *! size w *! 4ul) (size w *! 4ul)))

inline_for_extraction noextract
val store_state:
    #w:lanes
  -> b:lbuffer uint8 (size w *! 64ul)
  -> st:state w ->
  Stack unit
    (requires (fun h -> live h st /\ live h b /\ disjoint st b))
    (ensures (fun h0 _ h1 -> modifies (loc b) h0 h1 /\ as_seq h1 b == Spec.store_blocks (as_seq h0 st)))
let store_state #w b st =
  let h0 = ST.get() in
  [@inline_let]
  let store_blocks_a (i:nat{i <= 16}) = unit in
  fill_blocks h0 (size w *! 4ul) 16ul b
    (store_blocks_a)
    (fun h -> fun i -> ())
    (fun i -> LowStar.Monotonic.Buffer.loc_none)
    (fun h -> (Spec.store_blocks_inner (as_seq h0 st)))
    (fun i -> vec_store_le #U32 #w (sub b (i *! (size w *! 4ul)) (size w *! 4ul)) st.(i));
  let h1 = ST.get() in
  assert (16ul *! (size w *! 4ul) == size w *! 64ul);
  Seq.slice_length (as_seq h1 b);
  assert (Lib.Sequence.equal (as_seq h1 b) (as_seq h1 (gsub b 0ul (size w *! 64ul))))

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

#set-options "--z3rlimit 100"

inline_for_extraction noextract
val transpose4: st:state 4 ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1 /\
      as_seq h1 st == Spec.transpose4 (as_seq h0 st)))
let transpose4 st =
  let h0 = ST.get() in
  let (v0,v1,v2,v3) = Spec.transpose4x4 (st.(0ul),st.(1ul),st.(2ul),st.(3ul)) in
  let (v4,v5,v6,v7) = Spec.transpose4x4 (st.(4ul),st.(5ul),st.(6ul),st.(7ul)) in
  let (v8,v9,v10,v11) = Spec.transpose4x4 (st.(8ul),st.(9ul),st.(10ul),st.(11ul)) in
  let (v12,v13,v14,v15) = Spec.transpose4x4 (st.(12ul),st.(13ul),st.(14ul),st.(15ul)) in
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
  let h0 = ST.get() in
  let (v0,v1,v2,v3,v4,v5,v6,v7) = Spec.transpose8x8 (st.(0ul),st.(1ul),st.(2ul),st.(3ul),st.(4ul),st.(5ul),st.(6ul),st.(7ul)) in
  let (v8,v9,v10,v11,v12,v13,v14,v15) = Spec.transpose8x8 (st.(8ul),st.(9ul),st.(10ul),st.(11ul),st.(12ul),st.(13ul),st.(14ul),st.(15ul)) in
  let h1 = ST.get() in
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
  assert (Lib.Sequence.equal (as_seq h1 st) (Spec.transpose8 (as_seq h0 st)))

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

inline_for_extraction noextract
val xor_block:
    #w:lanes
  -> o:lbuffer uint8 ((4ul *! size w) *! 16ul)
  -> st:state w
  -> b:lbuffer uint8 ((4ul *! size w) *! 16ul) ->
  Stack unit
    (requires (fun h -> live h o /\ live h st /\ live h b /\ disjoint st b /\ disjoint st o))
    (ensures (fun h0 _ h1 -> modifies (loc st |+| loc o) h0 h1 /\
      as_seq h1 o == Spec.xor_block #w (as_seq h0 st) (as_seq h0 b)))
let xor_block #w o st b =
  push_frame();
  let bl = create_state w in
  load_state bl b;
  transpose st;
  map2T (size 16) bl ( ^| ) bl st;
  store_state o bl;
  pop_frame()

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

//#set-options "--z3rlimit  200"
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
