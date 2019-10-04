module Hacl.Impl.Chacha20.Core32

open FStar.HyperStack
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Sequence
open Lib.Buffer
open Lib.ByteBuffer

module ST = FStar.HyperStack.ST
module Spec = Spec.Chacha20


let state = lbuffer uint32 16ul
let index = i:size_t{size_v i < 16}


inline_for_extraction
val create_state: unit ->
  StackInline state
  (requires fun h -> True)
  (ensures  fun h0 r h1 -> live h1 r /\
    as_seq h1 r == Seq.create 16 (u32 0) /\
    stack_allocated r h0 h1 (Seq.create 16 (u32 0)))

let create_state () = create (size 16) (u32 0)


inline_for_extraction
val load_state:
    st:state
  -> b:lbuffer uint8 64ul ->
  Stack unit
  (requires fun h -> live h st /\ live h b /\ disjoint st b)
  (ensures  fun h0 _ h1 -> modifies (loc st) h0 h1 /\
    as_seq h1 st == Lib.ByteSequence.uints_from_bytes_le (as_seq h0 b))

let load_state st b =
  uints_from_bytes_le st b


inline_for_extraction
val store_state:
    b:lbuffer uint8 64ul
  -> st:state ->
  Stack unit
  (requires fun h -> live h st /\ live h b /\ disjoint st b)
  (ensures  fun h0 _ h1 -> modifies (loc b) h0 h1 /\
    as_seq h1 b == Lib.ByteSequence.uints_to_bytes_le (as_seq h0 st))

let store_state st b =
  uints_to_bytes_le 16ul st b


inline_for_extraction
val set_counter:
    st:state
  -> c:size_t ->
  Stack unit
  (requires fun h -> live h st)
  (ensures  fun h0 _ h1 -> modifies (loc st) h0 h1 /\
    as_seq h1 st == Seq.upd (as_seq h0 st) 12 (size_to_uint32 c))

let set_counter st c =
  st.(size 12) <- size_to_uint32 c


inline_for_extraction
val incr_counter:
  st:state ->
  Stack unit
  (requires fun h -> live h st)
  (ensures  fun h0 _ h1 -> modifies (loc st) h0 h1)

let incr_counter st =
  let c = st.(size 12) in
  st.(size 12) <- c +. u32 1


inline_for_extraction
val copy_state:
    st:state
  -> ost:state ->
  Stack unit
  (requires fun h -> live h st /\ live h ost /\ disjoint st ost)
  (ensures  fun h0 _ h1 -> modifies (loc st) h0 h1 /\
    as_seq h1 st == as_seq h0 ost)

let copy_state st ost = copy #MUT #uint32 #(size 16) st ost


inline_for_extraction
val sum_state:
    st:state
  -> ost:state ->
  Stack unit
  (requires fun h -> live h st /\ live h ost /\ eq_or_disjoint st ost)
  (ensures  fun h0 _ h1 -> modifies (loc st) h0 h1 /\
    as_seq h1 st == Spec.sum_state (as_seq h0 st) (as_seq h0 ost))

let sum_state st ost =  map2T #MUT #uint32 #uint32 #uint32 (size 16) st ( +. ) st ost

#set-options "--z3rlimit 100"
inline_for_extraction
val xor_block:
    o:lbuffer uint8 64ul
  -> st:state
  -> b:lbuffer uint8 64ul ->
  Stack unit
  (requires fun h -> live h o /\ live h st /\ live h b)
  (ensures  fun h0 _ h1 -> modifies (loc o) h0 h1 /\
    as_seq h1 o == Spec.xor_block (as_seq h0 st) (as_seq h0 b))

let xor_block o st b =
  push_frame();
  let bl = create_state() in
  load_state bl b;
  map2T (size 16) bl ( ^. ) bl st;
  store_state o bl;
  pop_frame()


inline_for_extraction
val line:
    st:state
  -> a:index
  -> b:index
  -> d:index
  -> r:rotval U32 ->
  Stack unit
  (requires fun h -> live h st /\ v a <> v d)
  (ensures  fun h0 _ h1 -> modifies (loc st) h0 h1 /\
    as_seq h1 st == Spec.line (v a) (v b) (v d) r (as_seq h0 st))

let line st a b d r =
  let sta = st.(a) in
  let stb = st.(b) in
  let std = st.(d) in
  let sta = sta +. stb in
  let std = std ^. sta in
  let std = rotate_left std r in
  st.(a) <- sta;
  st.(d) <- std


val quarter_round:
    st:state
  -> a:index
  -> b:index
  -> c:index
  -> d:index ->
  Stack unit
  (requires fun h -> live h st /\ v a <> v d /\ v c <> v b)
  (ensures  fun h0 _ h1 -> modifies (loc st) h0 h1 /\
    as_seq h1 st == Spec.quarter_round (v a) (v b) (v c) (v d) (as_seq h0 st))

[@ CInline ]
let quarter_round st a b c d =
  line st a b d (size 16);
  line st c d b (size 12);
  line st a b d (size 8);
  line st c d b (size 7)


#reset-options "--z3rlimit 50"

val double_round:
  st:state ->
  Stack unit
  (requires fun h -> live h st)
  (ensures  fun h0 _ h1 -> modifies (loc st) h0 h1 /\
    as_seq h1 st == Spec.double_round (as_seq h0 st))

[@ CInline]
let double_round st =
  quarter_round st (size 0) (size 4) (size 8) (size 12);
  quarter_round st (size 1) (size 5) (size 9) (size 13);
  quarter_round st (size 2) (size 6) (size 10) (size 14);
  quarter_round st (size 3) (size 7) (size 11) (size 15);

  quarter_round st (size 0) (size 5) (size 10) (size 15);
  quarter_round st (size 1) (size 6) (size 11) (size 12);
  quarter_round st (size 2) (size 7) (size 8) (size 13);
  quarter_round st (size 3) (size 4) (size 9) (size 14)
