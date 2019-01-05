module Hacl.Impl.Chacha20.Core32xN

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Sequence
open Lib.Buffer
open Lib.ByteBuffer
open Lib.IntVector
module Spec = Spec.Chacha20_Vec

open LowStar.Modifies.Linear

#reset-options "--using_facts_from '* -LowStar.Monotonic.Buffer.modifies_trans -FStar.Seq'"

let lanes = Spec.lanes

inline_for_extraction
let uint32xN (w:lanes) = vec_t U32 w
inline_for_extraction
let state (w:lanes) = lbuffer (uint32xN w) 16ul
inline_for_extraction
let index = (i:size_t{size_v i < 16})

inline_for_extraction
val create_state: w:lanes -> StackInline (state w)
		  (requires (fun h -> True))
   		  (ensures (fun h0 r h1 -> live h1 r /\ 
					as_seq h1 r == Seq.create 16 (vec_zero U32 w) /\
					stack_allocated r h0 h1 (Seq.create 16 (vec_zero U32 w))))
let create_state w = create (size 16) (vec_zero U32 w) 

#set-options "--admit_smt_queries true"
inline_for_extraction
val load_state: #w:lanes -> st:state w -> b:lbuffer uint8 ((4ul *! size w) *! 16ul) -> ST unit
		  (requires (fun h -> live h st /\ live h b /\ disjoint st b))
   		  (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1 ))
let load_state #w st b =
    let h0 = ST.get() in
    fill h0 16ul st 
      (fun h -> (fun i -> admit()))
      (fun i -> vec_load_le U32 w (sub b ((4ul *! size w) *! i) (4ul *! size w)))


inline_for_extraction
val store_state: #w:lanes -> b:lbuffer uint8 (size w *! 64ul) -> st:state w -> ST unit
		  (requires (fun h -> live h st /\ live h b))
   		  (ensures (fun h0 _ h1 -> modifies (loc b) h0 h1))
let store_state #w b st =
    let h0 = ST.get() in
    loop1 h0 16ul b 
      (fun h -> fun i -> admit())
      (fun i -> vec_store_le #U32 #w (sub b ((4ul *! size w) *! i) (4ul *! size w)) st.(i))
#set-options "--admit_smt_queries false"

inline_for_extraction
val add_counter: #w:lanes -> st:state w -> c:size_t -> ST unit
		  (requires (fun h -> live h st))
   		  (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1 /\
			   as_seq h1 st == Seq.upd (as_seq h0 st) 12 
					   (Seq.index (as_seq h0 st) 12 +| (vec_load  (size_to_uint32 c) w))))
let add_counter #w st c =
    let v = vec_load #U32 (size_to_uint32 c) w in
    let old_c = st.(12ul) in
    st.(size 12) <- old_c +| v

inline_for_extraction
val copy_state: #w:lanes -> st:state w -> ost:state w -> ST unit
		  (requires (fun h -> live h st /\ live h ost /\ disjoint st ost))
   		  (ensures (fun h0 _ h1 -> 
		    modifies (loc st) h0 h1 /\
		    as_seq h1 st == as_seq h0 ost))
let copy_state #w st ost = copy st ost


inline_for_extraction
val sum_state: #w:lanes -> st:state w -> ost:state w -> ST unit
		  (requires (fun h -> live h st /\ live h ost /\ eq_or_disjoint st ost))
   		  (ensures (fun h0 _ h1 -> 
		    modifies (loc st) h0 h1 /\
		    as_seq h1 st == Spec.sum_state (as_seq h0 st) (as_seq h0 ost)))
let sum_state #w st ost =  map2T (size 16) st ( +| ) st ost
      
inline_for_extraction
val transpose_state1: st:state 1 -> ST unit
		  (requires (fun h -> live h st))
   		  (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1))
let transpose_state1 st = ()

inline_for_extraction
val transpose_4x4: st:lbuffer (uint32xN 4) 4ul -> ST unit
		  (requires (fun h -> live h st))
   		  (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1))
let transpose_4x4 st = 
  let v0 = vec_interleave_low st.(0ul) st.(1ul) in
  let v1 = vec_interleave_high st.(0ul) st.(1ul) in
  let v2 = vec_interleave_low st.(2ul) st.(3ul) in
  let v3 = vec_interleave_high st.(2ul) st.(3ul) in
  let v0' = cast U32 4 (vec_interleave_low (cast U64 2 v0) (cast U64 2 v2)) in
  let v1' = cast U32 4 (vec_interleave_high (cast U64 2 v0) (cast U64 2 v2)) in
  let v2' = cast U32 4 (vec_interleave_low (cast U64 2 v1) (cast U64 2 v3)) in
  let v3' = cast U32 4 (vec_interleave_high (cast U64 2 v1) (cast U64 2 v3)) in
  st.(0ul) <- v0';
  st.(1ul) <- v1';
  st.(2ul) <- v2';
  st.(3ul) <- v3'

inline_for_extraction
val transpose_state4: st:state 4 -> ST unit
		  (requires (fun h -> live h st))
   		  (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1))
let transpose_state4 st = 
  let h0 = ST.get() in
  transpose_4x4 (sub st 0ul 4ul);
  let h1 = ST.get() in
  assert (modifies (loc st) h0 h1);
  transpose_4x4 (sub st 4ul 4ul);
  let h1 = ST.get() in
  assert (modifies (loc st) h0 h1);
  transpose_4x4 (sub st 8ul 4ul);
  let h1 = ST.get() in
  assert (modifies (loc st) h0 h1);
  transpose_4x4 (sub st 12ul 4ul);
  let h1 = ST.get() in
  assert (modifies (loc st) h0 h1);
  let v0 = st.(0ul) in
  let v1 = st.(4ul) in
  let v2 = st.(8ul) in
  let v3 = st.(12ul) in
  let v4 = st.(1ul) in
  let v5 = st.(5ul) in
  let v6 = st.(9ul) in
  let v7 = st.(13ul) in
  let v8 = st.(2ul) in
  let v9 = st.(6ul) in
  let v10 = st.(10ul) in
  let v11 = st.(14ul) in
  let v12 = st.(3ul) in
  let v13 = st.(7ul) in
  let v14 = st.(11ul) in
  let v15 = st.(15ul) in
  st.(0ul) <- v0;
  st.(1ul) <- v1;
  st.(2ul) <- v2;
  st.(3ul) <- v3;
  st.(4ul) <- v4;
  st.(5ul) <- v5;
  st.(6ul) <- v6;
  st.(7ul) <- v7;
  let h1 = ST.get() in
  assert (modifies (loc st) h0 h1);
  st.(8ul) <- v8;
  st.(9ul) <- v9;
  st.(10ul) <- v10;
  st.(11ul) <- v11;
  st.(12ul) <- v12;
  st.(13ul) <- v13;
  st.(14ul) <- v14;
  st.(15ul) <- v15;
  let h1 = ST.get() in
  assert (modifies (loc st) h0 h1)


inline_for_extraction
val transpose_8x8: st:lbuffer (uint32xN 8) 8ul -> ST unit
		  (requires (fun h -> live h st))
   		  (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1))
let transpose_8x8 st = 
  let v0 = vec_interleave_low st.(0ul) st.(1ul) in
  let v1 = vec_interleave_high st.(0ul) st.(1ul) in
  let v2 = vec_interleave_low st.(2ul) st.(3ul) in
  let v3 = vec_interleave_high st.(2ul) st.(3ul) in
  let v4 = vec_interleave_low st.(4ul) st.(5ul) in
  let v5 = vec_interleave_high st.(4ul) st.(5ul) in
  let v6 = vec_interleave_low st.(6ul) st.(7ul) in
  let v7 = vec_interleave_high st.(6ul) st.(7ul) in
  let v0' = cast U32 8 (vec_interleave_low (cast U64 4 v0) (cast U64 4 v2)) in
  let v1' = cast U32 8 (vec_interleave_high (cast U64 4 v0) (cast U64 4 v2)) in
  let v2' = cast U32 8 (vec_interleave_low (cast U64 4 v1) (cast U64 4 v3)) in
  let v3' = cast U32 8 (vec_interleave_high (cast U64 4 v1) (cast U64 4 v3)) in
  let v4' = cast U32 8 (vec_interleave_low (cast U64 4 v4) (cast U64 4 v6)) in
  let v5' = cast U32 8 (vec_interleave_high (cast U64 4 v4) (cast U64 4 v6)) in
  let v6' = cast U32 8 (vec_interleave_low (cast U64 4 v5) (cast U64 4 v7)) in
  let v7' = cast U32 8 (vec_interleave_high (cast U64 4 v5) (cast U64 4 v7)) in
  let v0'' = cast U32 8 (vec_interleave_low (cast U128 2 v0') (cast U128 2 v4')) in
  let v1'' = cast U32 8 (vec_interleave_high (cast U128 2 v0') (cast U128 2 v4')) in
  let v2'' = cast U32 8 (vec_interleave_low (cast U128 2 v1') (cast U128 2 v5')) in
  let v3'' = cast U32 8 (vec_interleave_high (cast U128 2 v1') (cast U128 2 v5')) in
  let v4'' = cast U32 8 (vec_interleave_low (cast U128 2 v2') (cast U128 2 v6')) in
  let v5'' = cast U32 8 (vec_interleave_high (cast U128 2 v2') (cast U128 2 v6')) in
  let v6'' = cast U32 8 (vec_interleave_low (cast U128 2 v3') (cast U128 2 v7')) in
  let v7'' = cast U32 8 (vec_interleave_high (cast U128 2 v3') (cast U128 2 v7')) in
  st.(0ul) <- v0'';
  st.(1ul) <- v1'';
  st.(2ul) <- v2'';
  st.(3ul) <- v3'';
  st.(4ul) <- v4'';
  st.(5ul) <- v5'';
  st.(6ul) <- v6'';
  st.(7ul) <- v7''

inline_for_extraction
val transpose_state8: st:state 8 -> ST unit
		  (requires (fun h -> live h st))
   		  (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1))
let transpose_state8 st = 
  let h0 = ST.get() in
  transpose_8x8 (sub st 0ul 8ul);
  transpose_8x8 (sub st 8ul 8ul);
  let h1 = ST.get() in
  assert (modifies (loc st)  h0 h1);
  let v0 = st.(0ul) in
  let v1 = st.(8ul) in
  let v2 = st.(1ul) in
  let v3 = st.(9ul) in
  let v4 = st.(2ul) in
  let v5 = st.(10ul) in
  let v6 = st.(3ul) in
  let v7 = st.(11ul) in
  let v8 = st.(4ul) in
  let v9 = st.(12ul) in
  let v10 = st.(5ul) in
  let v11 = st.(13ul) in
  let v12 = st.(6ul) in
  let v13 = st.(14ul) in
  let v14 = st.(7ul) in
  let v15 = st.(15ul) in
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
  assert (modifies (loc st)  h0 h1)
  
inline_for_extraction
val transpose_state: #w:lanes -> st:state w -> ST unit
		  (requires (fun h -> live h st))
   		  (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1))
let transpose_state #w st = 
  match w with
  | 1 -> transpose_state1 st
  | 4 -> transpose_state4 st
  | 8 -> transpose_state8 st

inline_for_extraction
val xor_block: #w:lanes -> o:lbuffer uint8 ((4ul *! size w) *! 16ul) -> st:state w -> b:lbuffer uint8 ((4ul *! size w) *! 16ul) -> ST unit
		  (requires (fun h -> live h o /\ live h st /\ live h b))
   		  (ensures (fun h0 _ h1 -> modifies (loc o) h0 h1 /\
		    as_seq h1 o == Spec.xor_block #w (as_seq h0 st) (as_seq h0 b)))
let xor_block #w o st b =
    push_frame();
    let bl = create_state w in
    load_state bl b;
    let h0 = ST.get () in
    transpose_state st;
    map2T (size 16) bl ( ^| ) bl st;
    store_state o bl;
    admit();
    pop_frame()


inline_for_extraction
val line: #w:lanes -> st:state w -> a:index -> b:index -> d:index -> r:rotval U32 -> ST unit
		  (requires (fun h -> live h st /\ v a <> v d))
		  (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1 /\
		    as_seq h1 st == Spec.line (v a) (v b) (v d) r (as_seq h0 st)))
let line #w st a b d r = 
  let sta = st.(a) in
  let stb = st.(b) in
  let std = st.(d) in
  let sta = sta +| stb in
  let std = std ^| sta in
  let std = std <<<| r in
  st.(a) <- sta;
  st.(d) <- std

inline_for_extraction
val quarter_round: #w:lanes -> st:state w -> a:index -> b:index -> c:index -> d:index -> ST unit
		  (requires (fun h -> live h st /\ v a <> v d /\ v c <> v b))
		  (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1 /\
			   as_seq h1 st == Spec.quarter_round (v a) (v b) (v c) (v d) (as_seq h0 st)))
[@ CInline ]
let quarter_round #w st a b c d = 
    line st a b d (size 16);
    line st c d b (size 12);
    line st a b d (size 8);
    line st c d b (size 7)

#set-options "--z3rlimit  200"
inline_for_extraction
val double_round_: #w:lanes -> st:state w -> ST unit
		  (requires (fun h -> live h st))
		  (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1 /\
		    as_seq h1 st == Spec.double_round (as_seq h0 st)))
let double_round_ #w st = 
  quarter_round st (size 0) (size 4) (size 8) (size 12);
  quarter_round st (size 1) (size 5) (size 9) (size 13);
  quarter_round st (size 2) (size 6) (size 10) (size 14);
  quarter_round st (size 3) (size 7) (size 11) (size 15);

  quarter_round st (size 0) (size 5) (size 10) (size 15);
  quarter_round st (size 1) (size 6) (size 11) (size 12);
  quarter_round st (size 2) (size 7) (size 8) (size 13);
  quarter_round st (size 3) (size 4) (size 9) (size 14)

[@CInline]
let double_round1 st = double_round_ #1 st
[@CInline]
let double_round4 st = double_round_ #4 st
[@CInline]
let double_round8 st = double_round_ #8 st

inline_for_extraction
val double_round: #w:lanes -> st:state w -> ST unit
		  (requires (fun h -> live h st))
		  (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1 /\
		    as_seq h1 st == Spec.double_round (as_seq h0 st)))
inline_for_extraction
let double_round #w st =
  match w with
  | 1 -> double_round1 st
  | 4 -> double_round4 st
  | 8 -> double_round8 st

  
