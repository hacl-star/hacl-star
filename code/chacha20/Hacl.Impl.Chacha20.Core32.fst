module Hacl.Impl.Chacha20.Core32

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Sequence
open Lib.Buffer
open Lib.ByteBuffer
module Spec = Spec.Chacha20

let state = lbuffer uint32 16ul
let index = (i:size_t{size_v i < 16})

inline_for_extraction
val create_state: unit -> StackInline state
		  (requires (fun h -> True))
   		  (ensures (fun h0 r h1 -> live h1 r /\
					as_seq h1 r == Seq.create 16 (u32 0) /\
					stack_allocated r h0 h1 (Seq.create 16 (u32 0))))
let create_state () = create (size 16) (u32 0)

inline_for_extraction
val load_state: st:state -> b:lbuffer uint8 64ul -> Stack unit
		  (requires (fun h -> live h st /\ live h b /\ disjoint st b))
   		  (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1 /\
			   as_seq h1 st == Lib.ByteSequence.uints_from_bytes_le (as_seq h0 b)))
let load_state st b =
    uints_from_bytes_le st b

inline_for_extraction
val store_state: b:lbuffer uint8 64ul -> st:state -> Stack unit
		  (requires (fun h -> live h st /\ live h b /\ disjoint st b))
   		  (ensures (fun h0 _ h1 -> modifies (loc b) h0 h1 /\
		    as_seq h1 b == Lib.ByteSequence.uints_to_bytes_le (as_seq h0 st)))
let store_state st b =
    uints_to_bytes_le 16ul st b

inline_for_extraction
val set_counter: st:state -> c:size_t -> Stack unit
		  (requires (fun h -> live h st))
   		  (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1 /\
			   as_seq h1 st == Seq.upd (as_seq h0 st) 12 (size_to_uint32 c)))
let set_counter st c =
    st.(size 12) <- size_to_uint32 c

inline_for_extraction
val incr_counter: st:state -> Stack unit
		  (requires (fun h -> live h st))
   		  (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1))
let incr_counter st =
    let c = st.(size 12) in
    st.(size 12) <- c +. u32 1

inline_for_extraction
val copy_state: st:state -> ost:state -> Stack unit
		  (requires (fun h -> live h st /\ live h ost /\ disjoint st ost))
   		  (ensures (fun h0 _ h1 ->
		    modifies (loc st) h0 h1 /\
		    as_seq h1 st == as_seq h0 ost))
let copy_state st ost = copy #MUT #uint32 #(size 16) st ost


inline_for_extraction
val sum_state: st:state -> ost:state -> Stack unit
		  (requires (fun h -> live h st /\ live h ost /\ eq_or_disjoint st ost))
   		  (ensures (fun h0 _ h1 ->
		    modifies (loc st) h0 h1 /\
		    as_seq h1 st == Spec.sum_state (as_seq h0 st) (as_seq h0 ost)))
let sum_state st ost =  map2T #MUT #uint32 #uint32 #uint32 (size 16) st ( +. ) st ost


inline_for_extraction
val xor_block: o:lbuffer uint8 64ul -> st:state -> b:lbuffer uint8 64ul -> Stack unit
		  (requires (fun h -> live h o /\ live h st /\ live h b))
   		  (ensures (fun h0 _ h1 -> modifies (loc o) h0 h1 /\
					as_seq h1 o == Spec.xor_block (as_seq h0 st) (as_seq h0 b)))
let xor_block o st b =
    push_frame();
    let bl = create_state() in
    load_state bl b;
    let h0 = ST.get () in
    map2T (size 16) bl ( ^. ) bl st;
    store_state o bl;
    pop_frame()



inline_for_extraction
val line: st:state -> a:index -> b:index -> d:index -> r:rotval U32 -> Stack unit
		  (requires (fun h -> live h st /\ v a <> v d))
		  (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1 /\
		    as_seq h1 st == Spec.line (v a) (v b) (v d) r (as_seq h0 st)))
let line st a b d r =
  let sta = st.(a) in
  let stb = st.(b) in
  let std = st.(d) in
  let sta = sta +. stb in
  let std = std ^. sta in
  let std = rotate_left std r in
  st.(a) <- sta;
  st.(d) <- std

inline_for_extraction val line_alt: a:uint32 -> b:uint32 -> d:uint32 -> r:rotval U32 -> Tot (uint32 & uint32)
inline_for_extraction let line_alt sta stb std r =
  let sta = sta +. stb in
  let std = std ^. sta in
  let std = rotate_left std r in
  (sta, std)

inline_for_extraction
val quarter_round: st:state -> a:index -> b:index -> c:index -> d:index -> Stack unit
		  (requires (fun h -> live h st /\ v a <> v d /\ v c <> v b))
		  (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1 /\
			   as_seq h1 st == Spec.quarter_round (v a) (v b) (v c) (v d) (as_seq h0 st)))
[@ CInline ]
let quarter_round st a b c d =
    line st a b d (size 16);
    line st c d b (size 12);
    line st a b d (size 8);
    line st c d b (size 7)

type quarter_state_alt = uint32 & uint32 & uint32 & uint32

inline_for_extraction val quarter_round_alt: quarter_state_alt -> Tot quarter_state_alt
inline_for_extraction let quarter_round_alt qs =
  let (a, b, c, d) = qs in
  let (a, d) = line_alt a b d (size 16) in
  let (c, b) = line_alt c d b (size 12) in
  let (a, d) = line_alt a b d (size 8) in
  let (c, b) = line_alt c d b (size 7) in
  (a, b, c, d)

type state_alt = quarter_state_alt & quarter_state_alt & quarter_state_alt & quarter_state_alt

inline_for_extraction val double_round_alt: st: state_alt -> Tot state_alt
inline_for_extraction let double_round_alt st =
  let ((s0, s1, s2, s3), (s4, s5, s6, s7), (s8, s9, s10, s11), (s12, s13, s14, s15)) = st in
  let (s0, s4, s8, s12) = quarter_round_alt (s0, s4, s8, s12) in
  let (s1, s5, s9, s13) = quarter_round_alt (s1, s5, s9, s13) in
  let (s2, s6, s10, s14) = quarter_round_alt (s2, s6, s10, s14) in
  let (s3, s7, s11, s15) = quarter_round_alt (s3, s7, s11, s15) in

  let (s0, s5, s10, s15) = quarter_round_alt (s0, s5, s10, s15) in
  let (s1, s6, s11, s12) = quarter_round_alt (s1, s6, s11, s12) in
  let (s2, s7, s8, s13) = quarter_round_alt (s2, s7, s8, s13) in
  let (s3, s4, s9, s14) = quarter_round_alt (s3, s4, s9, s14) in
  ((s0, s1, s2, s3), (s4, s5, s6, s7), (s8, s9, s10, s11), (s12, s13, s14, s15))


[@ CInline]
val double_round: st:state -> Stack unit
		  (requires (fun h -> live h st))
		  (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1 /\
	
	            as_seq h1 st == Spec.double_round (as_seq h0 st)))
(*
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
*)

[@ CInline]
let double_round st =
  let s0 = Lib.Buffer.index st (size 0) in
  let s1 = Lib.Buffer.index st (size 1) in
  let s2 = Lib.Buffer.index st (size 2) in
  let s3 = Lib.Buffer.index st (size 3) in
  let s4 = Lib.Buffer.index st (size 4) in
  let s5 = Lib.Buffer.index st (size 5) in
  let s6 = Lib.Buffer.index st (size 6) in
  let s7 = Lib.Buffer.index st (size 7) in
  let s8 = Lib.Buffer.index st (size 8) in
  let s9 = Lib.Buffer.index st (size 9) in
  let s10 = Lib.Buffer.index st (size 10) in
  let s11 = Lib.Buffer.index st (size 11) in
  let s12 = Lib.Buffer.index st (size 12) in
  let s13 = Lib.Buffer.index st (size 13) in
  let s14 = Lib.Buffer.index st (size 14) in
  let s15 = Lib.Buffer.index st (size 15) in
  let ((s0, s1, s2, s3), (s4, s5, s6, s7), (s8, s9, s10, s11), (s12, s13, s14, s15)) =
    double_round_alt ((s0, s1, s2, s3), (s4, s5, s6, s7), (s8, s9, s10, s11), (s12, s13, s14, s15))
  in
  Lib.Buffer.upd st (size 0) s0;
  Lib.Buffer.upd st (size 1) s1;
  Lib.Buffer.upd st (size 2) s2;
  Lib.Buffer.upd st (size 3) s3;
  Lib.Buffer.upd st (size 4) s4;
  Lib.Buffer.upd st (size 5) s5;
  Lib.Buffer.upd st (size 6) s6;
  Lib.Buffer.upd st (size 7) s7;
  Lib.Buffer.upd st (size 8) s8;
  Lib.Buffer.upd st (size 9) s9;
  Lib.Buffer.upd st (size 10) s10;
  Lib.Buffer.upd st (size 11) s11;
  Lib.Buffer.upd st (size 12) s12;
  Lib.Buffer.upd st (size 13) s13;
  Lib.Buffer.upd st (size 14) s14;
  Lib.Buffer.upd st (size 15) s15;
  admit()
