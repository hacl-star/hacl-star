module Hacl.Impl.Chacha20.Core32

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

let state = lbuffer uint32 16ul
let index = (i:size_t{size_v i < 16})

inline_for_extraction
val create_state: unit -> StackInline state
		  (requires (fun h -> True))
   		  (ensures (fun h0 r h1 -> live h1 r /\ stack_allocated r h0 h1 (Seq.create 16 (u32 0))))
let create_state () = create (size 16) (u32 0) 

inline_for_extraction
val load_state: st:state -> b:lbuffer uint8 64ul -> ST unit
		  (requires (fun h -> live h st /\ live h b))
   		  (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1))
let load_state st b =
    uints_from_bytes_le st b

inline_for_extraction
val set_counter: st:state -> c:size_t -> ST unit
		  (requires (fun h -> live h st))
   		  (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1))
let set_counter st c =
    st.(size 12) <- size_to_uint32 c

inline_for_extraction
val incr_counter: st:state -> ST unit
		  (requires (fun h -> live h st))
   		  (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1))
let incr_counter st =
    let c = st.(size 12) in
    st.(size 12) <- c +. u32 1

inline_for_extraction
val copy_state: st:state -> ost:state -> ST unit
		  (requires (fun h -> live h st /\ live h ost /\ disjoint st ost))
   		  (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1))
let copy_state st ost =
    copy st ost


inline_for_extraction
val sum_state: st:state -> ost:state -> ST unit
		  (requires (fun h -> live h st /\ live h ost))
   		  (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1))
let sum_state st ost =
    let h0 = ST.get() in
    loop_nospec #h0 (size 16) st 
      (fun i -> let si = st.(i) in
	     let osi = ost.(i) in
	     st.(i) <- si +. osi)



inline_for_extraction
val xor_block: o:lbuffer uint8 64ul -> st:state -> b:lbuffer uint8 64ul -> ST unit
		  (requires (fun h -> live h o /\ live h st /\ live h b))
   		  (ensures (fun h0 _ h1 -> modifies (loc o) h0 h1))
let xor_block o st b =
    let h0 = ST.get () in
    loop_nospec #h0 (size 16) o 
      (fun i -> 
	let u = uint_from_bytes_le (sub b (i *. size 4) (size 4)) in
        uint_to_bytes_le (sub o (i *. size 4) (size 4)) (u ^. st.(i)))
    
    

inline_for_extraction
val line: st:state -> a:index -> b:index -> d:index -> r:rotval U32 -> ST unit
		  (requires (fun h -> live h st))
		  (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1))
let line st a b d r = 
  let sta = st.(a) in
  let stb = st.(b) in
  let std = st.(d) in
  let sta = sta +. stb in
  let std = std ^. sta in
  let std = rotate_left std r in
  st.(a) <- sta;
  st.(d) <- std


inline_for_extraction
val quarter_round: st:state -> a:index -> b:index -> c:index -> d:index -> ST unit
		  (requires (fun h -> live h st))
		  (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1))
[@ CInline ]
let quarter_round st a b c d = 
    line st a b d (size 16);
    line st c d b (size 12);
    line st a b d (size 8);
    line st c d b (size 7)

[@ CInline]
val double_round: st:state -> ST unit
		  (requires (fun h -> live h st))
		  (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1))
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
