module Hacl.Impl.Chacha20.Core128

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open LowStar.Buffer
open Lib.Utils
open Lib.Vec128

let state = lbuffer vec128 16
let index = (i:size_t{size_v i < 16})
let rot32 = (i:uint32{uint_v i > 0 /\ uint_v i < 32})

inline_for_extraction
val create_state: unit -> StackInline state
		  (requires (fun h -> True))
   		  (ensures (fun h0 r h1 -> live h1 r))
let create_state () = create vec128_zero (size 16)

inline_for_extraction
val load_state: st:state -> b:lbytes 64 -> ST unit
		  (requires (fun h -> live h st /\ live h b))
   		  (ensures (fun h0 _ h1 -> modifies (loc_buffer st) h0 h1))
let load_state st b =
    let h0 = ST.get() in
    loop_nospec #h0 (size 16) st 
      (fun i -> st.(i) <- vec128_load_le (sub b (size 16 *. i) (size 16)));
    let st2200 = vec128_interleave_low64
    

inline_for_extraction
val set_counter: st:state -> c:size_t -> ST unit
		  (requires (fun h -> live h st))
   		  (ensures (fun h0 _ h1 -> modifies (loc_buffer st) h0 h1))
let set_counter st c =
    let vff = vec128_load32s (u32 0xffffffff) (u32 0xffffffff) (u32 0xffffffff) (u32 0) in
    let st3 = vec128_and st.(size 3) vff in
    let vc = vec128_load32s (u32 0) (u32 0) (u32 0) (size_to_uint32 c) in
    st.(size 3) <- vec128_or st3 vc

inline_for_extraction
val copy_state: st:state -> ost:state -> ST unit
		  (requires (fun h -> live h st /\ live h ost))
   		  (ensures (fun h0 _ h1 -> modifies (loc_buffer st) h0 h1))
let copy_state st ost =
    blit ost (size 0) st (size 0) (size 16)


inline_for_extraction
val sum_state: st:state -> ost:state -> ST unit
		  (requires (fun h -> live h st /\ live h ost))
   		  (ensures (fun h0 _ h1 -> modifies (loc_buffer st) h0 h1))
let sum_state st ost =
    let h0 = ST.get() in
    loop_nospec #h0 (size 16) st 
      (fun i -> let si = st.(i) in
	     let osi = ost.(i) in
	     st.(i) <- si +. osi)



inline_for_extraction
val xor_block: o:lbytes 64 -> st:state -> b:lbytes 64 -> ST unit
		  (requires (fun h -> live h o /\ live h st /\ live h b))
   		  (ensures (fun h0 _ h1 -> modifies (loc_buffer o) h0 h1))
let xor_block o st b =
    let h0 = ST.get () in
    loop_nospec #h0 (size 16) o 
      (fun i -> 
	let u = load32_le (sub b (i *. size 4) (size 4)) in
        store32_le (sub o (i *. size 4) (size 4)) (u ^. st.(i)))
    
    

inline_for_extraction
val line: st:state -> a:index -> b:index -> d:index -> r:rot32 -> ST unit
		  (requires (fun h -> live h st))
		  (ensures (fun h0 _ h1 -> modifies (loc_buffer st) h0 h1))
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
		  (ensures (fun h0 _ h1 -> modifies (loc_buffer st) h0 h1))
[@ CInline ]
let quarter_round st a b c d = 
    line st a b d (u32 16);
    line st c d b (u32 12);
    line st a b d (u32 8);
    line st c d b (u32 7)

[@ CInline]
val double_round: st:state -> ST unit
		  (requires (fun h -> live h st))
		  (ensures (fun h0 _ h1 -> modifies (loc_buffer st) h0 h1))
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


