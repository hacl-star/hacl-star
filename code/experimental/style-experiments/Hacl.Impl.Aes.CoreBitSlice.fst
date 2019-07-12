module Hacl.Impl.Aes.CoreBitSlice

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open LowStar.Buffer
open Lib.Utils
open Lib.Vec128
open Hacl.Spec.Aes.BitSlice
type state = lbuffer uint64 8
type key1 =  lbuffer uint64 8
type nonce =  lbuffer uint64 8

type block = lbytes 16
type block4 = lbytes 64

inline_for_extraction
val create_state: unit -> StackInline state
                   (requires (fun h -> True))
		   (ensures (fun h0 f h1 -> live h1 f))
let create_state() = create (u64 0) (size 8)

inline_for_extraction
val copy_state: next:state -> prev:state -> ST unit
			     (requires (fun h -> live h prev /\ live h next))
			     (ensures (fun h0 _ h1 -> live h1 prev /\ live h1 next /\ modifies (loc_buffer next) h0 h1))
let copy_state next prev = 
    blit prev (size 0) next (size 0) (size 8)

val load_block: out:state -> inp:block -> ST unit 
			        (requires (fun h -> live h out /\ live h inp))
				(ensures (fun h0 _ h1 -> live h1 out /\ live h1 inp /\ modifies (loc_buffer out) h0 h1))
let load_block (out:state) (inp:block) = 
  let b1 : lbytes 8 = sub inp (size 0) (size 8) in
  let b2 : lbytes 8 = sub inp (size 8) (size 8) in
  let fst = load64_le b1 in
  let snd = load64_le b2 in 
  let fst = transpose_bits64 fst in
  let snd = transpose_bits64 snd in
  let h0 = ST.get() in
  loop_nospec #h0 #uint64 (size 8) out 
    (fun i -> 
      let sh = size_to_uint32 (i *. size 8) in
      let u = (fst >>. sh) &. u64 0xff in
      let u = u ^. (((snd >>. sh) &. u64 0xff) <<. u32 8) in
      out.(i) <- u)


val transpose_state: st:state -> ST unit 
			        (requires (fun h -> live h st))
				(ensures (fun h0 _ h1 -> live h1 st /\ modifies (loc_buffer st) h0 h1))
let transpose_state st = 
  let i0 = st.(size 0) in
  let i1 = st.(size 1) in
  let i2 = st.(size 2) in
  let i3 = st.(size 3) in
  let i4 = st.(size 4) in
  let i5 = st.(size 5) in
  let i6 = st.(size 6) in
  let i7 = st.(size 7) in  
  let (t0,t1,t2,t3,t4,t5,t6,t7) = 
    transpose_bits64x8 i0 i1 i2 i3 i4 i5 i6 i7 in
  st.(size 0) <- t0;
  st.(size 1) <- t1;
  st.(size 2) <- t2;
  st.(size 3) <- t3;
  st.(size 4) <- t4;
  st.(size 5) <- t5;
  st.(size 6) <- t6;
  st.(size 7) <- t7


val store_block0: out:block -> inp:state -> ST unit 
			        (requires (fun h -> live h out /\ live h inp))
				(ensures (fun h0 _ h1 -> live h1 out /\ live h1 inp /\ modifies (loc_buffer out) h0 h1))
let store_block0 out (inp:state) = 
  let (t0,t1,t2,t3,t4,t5,t6,t7) = transpose_bits64x8
				  inp.(size 0)
				  inp.(size 1)
				  inp.(size 2)
				  inp.(size 3)
				  inp.(size 4)
				  inp.(size 5)
				  inp.(size 6)
				  inp.(size 7) in
  store64_le (sub out (size 0) (size 8)) t0;
  store64_le (sub out (size 8) (size 8)) t1


val load_key1: out:key1 -> k:block -> ST unit 
	        (requires (fun h -> live h out /\ live h k))
		(ensures (fun h0 _ h1 -> live h1 out /\ live h1 k /\ modifies (loc_buffer out) h0 h1))
let load_key1 (out:state) (k:block) = 
  load_block out k;
  let h0 = ST.get() in
  loop_nospec #h0 (size 8) out 
    (fun i -> 
      let u = out.(i) in
      let u = u ^. (u <<. u32 16) in
      let u = u ^. (u <<. u32 32) in
      out.(i) <- u)


val load_nonce: out:nonce -> nonce:lbytes 12 -> ST unit 
			        (requires (fun h -> live h out /\ live h nonce))
				(ensures (fun h0 _ h1 -> live h1 out /\ live h1 nonce /\ modifies (loc_buffer out) h0 h1))
let load_nonce (out:state) (n:lbytes 12) = 
  push_frame();
  let nb = alloca 0uy 16ul in
  blit n (size 0) nb (size 0) (size 12);
  load_key1 out nb;
  pop_frame()    


val load_state: out:state -> nonce:nonce -> counter:size_t -> ST unit 
	        (requires (fun h -> live h out /\ live h nonce))
		(ensures (fun h0 _ h1 -> modifies (loc_buffer out) h0 h1))
let load_state (out:state) (nonce:nonce) (counter:size_t) = 
  push_frame();
  let counter = size_to_uint32 counter in
  let ctr = alloca 0uy 16ul in
  store32_be  (sub ctr (size 0) (size 4)) counter;
  store32_be  (sub ctr (size 4) (size 4)) (counter +. u32 1);
  store32_be  (sub ctr (size 8) (size 4)) (counter +. u32 2);
  store32_be  (sub ctr (size 12) (size 4)) (counter +. u32 3);
  load_block out ctr;
  let h0 = ST.get() in
  loop_nospec #h0 (size 8) out 
    (fun i -> 
      let u = out.(i) in
      let u = (u <<. u32 12) |. (u <<. u32 24) |. (u <<. u32 36) |. (u <<. u32 48) in 
      let u = u &. u64 0xf000f000f000f000 in
      out.(i) <- u ^. nonce.(i))


val xor_state_key1: st:state -> ost:state -> ST unit
	     (requires (fun h -> live h st /\ live h ost))
	     (ensures (fun h0 _ h1 -> live h1 st /\ live h1 ost /\ modifies (loc_buffer st) h0 h1))
let xor_state_key1 st ost =
    let h0 = ST.get() in
    loop_nospec #h0 (size 8) st 
      (fun i -> st.(i) <- st.(i) ^. ost.(i))

inline_for_extraction
val xor_block: out:lbytes 64 -> st:state -> b:lbytes 64 -> ST unit
			     (requires (fun h -> live h st /\ live h out /\ live h b))
			     (ensures (fun h0 _ h1 -> modifies (loc_buffer out) h0 h1))
let xor_block out st inp = 
  transpose_state st;
  let h0 = ST.get() in
  loop_nospec #h0 (size 8) out
     (fun j -> 
       let ob = sub out (j *. size 8) (size 8) in
       let ib = sub inp (j *. size 8) (size 8) in
       let u = load64_le ib in
       store64_le ob (u ^. st.(j)))
       

val sub_bytes_state: st:state -> ST unit
			     (requires (fun h -> live h st))
			     (ensures (fun h0 _ h1 -> live h1 st /\ modifies (loc_buffer st) h0 h1))
let sub_bytes_state (st:state) = 
  let (st0,st1,st2,st3,st4,st5,st6,st7) = sub_bytes64x8 st.(size 0) st.(size 1)
					           st.(size 2) st.(size 3)
						   st.(size 4) st.(size 5)
						   st.(size 6) st.(size 7) in
  st.(size 0) <- st0;
  st.(size 1) <- st1;
  st.(size 2) <- st2;
  st.(size 3) <- st3;
  st.(size 4) <- st4;
  st.(size 5) <- st5;
  st.(size 6) <- st6;
  st.(size 7) <- st7

val shift_rows_state: st:state -> ST unit
			     (requires (fun h -> live h st))
			     (ensures (fun h0 _ h1 -> live h1 st /\ modifies (loc_buffer st) h0 h1))
let shift_rows_state st = 
    let h0 = ST.get() in
    loop_nospec #h0 (size 8) st 
      (fun i -> st.(i) <- let rowi = st.(i) in shift_row64 rowi)


val mix_columns_state: st:state -> ST unit
			     (requires (fun h -> live h st))
			     (ensures (fun h0 _ h1 -> live h1 st /\ modifies (loc_buffer st) h0 h1))
let mix_columns_state st = 
    push_frame () ;
    let col = alloca (u64 0) 8ul in
    let h0 = ST.get() in
    loop_nospec #h0 (size 8) st 
      (fun i -> 
	 let coli = st.(i) in
	 col.(i) <- coli ^. (((coli &. u64 0xeeeeeeeeeeeeeeee) >>. u32 1) 
                |. ((coli &. u64 0x1111111111111111) <<. u32 3)));
    let col0 = col.(size 0) in
    let ncol0 = col0 ^. (((col0 &. u64 0xcccccccccccccccc ) >>. u32  2)
		  |. ((col0 &. u64 0x3333333333333333) <<. u32  2)) in
    st.(size 0) <- st.(size 0) ^. ncol0;
    loop_nospec #h0 (size 7) st 
      (fun i -> 
         let prev = col.(i) in
         let next = col.(i +. size 1) in
         let ncoli = next ^. (((next &. u64 0xcccccccccccccccc ) >>. u32  2)
		  |. ((next &. u64 0x3333333333333333) <<. u32  2)) in
	 st.(i +. size 1) <- st.(i +. size 1) ^. ncoli ^. prev);
    st.(size 0) <- st.(size 0) ^. col.(size 7);
    st.(size 1) <- st.(size 1) ^. col.(size 7);
    st.(size 3) <- st.(size 3) ^. col.(size 7);
    st.(size 4) <- st.(size 4) ^. col.(size 7);
    pop_frame()


val aes_enc: st:state -> key:key1 -> ST unit
			     (requires (fun h -> live h st /\ live h key))
			     (ensures (fun h0 _ h1 -> live h1 st /\ live h1 key /\ modifies (loc_buffer st) h0 h1))
let aes_enc st key = 
    sub_bytes_state st;
    shift_rows_state st;
    mix_columns_state st;
    xor_state_key1 st key


val aes_enc_last: st:state -> key:key1 -> ST unit
			     (requires (fun h -> live h st /\ live h key))
			     (ensures (fun h0 _ h1 -> live h1 st /\ live h1 key /\ modifies (loc_buffer st) h0 h1))
let aes_enc_last st key = 
    sub_bytes_state st;
    shift_rows_state st;
    xor_state_key1 st key

let rcon =  gcreateL [u8(0x8d); u8(0x01); u8(0x02); u8(0x04); u8(0x08); u8(0x10); u8(0x20); u8(0x40); u8(0x80); u8(0x1b); u8(0x36)]

inline_for_extraction 
val aes_keygen_assisti: rcon:uint8 -> i:size_t -> u:uint64 -> uint64
let aes_keygen_assisti rcon i u = 
    let n = (u &. u64 0xf000f000f000f000) >>. u32 12 in
    let n = ((n >>. u32 1) |. (n <<. u32 3)) &. u64  0x000f000f000f000f in
    let ri = to_u64 ((rcon >>. size_to_uint32 i) &. u8 1) in
    let ri = ri ^. (ri <<. u32 16) in
    let ri = ri ^. (ri <<. u32 32) in
    let n = n ^. ri in
    let n = n <<. u32 12 in
    n
    
val aes_keygen_assist: next:state -> prev:state -> rcon:uint8 -> ST unit
			     (requires (fun h -> live h next /\ live h prev))
			     (ensures (fun h0 _ h1 -> modifies (loc_buffer next) h0 h1))
let aes_keygen_assist next prev rcon = 
    copy_state next prev;
    sub_bytes_state next;
    let h0 = ST.get() in
    loop_nospec #h0 (size 8) next
      (fun i -> next.(i) <- aes_keygen_assisti rcon i next.(i))

inline_for_extraction 
let key_expand1 (p:uint64) (n:uint64) = 
      let n = (n &. u64 0xf000f000f000f000) in
      let n = n ^. (n >>. u32 4) in
      let n = n ^. (n >>. u32 8) in
      let p = p ^. ((p &. u64 0x0fff0fff0fff0fff) <<. u32 4) ^. ((p &. u64 0x00ff00ff00ff00ff) <<. u32 8)
      ^. ((p &. u64 0x000f000f000f000f) <<. u32 12) in
      n ^. p

inline_for_extraction 
val key_expansion_step: next:state -> prev:state -> ST unit
			     (requires (fun h -> live h prev /\ live h next))
			     (ensures (fun h0 _ h1 -> live h1 prev /\ live h1 next /\ modifies (loc_buffer next) h0 h1))
let key_expansion_step next prev = 
    let h0 = ST.get() in
    loop_nospec #h0 (size 8) next 
      (fun i -> next.(i) <- let p = prev.(i) in let n = next.(i) in key_expand1 p n)


