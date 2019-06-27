module Hacl.Impl.AES.CoreBitSlice

open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Hacl.Spec.AES_128.BitSlice

module ST = FStar.HyperStack.ST




type state = lbuffer uint64 8ul
type key1 =  lbuffer uint64 8ul
type nonce =  lbuffer uint64 8ul

type block = lbuffer uint8 16ul
type block4 = lbuffer uint8 64ul


inline_for_extraction
val create_state: unit ->
  StackInline state
  (requires (fun h -> True))
  (ensures (fun h0 f h1 -> live h1 f /\ stack_allocated f h0 h1 (Seq.create 8 (u64 0))))

let create_state() = create 8ul (u64 0)


inline_for_extraction
val copy_state:
    next: state
  -> prev: state ->
  Stack unit
  (requires (fun h -> live h prev /\ live h next /\ disjoint next prev))
  (ensures (fun h0 _ h1 -> modifies1 next h0 h1))

let copy_state next prev = copy next prev


val load_block0:
    out: state
  -> inp: block ->
  ST unit
  (requires (fun h -> live h out /\ live h inp))
  (ensures (fun h0 _ h1 -> modifies1 out h0 h1))

let load_block0 (out:state) (inp:block) =
  let b1 = sub inp (size 0) (size 8) in
  let b2 = sub inp (size 8) (size 8) in
  let fst = uint_from_bytes_le #U64 b1 in
  let snd = uint_from_bytes_le #U64 b2 in
  let fst = transpose_bits64 fst in
  let snd = transpose_bits64 snd in
  let h0 = ST.get() in
  Lib.Buffer.loop_nospec #h0 (size 8) out
    (fun i ->
      let sh = i *. (size 8) in
      let u = (fst >>. sh) &. u64 0xff in
      let u = u ^. (((snd >>. sh) &. u64 0xff) <<. size 8) in
      out.(i) <- u)


val transpose_state:
  st: state ->
  Stack unit
  (requires (fun h -> live h st))
  (ensures (fun h0 _ h1 -> modifies1 st h0 h1))

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


val store_block0:
    out: block
  -> inp: state ->
  Stack unit
  (requires (fun h -> live h out /\ live h inp))
  (ensures (fun h0 _ h1 -> modifies1 out h0 h1))

let store_block0 out (inp:state) =
  let i0 = inp.(0ul) in
  let i1 = inp.(1ul) in
  let i2 = inp.(2ul) in
  let i3 = inp.(3ul) in
  let i4 = inp.(4ul) in
  let i5 = inp.(5ul) in
  let i6 = inp.(6ul) in
  let i7 = inp.(7ul) in
  let (t0,t1,t2,t3,t4,t5,t6,t7) =
    transpose_bits64x8 i0 i1 i2 i3 i4 i5 i6 i7
  in
  uint_to_bytes_le #U64 (sub out (size 0) (size 8)) t0;
  uint_to_bytes_le #U64 (sub out (size 8) (size 8)) t1


val load_key1:
    out: key1
  -> k: block ->
  Stack unit
  (requires (fun h -> live h out /\ live h k))
  (ensures (fun h0 _ h1 -> modifies1 out h0 h1))

let load_key1 (out:state) (k:block) =
  load_block0 out k;
  let h0 = ST.get() in
  loop_nospec #h0 (size 8) out
    (fun i ->
      let u = out.(i) in
      let u = u ^. (u <<. size 16) in
      let u = u ^. (u <<. size 32) in
      out.(i) <- u)


val load_nonce:
    out: nonce
  -> nonce: lbuffer uint8 12ul ->
  Stack unit
  (requires (fun h -> live h out /\ live h nonce))
  (ensures (fun h0 _ h1 -> modifies1 out h0 h1))

let load_nonce out nonce =
  push_frame();
  let nb = create 16ul (u8 0) in
  copy (sub nb 0ul 12ul) nonce;
  load_key1 out nb;
  pop_frame()


#set-options "--z3rlimit 100"

val load_state:
    out: state
  -> nonce: nonce
  -> counter: size_t ->
  Stack unit
  (requires (fun h -> live h out /\ live h nonce))
  (ensures (fun h0 _ h1 -> modifies1 out h0 h1))

let load_state out nonce counter =
  push_frame();
  let ctr = create 16ul (u8 0) in
  uint_to_bytes_be #U32  (sub ctr (size 0) (size 4)) (secret counter);
  uint_to_bytes_be #U32  (sub ctr (size 4) (size 4)) (secret (counter +. 1ul));
  uint_to_bytes_be #U32  (sub ctr (size 8) (size 4)) (secret (counter +. 2ul));
  uint_to_bytes_be #U32  (sub ctr (size 12) (size 4)) (secret (counter +. 3ul));
  load_block0 out ctr;
  let h0 = ST.get() in
  loop_nospec #h0 (size 8) out
    (fun i ->
      let u = out.(i) in
      let u = (u <<. size 12) |. (u <<. size 24) |. (u <<. size 36) |. (u <<. size 48) in
      let u = u &. u64 0xf000f000f000f000 in
      out.(i) <- u ^. nonce.(i));
  pop_frame ()


val xor_state_key1:
    st: state
  -> ost: state ->
  Stack unit
  (requires (fun h -> live h st /\ live h ost))
  (ensures (fun h0 _ h1 -> modifies1 st h0 h1))

let xor_state_key1 st ost =
  let h0 = ST.get() in
  loop_nospec #h0 (size 8) st
    (fun i -> st.(i) <- st.(i) ^. ost.(i))


val xor_block:
    out: lbuffer uint8 64ul
  -> st: state
  -> b: lbuffer uint8 64ul ->
  Stack unit
  (requires (fun h -> live h st /\ live h out /\ live h b))
  (ensures (fun h0 _ h1 -> modifies2 out st h0 h1))

let xor_block out st inp =
  transpose_state st;
  let h1 = ST.get () in
  loop_nospec #h1 (size 8) out
    (fun j ->
      let ob = sub out (j *. size 8) (size 8) in
      let ib = sub inp (j *. size 8) (size 8) in
      let u = uint_from_bytes_le #U64 ib in
      uint_to_bytes_le #U64 ob (u ^. st.(j)))


val sub_bytes_state:
  st: state ->
  Stack unit
  (requires (fun h -> live h st))
  (ensures (fun h0 _ h1 -> modifies1 st h0 h1))

let sub_bytes_state (st:state) =
  let (st0,st1,st2,st3,st4,st5,st6,st7) =
    sub_bytes64x8 st.(size 0) st.(size 1) st.(size 2) st.(size 3)
						st.(size 4) st.(size 5) st.(size 6) st.(size 7)
  in
  st.(size 0) <- st0;
  st.(size 1) <- st1;
  st.(size 2) <- st2;
  st.(size 3) <- st3;
  st.(size 4) <- st4;
  st.(size 5) <- st5;
  st.(size 6) <- st6;
  st.(size 7) <- st7


val shift_rows_state:
  st: state ->
  Stack unit
  (requires (fun h -> live h st))
  (ensures (fun h0 _ h1 -> modifies1 st h0 h1))

let shift_rows_state st =
  let h0 = ST.get() in
  loop_nospec #h0 (size 8) st
    (fun i -> st.(i) <- let rowi = st.(i) in shift_row64 rowi)


val mix_columns_state:
  st: state ->
  Stack unit
  (requires (fun h -> live h st))
  (ensures (fun h0 _ h1 -> modifies1 st h0 h1))

let mix_columns_state st =
  push_frame () ;
  let col = create 8ul (u64 0) in
  let h0 = ST.get() in
  loop_nospec #h0 (size 8) col (fun i ->
	 let coli = st.(i) in
	 col.(i) <- coli ^. (((coli &. u64 0xeeeeeeeeeeeeeeee) >>. size 1)
                |. ((coli &. u64 0x1111111111111111) <<. size 3)));
  let col0 = col.(size 0) in
  let ncol0 = col0 ^. (((col0 &. u64 0xcccccccccccccccc ) >>. size  2)
		      |. ((col0 &. u64 0x3333333333333333) <<. size  2)) in
  st.(size 0) <- st.(size 0) ^. ncol0;
  let h0 = ST.get() in
  loop_nospec #h0 (size 7) st (fun i ->
    let prev = col.(i) in
    let next = col.(i +. size 1) in
    let ncoli = next ^. (((next &. u64 0xcccccccccccccccc ) >>. size  2)
		               |. ((next &. u64 0x3333333333333333) <<. size  2)) in
  st.(i +. size 1) <- st.(i +. size 1) ^. ncoli ^. prev);
  st.(size 0) <- st.(size 0) ^. col.(size 7);
  st.(size 1) <- st.(size 1) ^. col.(size 7);
  st.(size 3) <- st.(size 3) ^. col.(size 7);
  st.(size 4) <- st.(size 4) ^. col.(size 7);
  pop_frame()


val aes_enc:
    st: state
  -> key: key1 ->
  Stack unit
  (requires (fun h -> live h st /\ live h key))
  (ensures (fun h0 _ h1 -> modifies1 st h0 h1))

let aes_enc st key =
  sub_bytes_state st;
  shift_rows_state st;
  mix_columns_state st;
  xor_state_key1 st key


val aes_enc_last:
    st: state
  -> key: key1 ->
  Stack unit
  (requires (fun h -> live h st /\ live h key))
  (ensures (fun h0 _ h1 -> modifies1 st h0 h1))

let aes_enc_last st key =
  sub_bytes_state st;
  shift_rows_state st;
  xor_state_key1 st key


let rcon : b:ilbuffer uint8 11ul =
  [@ inline_let]
  let rcon_l = [
    u8(0x8d); u8(0x01); u8(0x02); u8(0x04);
    u8(0x08); u8(0x10); u8(0x20); u8(0x40);
    u8(0x80); u8(0x1b); u8(0x36)
  ] in
  assert_norm (List.Tot.length rcon_l == 11);
  createL_global rcon_l


inline_for_extraction
val aes_keygen_assisti: rcon:uint8 -> i:shiftval U8 -> u:uint64 -> Tot uint64
let aes_keygen_assisti rcon i u =
  let u3 = u &. u64 0xf000f000f000f000 in
  let n = u3 >>. size 12 in
  let n = ((n >>. size 1) |. (n <<. size 3)) &. u64  0x000f000f000f000f in
  let ri = to_u64 ((rcon >>. i) &. u8 1) in
  let ri = ri ^. (ri <<. size 16) in
  let ri = ri ^. (ri <<. size 32) in
  let n = n ^. ri in
  let n = n <<. size 12 in
  n ^. (u3 >>. 4ul)


val aes_keygen_assist:
    next: state
  -> prev: state
  -> rcon: uint8 ->
  Stack unit
  (requires (fun h -> live h next /\ live h prev /\ disjoint next prev))
  (ensures (fun h0 _ h1 -> modifies1 next h0 h1))

let aes_keygen_assist next prev rcon =
  copy_state next prev;
  sub_bytes_state next;
  let h0 = ST.get() in
  loop_nospec #h0 (size 8) next
    (fun i -> next.(i) <- aes_keygen_assisti rcon i next.(i))


inline_for_extraction
val aes_keygen_assist0:
    next: state
  -> prev: state
  -> rcon: uint8 ->
  Stack unit
  (requires (fun h -> live h next /\ live h prev /\ disjoint next prev))
  (ensures (fun h0 _ h1 -> modifies1 next h0 h1))

let aes_keygen_assist0 next prev rcon =
  aes_keygen_assist next prev rcon;
  let h0 = ST.get() in
  loop_nospec #h0 (size 8) next
    (fun i -> let n = next.(i) in
           let n = (n &. u64 0xf000f000f000f000) in
	   let n = n ^. (n >>. size 4) in
	   let n = n ^. (n >>. size 8) in
	   next.(i) <- n)

inline_for_extraction
val aes_keygen_assist1:
    next: state
  -> prev: state ->
  Stack unit
  (requires (fun h -> live h next /\ live h prev /\ disjoint next prev))
  (ensures (fun h0 _ h1 -> modifies1 next h0 h1))

let aes_keygen_assist1 next prev =
  aes_keygen_assist next prev (u8 0);
  let h0 = ST.get() in
  loop_nospec #h0 (size 8) next
    (fun i -> let n = next.(i) in
           let n = (n &. u64 0x0f000f000f000f00) in
	   let n = n ^. (n <<. size 4) in
	   let n = n ^. (n >>. size 8) in
	   next.(i) <- n)

inline_for_extraction
let key_expand1 (p:uint64) (n:uint64) =
  let p = p ^. ((p &. u64 0x0fff0fff0fff0fff) <<. size 4) ^. ((p &. u64 0x00ff00ff00ff00ff) <<. size 8)
            ^. ((p &. u64 0x000f000f000f000f) <<. size 12) in
  n ^. p


val key_expansion_step:
    next: state
  -> prev: state ->
  ST unit
  (requires (fun h -> live h prev /\ live h next))
  (ensures (fun h0 _ h1 -> modifies1 next h0 h1))

let key_expansion_step next prev =
  let h0 = ST.get() in
  loop_nospec #h0 (size 8) next
    (fun i -> next.(i) <- let p = prev.(i) in let n = next.(i) in key_expand1 p n)
