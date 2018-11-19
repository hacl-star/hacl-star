module Hacl.Impl.Aes.CoreNI

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer
open Lib.Vec128

type state = lbuffer vec128 4ul
type key1 =  lbuffer vec128 1ul
type nonce =  lbuffer vec128 1ul

inline_for_extraction
val create_state: unit -> StackInline state
                   (requires (fun h -> True))
		   (ensures (fun h0 f h1 -> live h1 f /\ stack_allocated f h0 h1 (Seq.create 4 vec128_zero)))
let create_state () = create (size 4) vec128_zero 


inline_for_extraction
val copy_state: st:state -> ost:state -> ST unit
			     (requires (fun h -> live h st /\ live h ost))
			     (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1))
let copy_state st ost = 
    st.(size 0) <- ost.(size 0);
    st.(size 1) <- ost.(size 1);
    st.(size 2) <- ost.(size 2);
    st.(size 3) <- ost.(size 3)


inline_for_extraction
val load_block0: st:state -> b: lbuffer uint8 16ul -> ST unit
	     (requires (fun h -> live h st /\ live h b))
	     (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1))
let load_block0 st b = st.(size 0) <- vec128_load_le b

inline_for_extraction
val load_key1: k:key1 -> b: lbuffer uint8 16ul -> ST unit
			     (requires (fun h -> live h k /\ live h b))
			     (ensures (fun h0 _ h1 -> modifies (loc k) h0 h1))
let load_key1 k b = k.(size 0) <- vec128_load_le b

inline_for_extraction
val load_nonce: n:nonce -> b: lbuffer uint8 12ul -> ST unit
			     (requires (fun h -> live h n /\ live h b))
			     (ensures (fun h0 _ h1 -> modifies (loc n) h0 h1))
let load_nonce n b =
  push_frame();
  let nb = create 16ul (u8 0) in
  copy (sub nb 0ul 12ul) b;
  n.(size 0) <- vec128_load_le nb;
  pop_frame()



inline_for_extraction
val load_state: st:state -> nonce:nonce -> counter:size_t -> ST unit
			     (requires (fun h -> live h st /\ live h nonce))
			     (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1))
let load_state st nonce counter = 
    let counter0 = secret (to_be counter) in
    let counter1 = secret (to_be (counter +. 1ul)) in
    let counter2 = secret (to_be (counter +. 2ul)) in
    let counter3 = secret (to_be (counter +. 3ul)) in
    st.(size 0) <- vec128_insert32 nonce.(size 0) counter0 (u8 3);
    st.(size 1) <- vec128_insert32 nonce.(size 0) counter1 (u8 3);
    st.(size 2) <- vec128_insert32 nonce.(size 0) counter2 (u8 3);
    st.(size 3) <- vec128_insert32 nonce.(size 0) counter3 (u8 3)

inline_for_extraction
val store_block0: out:lbuffer uint8 16ul -> st:state -> ST unit
			     (requires (fun h -> live h st /\ live h out))
			     (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
let store_block0 out st =
    vec128_store_le out st.(size 0)



inline_for_extraction
val xor_state_key1: st:state -> key:key1 -> ST unit
			     (requires (fun h -> live h st /\ live h key))
			     (ensures (fun h0 _ h1 -> live h1 st /\ live h1 key /\ modifies (loc st) h0 h1))
let xor_state_key1 st key = 
    st.(size 0) <- vec128_xor st.(size 0) key.(size 0);
    st.(size 1) <- vec128_xor st.(size 1) key.(size 0);
    st.(size 2) <- vec128_xor st.(size 2) key.(size 0);
    st.(size 3) <- vec128_xor st.(size 3) key.(size 0)

inline_for_extraction
val xor_block: out:lbuffer uint8 64ul -> st:state -> b:lbuffer uint8 64ul -> ST unit
			     (requires (fun h -> live h st /\ live h out /\ live h b))
			     (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
let xor_block out st inp = 
    let v0 = vec128_load_le (sub inp (size 0) (size 16)) in
    let v1 = vec128_load_le (sub inp (size 16) (size 16)) in
    let v2 = vec128_load_le (sub inp (size 32) (size 16)) in
    let v3 = vec128_load_le (sub inp (size 48) (size 16)) in
    let v0 = vec128_xor v0 st.(size 0) in
    let v1 = vec128_xor v1 st.(size 1) in
    let v2 = vec128_xor v2 st.(size 2) in
    let v3 = vec128_xor v3 st.(size 3) in
    vec128_store_le (sub out (size 0) (size 16)) v0;
    vec128_store_le (sub out (size 16) (size 16)) v1;
    vec128_store_le (sub out (size 32) (size 16)) v2;
    vec128_store_le (sub out (size 48) (size 16)) v3



inline_for_extraction
val aes_enc: st:state -> key:key1 -> ST unit
			     (requires (fun h -> live h st /\ live h key))
			     (ensures (fun h0 _ h1 -> live h1 st /\ live h1 key /\ modifies (loc st) h0 h1))
let aes_enc st key = 
    st.(size 0) <- ni_aes_enc st.(size 0) key.(size 0);
    st.(size 1) <- ni_aes_enc st.(size 1) key.(size 0);
    st.(size 2) <- ni_aes_enc st.(size 2) key.(size 0);
    st.(size 3) <- ni_aes_enc st.(size 3) key.(size 0)

inline_for_extraction
val aes_enc_last: st:state -> key:key1 -> ST unit
			     (requires (fun h -> live h st /\ live h key))
			     (ensures (fun h0 _ h1 -> live h1 st /\ live h1 key /\ modifies (loc st) h0 h1))
let aes_enc_last st key = 
    st.(size 0) <- ni_aes_enc_last st.(size 0) key.(size 0);
    st.(size 1) <- ni_aes_enc_last st.(size 1) key.(size 0);
    st.(size 2) <- ni_aes_enc_last st.(size 2) key.(size 0);
    st.(size 3) <- ni_aes_enc_last st.(size 3) key.(size 0)

inline_for_extraction
val aes_keygen_assist: ok:key1 -> ik:key1 -> rcon:uint8 -> ST unit
			     (requires (fun h -> live h ok /\ live h ik))
			     (ensures (fun h0 _ h1 -> live h1 ok /\ live h1 ik /\ modifies (loc ok) h0 h1))
let aes_keygen_assist ok ik rcon = 
    ok.(size 0) <- ni_aes_keygen_assist ik.(size 0) rcon		      


inline_for_extraction 
val key_expansion_step: next:key1 -> prev:key1 -> ST unit
			     (requires (fun h -> live h prev /\ live h next))
			     (ensures (fun h0 _ h1 -> live h1 prev /\ live h1 next /\ modifies (loc next) h0 h1))
let key_expansion_step next prev = 
    let n0 = next.(size 0) in
    next.(size 0) <- vec128_shuffle32 n0 (vec128_shuffle32_spec (u8 3) (u8 3) (u8 3) (u8 3));
    let key = prev.(size 0) in
    let key = vec128_xor key (vec128_shift_left key (size 32)) in
    let key = vec128_xor key (vec128_shift_left key (size 32)) in
    let key = vec128_xor key (vec128_shift_left key (size 32)) in
    next.(size 0) <- vec128_xor next.(size 0) key


inline_for_extraction 
val key_expansion_step2: next:key1 -> prev:key1 -> ST unit
			     (requires (fun h -> live h prev /\ live h next))
			     (ensures (fun h0 _ h1 -> live h1 prev /\ live h1 next /\ modifies (loc next) h0 h1))
let key_expansion_step2 next prev = 
    next.(size 0) <- vec128_shuffle32 next.(size 0) (vec128_shuffle32_spec (u8 2) (u8 2) (u8 2) (u8 2));
    let key = prev.(size 0) in
    let key = vec128_xor key (vec128_shift_left key (size 32)) in
    let key = vec128_xor key (vec128_shift_left key (size 32)) in
    let key = vec128_xor key (vec128_shift_left key (size 32)) in
    next.(size 0) <- vec128_xor next.(size 0) key


