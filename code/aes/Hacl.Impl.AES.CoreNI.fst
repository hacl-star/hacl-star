module Hacl.Impl.AES.CoreNI

open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer
open Lib.IntVector

module ST = FStar.HyperStack.ST

inline_for_extraction noextract
let vec128 = vec_t U128 1
inline_for_extraction noextract
let vec128_zero = vec_zero U128 1

type state = lbuffer vec128 4ul
type key1 =  lbuffer vec128 1ul
type nonce =  lbuffer vec128 1ul


inline_for_extraction noextract
val create_state: unit ->
  StackInline state
  (requires (fun h -> True))
  (ensures (fun h0 f h1 -> live h1 f /\ stack_allocated f h0 h1 (Seq.create 4 vec128_zero)))

let create_state () = create (size 4) vec128_zero


inline_for_extraction noextract
val copy_state:
    st: state
  -> ost: state ->
  Stack unit
  (requires (fun h -> live h st /\ live h ost))
  (ensures (fun h0 _ h1 -> modifies1 st h0 h1))

let copy_state st ost =
  st.(size 0) <- ost.(size 0);
  st.(size 1) <- ost.(size 1);
  st.(size 2) <- ost.(size 2);
  st.(size 3) <- ost.(size 3)


inline_for_extraction noextract
val load_block0:
    st: state
  -> b: lbuffer uint8 16ul ->
  Stack unit
  (requires (fun h -> live h st /\ live h b))
  (ensures  (fun h0 _ h1 -> modifies1 st h0 h1))

let load_block0 st b = st.(size 0) <- vec_load_le U128 1 b


inline_for_extraction noextract
val load_key1:
    k: key1
  -> b: lbuffer uint8 16ul ->
  Stack unit
  (requires (fun h -> live h k /\ live h b))
  (ensures (fun h0 _ h1 -> modifies1 k h0 h1))

let load_key1 k b = k.(size 0) <- vec_load_le U128 1 b


inline_for_extraction noextract
val load_nonce:
    n: nonce
  -> b: lbuffer uint8 12ul ->
  Stack unit
  (requires (fun h -> live h n /\ live h b))
  (ensures (fun h0 _ h1 -> modifies1 n h0 h1))

let load_nonce n b =
  push_frame();
  let nb = create 16ul (u8 0) in
  copy (sub nb 0ul 12ul) b;
  n.(size 0) <- vec_load_le U128 1 nb;
  pop_frame()


inline_for_extraction noextract
val load_state:
    st: state
  -> nonce: nonce
  -> counter: size_t ->
  Stack unit
  (requires (fun h -> live h st /\ live h nonce))
  (ensures (fun h0 _ h1 -> modifies1 st h0 h1))

let load_state st nonce counter =
  let counter = secret counter in
  let counter0 = Lib.ByteBuffer.uint_to_be counter in
  let counter1 = Lib.ByteBuffer.uint_to_be (counter +. u32 1) in
  let counter2 = Lib.ByteBuffer.uint_to_be (counter +. u32 2) in
  let counter3 = Lib.ByteBuffer.uint_to_be (counter +. u32 3) in

  let nonce0 = nonce.(size 0) in
  st.(size 0) <- cast U128 1 (vec_set #U32 #4 (cast #U128 #1 U32 4 nonce0) 3ul counter0);
  st.(size 1) <- cast U128 1 (vec_set #U32 #4 (cast #U128 #1 U32 4 nonce0) 3ul counter1);
  st.(size 2) <- cast U128 1 (vec_set #U32 #4 (cast #U128 #1 U32 4 nonce0) 3ul counter2);
  st.(size 3) <- cast U128 1 (vec_set #U32 #4 (cast #U128 #1 U32 4 nonce0) 3ul counter3)

inline_for_extraction noextract
val store_block0:
    out: lbuffer uint8 16ul
  -> st: state ->
  Stack unit
  (requires (fun h -> live h st /\ live h out))
  (ensures (fun h0 _ h1 -> modifies1 out h0 h1))

let store_block0 out st =
  vec_store_le out st.(size 0)


inline_for_extraction noextract
val xor_state_key1:
    st: state
  -> key: key1 ->
  Stack unit
  (requires (fun h -> live h st /\ live h key))
  (ensures (fun h0 _ h1 -> modifies1 st h0 h1))

let xor_state_key1 st key =
  st.(size 0) <- vec_xor st.(size 0) key.(size 0);
  st.(size 1) <- vec_xor st.(size 1) key.(size 0);
  st.(size 2) <- vec_xor st.(size 2) key.(size 0);
  st.(size 3) <- vec_xor st.(size 3) key.(size 0)


inline_for_extraction noextract
val xor_block:
    out: lbuffer uint8 64ul
  -> st: state
  -> b: lbuffer uint8 64ul ->
  Stack unit
  (requires (fun h -> live h st /\ live h out /\ live h b))
  (ensures (fun h0 _ h1 -> modifies1 out h0 h1))

let xor_block out st inp =
  let v0 = vec_load_le U128 1 (sub inp (size 0) (size 16)) in
  let v1 = vec_load_le U128 1 (sub inp (size 16) (size 16)) in
  let v2 = vec_load_le U128 1 (sub inp (size 32) (size 16)) in
  let v3 = vec_load_le U128 1 (sub inp (size 48) (size 16)) in
  let v0 = vec_xor v0 st.(size 0) in
  let v1 = vec_xor v1 st.(size 1) in
  let v2 = vec_xor v2 st.(size 2) in
  let v3 = vec_xor v3 st.(size 3) in
  vec_store_le (sub out (size 0) (size 16)) v0;
  vec_store_le (sub out (size 16) (size 16)) v1;
  vec_store_le (sub out (size 32) (size 16)) v2;
  vec_store_le (sub out (size 48) (size 16)) v3


inline_for_extraction noextract
val aes_enc:
    st: state
  -> key: key1 ->
  Stack unit
  (requires (fun h -> live h st /\ live h key))
  (ensures (fun h0 _ h1 -> modifies1 st h0 h1))

let aes_enc st key =
  st.(size 0) <- cast U128 1 (vec_aes_enc (cast U8 16 st.(size 0)) (cast U8 16 key.(size 0)));
  st.(size 1) <- cast U128 1 (vec_aes_enc (cast U8 16 st.(size 1)) (cast U8 16 key.(size 0)));
  st.(size 2) <- cast U128 1 (vec_aes_enc (cast U8 16 st.(size 2)) (cast U8 16 key.(size 0)));
  st.(size 3) <- cast U128 1 (vec_aes_enc (cast U8 16 st.(size 3)) (cast U8 16 key.(size 0)))


inline_for_extraction noextract
val aes_enc_last:
    st: state
  -> key: key1 ->
  Stack unit
  (requires (fun h -> live h st /\ live h key))
  (ensures (fun h0 _ h1 -> modifies1 st h0 h1))

let aes_enc_last st key =
  st.(size 0) <- cast U128 1 (vec_aes_enc_last (cast U8 16 st.(size 0)) (cast U8 16 key.(size 0)));
  st.(size 1) <- cast U128 1 (vec_aes_enc_last (cast U8 16 st.(size 1)) (cast U8 16 key.(size 0)));
  st.(size 2) <- cast U128 1 (vec_aes_enc_last (cast U8 16 st.(size 2)) (cast U8 16 key.(size 0)));
  st.(size 3) <- cast U128 1 (vec_aes_enc_last (cast U8 16 st.(size 3)) (cast U8 16 key.(size 0)))


inline_for_extraction noextract
val aes_keygen_assist0:
    ok: key1
  -> ik: key1
  -> rcon: uint8 ->
  Stack unit
  (requires (fun h -> live h ok /\ live h ik))
  (ensures (fun h0 _ h1 -> modifies1 ok h0 h1))

let aes_keygen_assist0 ok ik rcon =
  let v = cast U128 1 (vec_aes_keygen_assist (cast U8 16 ik.(size 0)) rcon) in
  ok.(size 0) <- cast U128 1 (vec_permute4 (cast U32 4 v) 3ul 3ul 3ul 3ul)

inline_for_extraction noextract
val aes_keygen_assist1:
    ok: key1
  -> ik: key1 ->
  Stack unit
  (requires (fun h -> live h ok /\ live h ik))
  (ensures (fun h0 _ h1 -> modifies1 ok h0 h1))

let aes_keygen_assist1 ok ik =
  let v = cast U128 1 (vec_aes_keygen_assist (cast U8 16 ik.(size 0)) (u8 0)) in
  ok.(size 0) <- cast U128 1 (vec_permute4 (cast U32 4 v) 2ul 2ul 2ul 2ul)


inline_for_extraction noextract
val key_expansion_step:
    next: key1
  -> prev: key1 ->
  Stack unit
  (requires (fun h -> live h prev /\ live h next))
  (ensures (fun h0 _ h1 -> modifies1 next h0 h1))

let key_expansion_step next prev =
  let n0 = next.(size 0) in
  let key = prev.(size 0) in
  let key = vec_xor key (vec_shift_left key (size 32)) in
  let key = vec_xor key (vec_shift_left key (size 32)) in
  let key = vec_xor key (vec_shift_left key (size 32)) in
  next.(size 0) <- vec_xor next.(size 0) key
