module Hacl.Impl.AES.CoreNI

open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer
open Lib.IntVector
open Lib.ByteSequence

open Hacl.AES.Common
open Hacl.AES.CoreNI.Lemmas

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence

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
  (requires (fun h -> live h st /\ live h ost /\ disjoint st ost))
  (ensures (fun h0 _ h1 -> modifies1 st h0 h1 /\ as_seq h1 st == as_seq h0 ost))

let copy_state st ost =
  let h0 = ST.get() in
  st.(size 0) <- ost.(size 0);
  st.(size 1) <- ost.(size 1);
  st.(size 2) <- ost.(size 2);
  st.(size 3) <- ost.(size 3);
  let h1 = ST.get() in
  LSeq.eq_intro (as_seq h1 st) (as_seq h0 ost)


inline_for_extraction noextract
val load_block0:
    st: state
  -> b: lbuffer uint8 16ul ->
  Stack unit
  (requires (fun h -> live h st /\ live h b /\ disjoint st b))
  (ensures  (fun h0 _ h1 -> modifies1 st h0 h1 /\
    (let st' = as_seq h1 st in
    u8_16_to_le (uints_to_bytes_be (vec_v (LSeq.index st' 0))) == as_seq h0 b /\
    LSeq.index st' 1 == LSeq.index (as_seq h0 st) 1 /\
    LSeq.index st' 2 == LSeq.index (as_seq h0 st) 2 /\
    LSeq.index st' 3 == LSeq.index (as_seq h0 st) 3)))

let load_block0 st b =
  let h0 = ST.get() in
  st.(size 0) <- vec_load_le U128 1 b;
  uints_bytes_le_lemma (as_seq h0 b)


inline_for_extraction noextract
val load_key1:
    k: key1
  -> b: lbuffer uint8 16ul ->
  Stack unit
  (requires (fun h -> live h k /\ live h b))
  (ensures (fun h0 _ h1 -> modifies1 k h0 h1 /\
    u8_16_to_le (uints_to_bytes_be (vec_v (LSeq.index (as_seq h1 k) 0))) == as_seq h0 b))

let load_key1 k b =
  let h0 = ST.get() in
  k.(size 0) <- vec_load_le U128 1 b;
  uints_bytes_le_lemma (as_seq h0 b)


inline_for_extraction noextract
val load_nonce_copy:
    n: nonce
  -> nb: lbuffer uint8 16ul
  -> b: lbuffer uint8 12ul ->
  Stack unit
  (requires (fun h -> live h n /\ live h nb /\ live h b /\ disjoint nb b))
  (ensures (fun h0 _ h1 -> modifies2 n nb h0 h1 /\
    u8_16_to_le (uints_to_bytes_be (vec_v (LSeq.index (as_seq h1 n) 0))) == 
      LSeq.update_sub (as_seq h0 nb) 0 12 (as_seq h0 b)))

let load_nonce_copy n nb b =
  let h0 = ST.get() in
  copy (sub nb 0ul 12ul) b;
  let h1 = ST.get() in
  LSeq.eq_intro (as_seq h1 (gsub nb 12ul 4ul))
    (LSeq.sub (as_seq h1 nb) 12 4);
  LSeq.lemma_update_sub (as_seq h0 nb) 0 12 (as_seq h0 b) (as_seq h1 nb);
  n.(size 0) <- vec_load_le U128 1 nb;
  uints_bytes_le_lemma (LSeq.update_sub (as_seq h0 nb) 0 12 (as_seq h0 b))

inline_for_extraction noextract
val load_nonce:
    n: nonce
  -> b: lbuffer uint8 12ul ->
  Stack unit
  (requires (fun h -> live h n /\ live h b))
  (ensures (fun h0 _ h1 -> modifies1 n h0 h1 /\
    u8_16_to_le (uints_to_bytes_be (vec_v (LSeq.index (as_seq h1 n) 0))) == 
      LSeq.update_sub (LSeq.create 16 (u8 0)) 0 12 (as_seq h0 b)))

let load_nonce n b =
  push_frame();
  let nb = create 16ul (u8 0) in
  load_nonce_copy n nb b;
  pop_frame()


inline_for_extraction noextract
val load_state:
    st: state
  -> nonce: nonce
  -> counter: uint32 ->
  Stack unit
  (requires (fun h -> live h st /\ live h nonce))
  (ensures (fun h0 _ h1 -> modifies1 st h0 h1 /\
    (let nonce0 = LSeq.index (as_seq h0 nonce) 0 in
    (* nonce <- counter0 *)
    let n0_128 =
      Spec.AES.aes_ctr32_set_counter_LE (uints_to_bytes_be (vec_v nonce0))
      counter in
    (* nonce <- counter1 *)
    let n1_128 =
      Spec.AES.aes_ctr32_set_counter_LE (uints_to_bytes_be (vec_v nonce0))
      (counter +. u32 1) in
    (* nonce <- counter2 *)
    let n2_128 =
      Spec.AES.aes_ctr32_set_counter_LE (uints_to_bytes_be (vec_v nonce0))
      (counter +. u32 2) in
    (* nonce <- counter3 *)
    let n3_128 =
      Spec.AES.aes_ctr32_set_counter_LE (uints_to_bytes_be (vec_v nonce0))
      (counter +. u32 3) in
    uints_to_bytes_be (vec_v (LSeq.index (as_seq h1 st) 0)) == n0_128 /\
    uints_to_bytes_be (vec_v (LSeq.index (as_seq h1 st) 1)) == n1_128 /\
    uints_to_bytes_be (vec_v (LSeq.index (as_seq h1 st) 2)) == n2_128 /\
    uints_to_bytes_be (vec_v (LSeq.index (as_seq h1 st) 3)) == n3_128)))

let load_state st nonce counter =
  let counter0 = Lib.ByteBuffer.uint_to_be counter in
  let counter1 = Lib.ByteBuffer.uint_to_be (counter +. u32 1) in
  let counter2 = Lib.ByteBuffer.uint_to_be (counter +. u32 2) in
  let counter3 = Lib.ByteBuffer.uint_to_be (counter +. u32 3) in
  let nonce0 = nonce.(size 0) in
  st.(size 0) <- cast U128 1 (vec_set #U32 #4 (cast #U128 #1 U32 4 nonce0) 3ul counter0);
  st.(size 1) <- cast U128 1 (vec_set #U32 #4 (cast #U128 #1 U32 4 nonce0) 3ul counter1);
  st.(size 2) <- cast U128 1 (vec_set #U32 #4 (cast #U128 #1 U32 4 nonce0) 3ul counter2);
  st.(size 3) <- cast U128 1 (vec_set #U32 #4 (cast #U128 #1 U32 4 nonce0) 3ul counter3);
  vec_set_counter_lemma (uints_to_bytes_be (vec_v nonce0)) (v counter0);
  vec_set_counter_lemma (uints_to_bytes_be (vec_v nonce0)) (v counter1);
  vec_set_counter_lemma (uints_to_bytes_be (vec_v nonce0)) (v counter2);
  vec_set_counter_lemma (uints_to_bytes_be (vec_v nonce0)) (v counter3)

inline_for_extraction noextract
val store_block0:
    out: lbuffer uint8 16ul
  -> st: state ->
  Stack unit
  (requires (fun h -> live h st /\ live h out))
  (ensures (fun h0 _ h1 -> modifies1 out h0 h1 /\
    as_seq h1 out == u8_16_to_le (uints_to_bytes_be (vec_v (LSeq.index (as_seq h0 st) 0)))))

let store_block0 out st =
  let h0 = ST.get() in
  vec_store_le out st.(size 0);
  uints_to_bytes_u8_16_le (vec_v (LSeq.index (as_seq h0 st) 0))


inline_for_extraction noextract
val xor_state_key1:
    st: state
  -> key: key1 ->
  Stack unit
  (requires (fun h -> live h st /\ live h key /\ disjoint st key))
  (ensures (fun h0 _ h1 -> modifies1 st h0 h1 /\
    (let st' = as_seq h0 st in
    let st'' = as_seq h1 st in
    let k = uints_to_bytes_be (vec_v (LSeq.index (as_seq h0 key) 0)) in
    uints_to_bytes_be (vec_v (LSeq.index st'' 0)) == LSeq.map2 ( ^. ) (uints_to_bytes_be (vec_v (LSeq.index st' 0))) k /\
    uints_to_bytes_be (vec_v (LSeq.index st'' 1)) == LSeq.map2 ( ^. ) (uints_to_bytes_be (vec_v (LSeq.index st' 1))) k /\
    uints_to_bytes_be (vec_v (LSeq.index st'' 2)) == LSeq.map2 ( ^. ) (uints_to_bytes_be (vec_v (LSeq.index st' 2))) k /\
    uints_to_bytes_be (vec_v (LSeq.index st'' 3)) == LSeq.map2 ( ^. ) (uints_to_bytes_be (vec_v (LSeq.index st' 3))) k)))

let xor_state_key1 st key =
  let h0 = ST.get() in
  st.(size 0) <- vec_xor st.(size 0) key.(size 0);
  st.(size 1) <- vec_xor st.(size 1) key.(size 0);
  st.(size 2) <- vec_xor st.(size 2) key.(size 0);
  st.(size 3) <- vec_xor st.(size 3) key.(size 0);
  let k = vec_v (LSeq.index (as_seq h0 key) 0) in
  vec_xor_lemma (vec_v (LSeq.index (as_seq h0 st) 0)) k;
  vec_xor_lemma (vec_v (LSeq.index (as_seq h0 st) 1)) k;
  vec_xor_lemma (vec_v (LSeq.index (as_seq h0 st) 2)) k;
  vec_xor_lemma (vec_v (LSeq.index (as_seq h0 st) 3)) k


inline_for_extraction noextract
val xor_block:
    out: lbuffer uint8 64ul
  -> st: state
  -> b: lbuffer uint8 64ul ->
  Stack unit
  (requires (fun h -> live h st /\ live h out /\ live h b))
  (ensures (fun h0 _ h1 -> modifies1 out h0 h1 /\
    (let b' = as_seq h0 b in
    let out' = as_seq h1 out in
    let st' = as_seq h0 st in
    LSeq.sub out' 0 16 == u8_16_to_le (LSeq.map2 ( ^. )
        (u8_16_to_le (LSeq.sub b' 0 16)) (uints_to_bytes_be (vec_v (LSeq.index st' 0)))) /\
    LSeq.sub out' 16 16 == u8_16_to_le (LSeq.map2 ( ^. )
        (u8_16_to_le (LSeq.sub b' 16 16)) (uints_to_bytes_be (vec_v (LSeq.index st' 1)))) /\
    LSeq.sub out' 32 16 == u8_16_to_le (LSeq.map2 ( ^. )
        (u8_16_to_le (LSeq.sub b' 32 16)) (uints_to_bytes_be (vec_v (LSeq.index st' 2)))) /\
    LSeq.sub out' 48 16 == u8_16_to_le (LSeq.map2 ( ^. )
        (u8_16_to_le (LSeq.sub b' 48 16)) (uints_to_bytes_be (vec_v (LSeq.index st' 3)))))))

let xor_block out st inp =
  let h0 = ST.get() in
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
  vec_store_le (sub out (size 48) (size 16)) v3;
  vec_xor_lemma_le (LSeq.sub (as_seq h0 inp) 0 16) (vec_v (LSeq.index (as_seq h0 st) 0));
  vec_xor_lemma_le (LSeq.sub (as_seq h0 inp) 16 16) (vec_v (LSeq.index (as_seq h0 st) 1));
  vec_xor_lemma_le (LSeq.sub (as_seq h0 inp) 32 16) (vec_v (LSeq.index (as_seq h0 st) 2));
  vec_xor_lemma_le (LSeq.sub (as_seq h0 inp) 48 16) (vec_v (LSeq.index (as_seq h0 st) 3))


inline_for_extraction noextract
val aes_enc:
    st: state
  -> key: key1 ->
  Stack unit
  (requires (fun h -> live h st /\ live h key /\ disjoint st key))
  (ensures (fun h0 _ h1 -> modifies1 st h0 h1 /\
    (let st' = as_seq h0 st in
    let st'' = as_seq h1 st in
    let k = uints_to_bytes_be (vec_v (LSeq.index (as_seq h0 key) 0)) in
    uints_to_bytes_be (vec_v (LSeq.index st'' 0)) ==
      Spec.AES.aes_enc k (uints_to_bytes_be (vec_v (LSeq.index st' 0))) /\
    uints_to_bytes_be (vec_v (LSeq.index st'' 1)) ==
      Spec.AES.aes_enc k (uints_to_bytes_be (vec_v (LSeq.index st' 1))) /\
    uints_to_bytes_be (vec_v (LSeq.index st'' 2)) ==
      Spec.AES.aes_enc k (uints_to_bytes_be (vec_v (LSeq.index st' 2))) /\
    uints_to_bytes_be (vec_v (LSeq.index st'' 3)) ==
      Spec.AES.aes_enc k (uints_to_bytes_be (vec_v (LSeq.index st' 3))))))

let aes_enc st key =
  let h0 = ST.get() in
  st.(size 0) <- cast U128 1 (vec_aes_enc (cast U8 16 key.(size 0)) (cast U8 16 st.(size 0)));
  st.(size 1) <- cast U128 1 (vec_aes_enc (cast U8 16 key.(size 0)) (cast U8 16 st.(size 1)));
  st.(size 2) <- cast U128 1 (vec_aes_enc (cast U8 16 key.(size 0)) (cast U8 16 st.(size 2)));
  st.(size 3) <- cast U128 1 (vec_aes_enc (cast U8 16 key.(size 0)) (cast U8 16 st.(size 3)));
  vec_u128_to_u8 (vec_v (LSeq.index (as_seq h0 key) 0));
  vec_u128_to_u8 (vec_v (LSeq.index (as_seq h0 st) 0));
  vec_u128_to_u8 (vec_v (LSeq.index (as_seq h0 st) 1));
  vec_u128_to_u8 (vec_v (LSeq.index (as_seq h0 st) 2));
  vec_u128_to_u8 (vec_v (LSeq.index (as_seq h0 st) 3));
  let k = uints_to_bytes_be (vec_v (LSeq.index (as_seq h0 key) 0)) in
  vec_u8_16 (Spec.AES.aes_enc k (uints_to_bytes_be (vec_v (LSeq.index (as_seq h0 st) 0))));
  vec_u8_16 (Spec.AES.aes_enc k (uints_to_bytes_be (vec_v (LSeq.index (as_seq h0 st) 1))));
  vec_u8_16 (Spec.AES.aes_enc k (uints_to_bytes_be (vec_v (LSeq.index (as_seq h0 st) 2))));
  vec_u8_16 (Spec.AES.aes_enc k (uints_to_bytes_be (vec_v (LSeq.index (as_seq h0 st) 3))));
  uints_bytes_be_lemma (Spec.AES.aes_enc k (uints_to_bytes_be (vec_v (LSeq.index (as_seq h0 st) 0))));
  uints_bytes_be_lemma (Spec.AES.aes_enc k (uints_to_bytes_be (vec_v (LSeq.index (as_seq h0 st) 1))));
  uints_bytes_be_lemma (Spec.AES.aes_enc k (uints_to_bytes_be (vec_v (LSeq.index (as_seq h0 st) 2))));
  uints_bytes_be_lemma (Spec.AES.aes_enc k (uints_to_bytes_be (vec_v (LSeq.index (as_seq h0 st) 3))))


inline_for_extraction noextract
val aes_enc_last:
    st: state
  -> key: key1 ->
  Stack unit
  (requires (fun h -> live h st /\ live h key /\ disjoint st key))
  (ensures (fun h0 _ h1 -> modifies1 st h0 h1 /\
    (let st' = as_seq h0 st in
    let st'' = as_seq h1 st in
    let k = uints_to_bytes_be (vec_v (LSeq.index (as_seq h0 key) 0)) in
    uints_to_bytes_be (vec_v (LSeq.index st'' 0)) ==
      Spec.AES.aes_enc_last k (uints_to_bytes_be (vec_v (LSeq.index st' 0))) /\
    uints_to_bytes_be (vec_v (LSeq.index st'' 1)) ==
      Spec.AES.aes_enc_last k (uints_to_bytes_be (vec_v (LSeq.index st' 1))) /\
    uints_to_bytes_be (vec_v (LSeq.index st'' 2)) ==
      Spec.AES.aes_enc_last k (uints_to_bytes_be (vec_v (LSeq.index st' 2))) /\
    uints_to_bytes_be (vec_v (LSeq.index st'' 3)) ==
      Spec.AES.aes_enc_last k (uints_to_bytes_be (vec_v (LSeq.index st' 3))))))

let aes_enc_last st key =
  let h0 = ST.get() in
  st.(size 0) <- cast U128 1 (vec_aes_enc_last (cast U8 16 key.(size 0)) (cast U8 16 st.(size 0)));
  st.(size 1) <- cast U128 1 (vec_aes_enc_last (cast U8 16 key.(size 0)) (cast U8 16 st.(size 1)));
  st.(size 2) <- cast U128 1 (vec_aes_enc_last (cast U8 16 key.(size 0)) (cast U8 16 st.(size 2)));
  st.(size 3) <- cast U128 1 (vec_aes_enc_last (cast U8 16 key.(size 0)) (cast U8 16 st.(size 3)));
  vec_u128_to_u8 (vec_v (LSeq.index (as_seq h0 key) 0));
  vec_u128_to_u8 (vec_v (LSeq.index (as_seq h0 st) 0));
  vec_u128_to_u8 (vec_v (LSeq.index (as_seq h0 st) 1));
  vec_u128_to_u8 (vec_v (LSeq.index (as_seq h0 st) 2));
  vec_u128_to_u8 (vec_v (LSeq.index (as_seq h0 st) 3));
  let k = uints_to_bytes_be (vec_v (LSeq.index (as_seq h0 key) 0)) in
  vec_u8_16 (Spec.AES.aes_enc_last k (uints_to_bytes_be (vec_v (LSeq.index (as_seq h0 st) 0))));
  vec_u8_16 (Spec.AES.aes_enc_last k (uints_to_bytes_be (vec_v (LSeq.index (as_seq h0 st) 1))));
  vec_u8_16 (Spec.AES.aes_enc_last k (uints_to_bytes_be (vec_v (LSeq.index (as_seq h0 st) 2))));
  vec_u8_16 (Spec.AES.aes_enc_last k (uints_to_bytes_be (vec_v (LSeq.index (as_seq h0 st) 3))));
  uints_bytes_be_lemma (Spec.AES.aes_enc_last k (uints_to_bytes_be (vec_v (LSeq.index (as_seq h0 st) 0))));
  uints_bytes_be_lemma (Spec.AES.aes_enc_last k (uints_to_bytes_be (vec_v (LSeq.index (as_seq h0 st) 1))));
  uints_bytes_be_lemma (Spec.AES.aes_enc_last k (uints_to_bytes_be (vec_v (LSeq.index (as_seq h0 st) 2))));
  uints_bytes_be_lemma (Spec.AES.aes_enc_last k (uints_to_bytes_be (vec_v (LSeq.index (as_seq h0 st) 3))))

inline_for_extraction noextract
val aes_keygen_assist0:
    ok: key1
  -> ik: key1
  -> rcon: uint8 ->
  Stack unit
  (requires (fun h -> live h ok /\ live h ik))
  (ensures (fun h0 _ h1 -> modifies1 ok h0 h1 /\
    uints_to_bytes_be (vec_v (LSeq.index (as_seq h1 ok) 0)) ==
      Spec.AES.keygen_assist0 rcon (uints_to_bytes_be (vec_v (LSeq.index (as_seq h0 ik) 0)))))

let aes_keygen_assist0 ok ik rcon =
  let h0 = ST.get() in
  let v = vec_aes_keygen_assist (cast U8 16 ik.(size 0)) rcon in
  ok.(size 0) <- cast U128 1 (vec_permute4 (cast U32 4 v) 3ul 3ul 3ul 3ul);
  vec_u128_to_u8 (vec_v (LSeq.index (as_seq h0 ik) 0));
  vec_u8_16 (Spec.AES.aes_keygen_assist rcon (uints_to_bytes_be (vec_v (LSeq.index (as_seq h0 ik) 0))));
  let k = Spec.AES.aes_keygen_assist rcon (uints_to_bytes_be (vec_v (LSeq.index (as_seq h0 ik) 0))) in
  let i = LSeq.index (uints_from_bytes_be #U32 #SEC #4 k) 3 in
  uints_bytes_be_lemma (uints_to_bytes_be (LSeq.create4 i i i i));
  vec_create4_3_lemma k

inline_for_extraction noextract
val aes_keygen_assist1:
    ok: key1
  -> ik: key1 ->
  Stack unit
  (requires (fun h -> live h ok /\ live h ik))
  (ensures (fun h0 _ h1 -> modifies1 ok h0 h1 /\
    uints_to_bytes_be (vec_v (LSeq.index (as_seq h1 ok) 0)) ==
      Spec.AES.keygen_assist1 (uints_to_bytes_be (vec_v (LSeq.index (as_seq h0 ik) 0)))))

let aes_keygen_assist1 ok ik =
  let h0 = ST.get() in
  let v = vec_aes_keygen_assist (cast U8 16 ik.(size 0)) (u8 0) in
  ok.(size 0) <- cast U128 1 (vec_permute4 (cast U32 4 v) 2ul 2ul 2ul 2ul);
  vec_u128_to_u8 (vec_v (LSeq.index (as_seq h0 ik) 0));
  vec_u8_16 (Spec.AES.aes_keygen_assist (u8 0) (uints_to_bytes_be (vec_v (LSeq.index (as_seq h0 ik) 0))));
  let k = Spec.AES.aes_keygen_assist (u8 0) (uints_to_bytes_be (vec_v (LSeq.index (as_seq h0 ik) 0))) in
  let i = LSeq.index (uints_from_bytes_be #U32 #SEC #4 k) 2 in
  uints_bytes_be_lemma (uints_to_bytes_be (LSeq.create4 i i i i));
  vec_create4_2_lemma k


inline_for_extraction noextract
val key_expansion_step:
    next: key1
  -> prev: key1 ->
  Stack unit
  (requires (fun h -> live h prev /\ live h next))
  (ensures (fun h0 _ h1 -> modifies1 next h0 h1 /\
    (let p = uints_to_bytes_be (vec_v (LSeq.index (as_seq h0 prev) 0)) in
    let n = uints_to_bytes_be (vec_v (LSeq.index (as_seq h0 next) 0)) in
    uints_to_bytes_be (vec_v (LSeq.index (as_seq h1 next) 0)) == Spec.AES.key_expansion_step_LE p n)))

let key_expansion_step next prev =
  let h0 = ST.get() in
  let key = prev.(size 0) in
  let key = vec_xor key (vec_shift_left key (size 32)) in
  let key = vec_xor key (vec_shift_left key (size 32)) in
  let key = vec_xor key (vec_shift_left key (size 32)) in
  next.(size 0) <- vec_xor key next.(size 0);
  let p0 = LSeq.create 16 (u8 0) in
  let p = vec_v (LSeq.index (as_seq h0 prev) 0) in
  let n = vec_v (LSeq.index (as_seq h0 next) 0) in
  vec_shift_l_32_lemma p0 p;
  vec_xor_lemma p (LSeq.map (shift_left_i (size 32)) p);
  let k = LSeq.map2 ( ^. ) p (LSeq.map (shift_left_i (size 32)) p) in
  vec_shift_l_32_lemma p0 k;
  vec_xor_lemma k (LSeq.map (shift_left_i (size 32)) k);
  let k = LSeq.map2 ( ^. ) k (LSeq.map (shift_left_i (size 32)) k) in
  vec_shift_l_32_lemma p0 k;
  vec_xor_lemma k (LSeq.map (shift_left_i (size 32)) k);
  let k = LSeq.map2 ( ^. ) k (LSeq.map (shift_left_i (size 32)) k) in
  vec_xor_lemma k n
