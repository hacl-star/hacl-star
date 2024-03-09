module Hacl.Impl.AES.Core

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul
open Lib.IntTypes
open Lib.Buffer
open Lib.IntVector
open Lib.ByteSequence

open Hacl.AES.Common

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence

#set-options "--z3rlimit 50"

type m_spec =
  | MAES
  | M32

unfold noextract
let stelem (m:m_spec) =
  match m with
  | MAES -> vec_t U128 1
  | M32 -> uint64

unfold noextract
let stlen (m:m_spec) =
  match m with
  | MAES -> 4ul
  | M32 -> 8ul

unfold noextract
let klen (m:m_spec) : n:size_t{v n <= 8} =
  match m with
  | MAES -> 1ul
  | M32 -> 8ul

unfold noextract
let nlen (m:m_spec) =
  match m with
  | MAES -> 1ul
  | M32 -> 8ul

unfold noextract
let blen (m:m_spec) =
  match m with
  | MAES -> 1ul
  | M32 -> 2ul

unfold noextract
let elem_zero (m:m_spec) : stelem m =
  match m with
  | M32 -> u64 0
  | MAES -> vec_zero U128 1

unfold noextract
let to_bytes (m:m_spec) (s:LSeq.lseq (stelem m) (v (blen m))) : LSeq.lseq uint8 16 =
  match m with
  | M32 -> LSeq.create 16 (u8 0)
  | MAES -> uints_to_bytes_be (vec_v #U128 #1 (LSeq.index s 0))

unfold noextract
let state_to_bytes (m:m_spec) (s:LSeq.lseq (stelem m) (v (stlen m))) (i:size_nat{i < 4}) : LSeq.lseq uint8 16 =
  match m with
  | M32 -> LSeq.create 16 (u8 0)
  | MAES -> uints_to_bytes_be (vec_v #U128 #1 (LSeq.index s i))

unfold noextract
let bytes_to_state (m:m_spec) (s0 s1 s2 s3:LSeq.lseq uint8 16) : LSeq.lseq (stelem m) (v (stlen m)) =
  match m with
  | M32 -> LSeq.create 8 (u64 0)
  | MAES -> LSeq.create4 (vec_from_bytes_be U128 1 s0) (vec_from_bytes_be U128 1 s1)
      (vec_from_bytes_be U128 1 s2) (vec_from_bytes_be U128 1 s3)

unfold noextract
let key_to_bytes (m:m_spec) (s:LSeq.lseq (stelem m) (v (klen m))) : LSeq.lseq uint8 16 =
  match m with
  | M32 -> LSeq.create 16 (u8 0)
  | MAES -> uints_to_bytes_be (vec_v #U128 #1 (LSeq.index s 0))

unfold noextract
let nonce_to_bytes (m:m_spec) (s:LSeq.lseq (stelem m) (v (nlen m))) : LSeq.lseq uint8 16 =
  match m with
  | M32 -> LSeq.create 16 (u8 0)
  | MAES -> uints_to_bytes_be (vec_v #U128 #1 (LSeq.index s 0))

unfold noextract
let keys_to_bytes (m:m_spec) (a:Spec.AES.variant) (b:LSeq.lseq (stelem m) ((Spec.AES.num_rounds a-1) * v (klen m))) : LSeq.lseq uint8 ((Spec.AES.num_rounds a-1) * 16) =
  match m with
  | M32 -> LSeq.create ((Spec.AES.num_rounds a-1) * 16) (u8 0)
  | MAES -> uints_to_bytes_be (LSeq.map (fun x -> LSeq.index (vec_v #U128 #1 x) 0) b)

unfold noextract
let keyx_to_bytes (m:m_spec) (a:Spec.AES.variant) (b:LSeq.lseq (stelem m) ((Spec.AES.num_rounds a+1) * v (klen m))) : LSeq.lseq uint8 ((Spec.AES.num_rounds a+1) * 16) =
  match m with
  | M32 -> LSeq.create ((Spec.AES.num_rounds a+1) * 16) (u8 0)
  | MAES -> uints_to_bytes_be (LSeq.map (fun x -> LSeq.index (vec_v #U128 #1 x) 0) b)

unfold noextract
let state (m:m_spec) = lbuffer (stelem m) (stlen m)

unfold noextract
let key1 (m:m_spec) = lbuffer (stelem m) (klen m)

unfold noextract
let nonce (m:m_spec) = lbuffer (stelem m) (nlen m)


inline_for_extraction noextract
val create_state:
  #m: m_spec ->
  StackInline (state m)
  (requires (fun h -> True))
  (ensures  (fun h0 f h1 -> live h1 f /\ stack_allocated f h0 h1 (Seq.create (v (stlen m)) (elem_zero m))))


inline_for_extraction noextract
val copy_state:
    #m: m_spec
  -> st: state m
  -> ost: state m ->
  Stack unit
  (requires (fun h -> live h st /\ live h ost /\ disjoint st ost))
  (ensures  (fun h0 _ h1 -> modifies1 st h0 h1 /\ as_seq h1 st == as_seq h0 ost))

inline_for_extraction noextract
val load_block0:
    #m: m_spec
  -> st: state m
  -> b: lbuffer uint8 16ul ->
  Stack unit
  (requires (fun h -> live h st /\ live h b /\ disjoint st b))
  (ensures  (fun h0 _ h1 -> modifies1 st h0 h1 /\
    (let st' = as_seq h0 st in
    let st'' = as_seq h1 st in
    u8_16_to_le (state_to_bytes m st'' 0) == as_seq h0 b /\
    state_to_bytes m st'' 1 == state_to_bytes m st' 1 /\
    state_to_bytes m st'' 2 == state_to_bytes m st' 2 /\
    state_to_bytes m st'' 3 == state_to_bytes m st' 3)))

inline_for_extraction noextract
val load_key1:
    #m: m_spec
  -> k: key1 m
  -> b: lbuffer uint8 16ul ->
  Stack unit
  (requires (fun h -> live h k /\ live h b))
  (ensures  (fun h0 _ h1 -> modifies1 k h0 h1 /\
    u8_16_to_le (key_to_bytes m (as_seq h1 k)) == as_seq h0 b))

inline_for_extraction noextract
val load_nonce:
    #m: m_spec
  -> n: nonce m
  -> b: lbuffer uint8 12ul ->
  Stack unit
  (requires (fun h -> live h n /\ live h b))
  (ensures  (fun h0 _ h1 -> modifies1 n h0 h1 /\
    u8_16_to_le (nonce_to_bytes m (as_seq h1 n)) == 
      LSeq.update_sub (LSeq.create 16 (u8 0)) 0 12 (as_seq h0 b)))

inline_for_extraction noextract
val load_state:
    #m: m_spec
  -> st: state m
  -> nonce: nonce m
  -> counter: uint32 ->
  Stack unit
  (requires (fun h -> live h st /\ live h nonce))
  (ensures  (fun h0 _ h1 -> modifies1 st h0 h1 /\
    (let nonce0 = nonce_to_bytes m (as_seq h0 nonce) in
    state_to_bytes m (as_seq h1 st) 0 ==
      Spec.AES.aes_ctr32_set_counter_LE nonce0 counter /\
    state_to_bytes m (as_seq h1 st) 1 ==
      Spec.AES.aes_ctr32_set_counter_LE nonce0 (counter +. u32 1) /\
    state_to_bytes m (as_seq h1 st) 2 ==
      Spec.AES.aes_ctr32_set_counter_LE nonce0 (counter +. u32 2) /\
    state_to_bytes m (as_seq h1 st) 3 ==
      Spec.AES.aes_ctr32_set_counter_LE nonce0 (counter +. u32 3))))

inline_for_extraction noextract
val store_block0:
    #m: m_spec
  -> out: lbuffer uint8 16ul
  -> st: state m ->
  Stack unit
  (requires (fun h -> live h st /\ live h out))
  (ensures  (fun h0 _ h1 -> modifies1 out h0 h1 /\
    as_seq h1 out == u8_16_to_le (state_to_bytes m (as_seq h0 st) 0)))

inline_for_extraction noextract
val xor_state_key1:
    #m: m_spec
  -> st: state m
  -> key: key1 m ->
  Stack unit
  (requires (fun h -> live h st /\ live h key /\ disjoint st key))
  (ensures  (fun h0 _ h1 -> modifies1 st h0 h1 /\
    (let st' = as_seq h0 st in
    let st'' = as_seq h1 st in
    let k = key_to_bytes m (as_seq h0 key) in
    state_to_bytes m st'' 0 == LSeq.map2 ( ^. ) (state_to_bytes m st' 0) k /\
    state_to_bytes m st'' 1 == LSeq.map2 ( ^. ) (state_to_bytes m st' 1) k /\
    state_to_bytes m st'' 2 == LSeq.map2 ( ^. ) (state_to_bytes m st' 2) k /\
    state_to_bytes m st'' 3 == LSeq.map2 ( ^. ) (state_to_bytes m st' 3) k)))

inline_for_extraction noextract
val xor_block:
    #m: m_spec
  -> out: lbuffer uint8 64ul
  -> st: state m
  -> b: lbuffer uint8 64ul ->
  Stack unit
  (requires (fun h -> live h st /\ live h out /\ live h b))
  (ensures  (fun h0 _ h1 -> modifies2 out st h0 h1 /\
    (let b' = as_seq h0 b in
    let out' = as_seq h1 out in
    let st' = as_seq h0 st in
    LSeq.sub out' 0 16 == u8_16_to_le (LSeq.map2 ( ^. )
        (u8_16_to_le (LSeq.sub b' 0 16)) (state_to_bytes m st' 0)) /\
    LSeq.sub out' 16 16 == u8_16_to_le (LSeq.map2 ( ^. )
        (u8_16_to_le (LSeq.sub b' 16 16)) (state_to_bytes m st' 1)) /\
    LSeq.sub out' 32 16 == u8_16_to_le (LSeq.map2 ( ^. )
        (u8_16_to_le (LSeq.sub b' 32 16)) (state_to_bytes m st' 2)) /\
    LSeq.sub out' 48 16 == u8_16_to_le (LSeq.map2 ( ^. )
        (u8_16_to_le (LSeq.sub b' 48 16)) (state_to_bytes m st' 3)))))

inline_for_extraction noextract
val aes_enc:
    #m: m_spec
  -> st: state m
  -> key: key1 m ->
  Stack unit
  (requires (fun h -> live h st /\ live h key /\ disjoint st key))
  (ensures  (fun h0 _ h1 -> modifies1 st h0 h1 /\
    (let st' = as_seq h0 st in
    let st'' = as_seq h1 st in
    let k = key_to_bytes m (as_seq h0 key) in
    state_to_bytes m st'' 0 == Spec.AES.aes_enc k (state_to_bytes m st' 0) /\
    state_to_bytes m st'' 1 == Spec.AES.aes_enc k (state_to_bytes m st' 1) /\
    state_to_bytes m st'' 2 == Spec.AES.aes_enc k (state_to_bytes m st' 2) /\
    state_to_bytes m st'' 3 == Spec.AES.aes_enc k (state_to_bytes m st' 3))))

inline_for_extraction noextract
val aes_enc_last:
    #m: m_spec
  -> st: state m
  -> key: key1 m ->
  Stack unit
  (requires (fun h -> live h st /\ live h key /\ disjoint st key))
  (ensures  (fun h0 _ h1 -> modifies1 st h0 h1 /\
    (let st' = as_seq h0 st in
    let st'' = as_seq h1 st in
    let k = key_to_bytes m (as_seq h0 key) in
    state_to_bytes m st'' 0 == Spec.AES.aes_enc_last k (state_to_bytes m st' 0) /\
    state_to_bytes m st'' 1 == Spec.AES.aes_enc_last k (state_to_bytes m st' 1) /\
    state_to_bytes m st'' 2 == Spec.AES.aes_enc_last k (state_to_bytes m st' 2) /\
    state_to_bytes m st'' 3 == Spec.AES.aes_enc_last k (state_to_bytes m st' 3))))

inline_for_extraction noextract
val aes_keygen_assist0:
    #m: m_spec
  -> ok: key1 m
  -> ik: key1 m
  -> rcon: uint8 ->
  Stack unit
  (requires (fun h -> live h ok /\ live h ik /\ disjoint ik ok))
  (ensures  (fun h0 _ h1 -> modifies1 ok h0 h1 /\
    key_to_bytes m (as_seq h1 ok) == Spec.AES.keygen_assist0 rcon (key_to_bytes m (as_seq h0 ik))))

inline_for_extraction noextract
val aes_keygen_assist1:
    #m: m_spec
  -> ok: key1 m
  -> ik: key1 m ->
  Stack unit
  (requires (fun h -> live h ok /\ live h ik /\ disjoint ik ok))
  (ensures  (fun h0 _ h1 -> modifies1 ok h0 h1 /\
    key_to_bytes m (as_seq h1 ok) == Spec.AES.keygen_assist1 (key_to_bytes m (as_seq h0 ik))))

inline_for_extraction noextract
val key_expansion_step:
    #m: m_spec
  -> next: key1 m
  -> prev: key1 m ->
  Stack unit
  (requires (fun h -> live h prev /\ live h next))
  (ensures  (fun h0 _ h1 -> modifies1 next h0 h1 /\
    (let p = key_to_bytes m (as_seq h0 prev) in
    let n = key_to_bytes m (as_seq h0 next) in
    key_to_bytes m (as_seq h1 next) == Spec.AES.key_expansion_step_LE p n)))
