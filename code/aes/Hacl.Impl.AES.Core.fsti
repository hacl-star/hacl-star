module Hacl.Impl.AES.Core

open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer
open Lib.IntVector

module ST = FStar.HyperStack.ST



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
let klen (m:m_spec) =
  match m with
  | MAES -> 1ul
  | M32 -> 8ul

unfold noextract
let nlen (m:m_spec) =
  match m with
  | MAES -> 1ul
  | M32 -> 8ul

unfold noextract
let elem_zero (m:m_spec) : stelem m =
  match m with
  | M32 -> u64 0
  | MAES -> vec_zero U128 1

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
  (ensures  (fun h0 _ h1 -> modifies1 st h0 h1))

inline_for_extraction noextract
val load_block0:
    #m: m_spec
  -> st: state m
  -> b: lbuffer uint8 16ul ->
  Stack unit
  (requires (fun h -> live h st /\ live h b))
  (ensures  (fun h0 _ h1 -> modifies1 st h0 h1))

inline_for_extraction noextract
val load_key1:
    #m: m_spec
  -> k: key1 m
  -> b: lbuffer uint8 16ul ->
  Stack unit
  (requires (fun h -> live h k /\ live h b))
  (ensures  (fun h0 _ h1 -> modifies1 k h0 h1))

inline_for_extraction noextract
val load_nonce:
    #m: m_spec
  -> n: nonce m
  -> b: lbuffer uint8 12ul ->
  Stack unit
  (requires (fun h -> live h n /\ live h b))
  (ensures  (fun h0 _ h1 -> modifies1 n h0 h1))

inline_for_extraction noextract
val load_state:
    #m: m_spec
  -> st: state m
  -> nonce: nonce m
  -> counter: size_t ->
  Stack unit
  (requires (fun h -> live h st /\ live h nonce))
  (ensures  (fun h0 _ h1 -> modifies1 st h0 h1))

inline_for_extraction noextract
val store_block0:
    #m: m_spec
  -> out: lbuffer uint8 16ul
  -> st: state m ->
  Stack unit
  (requires (fun h -> live h st /\ live h out))
  (ensures  (fun h0 _ h1 -> modifies1 out h0 h1))

inline_for_extraction noextract
val xor_state_key1:
    #m: m_spec
  -> st: state m
  -> key: key1 m ->
  Stack unit
  (requires (fun h -> live h st /\ live h key))
  (ensures  (fun h0 _ h1 -> modifies1 st h0 h1))

inline_for_extraction noextract
val xor_block:
    #m: m_spec
  -> out: lbuffer uint8 64ul
  -> st: state m
  -> b: lbuffer uint8 64ul ->
  Stack unit
  (requires (fun h -> live h st /\ live h out /\ live h b))
  (ensures  (fun h0 _ h1 -> modifies2 out st h0 h1))

inline_for_extraction noextract
val aes_enc:
    #m: m_spec
  -> st: state m
  -> key: key1 m ->
  Stack unit
  (requires (fun h -> live h st /\ live h key))
  (ensures  (fun h0 _ h1 -> modifies1 st h0 h1))

inline_for_extraction noextract
val aes_enc_last:
    #m: m_spec
  -> st: state m
  -> key: key1 m ->
  Stack unit
  (requires (fun h -> live h st /\ live h key))
  (ensures  (fun h0 _ h1 -> modifies1 st h0 h1))

inline_for_extraction noextract
val aes_keygen_assist0:
    #m: m_spec
  -> ok: key1 m
  -> ik: key1 m
  -> rcon: uint8 ->
  Stack unit
  (requires (fun h -> live h ok /\ live h ik /\ disjoint ik ok))
  (ensures  (fun h0 _ h1 -> modifies1 ok h0 h1))

inline_for_extraction noextract
val aes_keygen_assist1:
    #m: m_spec
  -> ok: key1 m
  -> ik: key1 m ->
  Stack unit
  (requires (fun h -> live h ok /\ live h ik /\ disjoint ik ok))
  (ensures  (fun h0 _ h1 -> modifies1 ok h0 h1))

inline_for_extraction noextract
val key_expansion_step:
    #m: m_spec
  -> next: key1 m
  -> prev: key1 m ->
  Stack unit
  (requires (fun h -> live h prev /\ live h next))
  (ensures  (fun h0 _ h1 -> modifies1 next h0 h1))
