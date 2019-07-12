module Hacl.Impl.Aes.Core

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer
open Lib.Vec128

type m_spec =
  | MAES
  | M32

unfold
let stelem (m:m_spec) =
  match m with
  | MAES -> vec128
  | M32 -> uint64

unfold
let stlen (m:m_spec) =
  match m with
  | MAES -> 4ul
  | M32 -> 8ul

unfold
let klen (m:m_spec) =
  match m with
  | MAES -> 1ul
  | M32 -> 8ul

unfold
let nlen (m:m_spec) =
  match m with
  | MAES -> 1ul
  | M32 -> 8ul

unfold
let elem_zero (m:m_spec) : stelem m =
  match m with
  | M32 -> u64 0
  | MAES -> vec128_zero

unfold
let state (m:m_spec) = lbuffer (stelem m) (stlen m)

unfold
let key1 (m:m_spec) = lbuffer (stelem m) (klen m)

unfold
let nonce (m:m_spec) = lbuffer (stelem m) (nlen m)

inline_for_extraction
val create_state: #m:m_spec -> StackInline (state m)
                   (requires (fun h -> True))
		   (ensures (fun h0 f h1 -> live h1 f /\ stack_allocated f h0 h1 (Seq.create (v (stlen m)) (elem_zero m))))

inline_for_extraction
val copy_state: #m:m_spec -> st:state m -> ost:state m -> ST unit
			     (requires (fun h -> live h st /\ live h ost /\ disjoint st ost))
			     (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1))

inline_for_extraction
val load_block0: #m:m_spec -> st:state m -> b: lbuffer uint8 16ul -> ST unit
			     (requires (fun h -> live h st /\ live h b))
			     (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1))

inline_for_extraction
val load_key1: #m:m_spec -> k:key1 m -> b: lbuffer uint8 16ul -> ST unit
			     (requires (fun h -> live h k /\ live h b))
			     (ensures (fun h0 _ h1 -> modifies (loc k) h0 h1))

inline_for_extraction
val load_nonce: #m:m_spec -> n:nonce m -> b: lbuffer uint8 12ul -> ST unit
			     (requires (fun h -> live h n /\ live h b))
			     (ensures (fun h0 _ h1 -> modifies (loc n) h0 h1))

inline_for_extraction
val load_state: #m:m_spec -> st:state m -> nonce:nonce m -> counter:size_t -> ST unit
			     (requires (fun h -> live h st /\ live h nonce))
			     (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1))

inline_for_extraction
val store_block0: #m:m_spec -> out:lbuffer uint8 16ul -> st:state m -> ST unit
			     (requires (fun h -> live h st /\ live h out))
			     (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))

inline_for_extraction
val xor_state_key1: #m:m_spec -> st:state m -> key:key1 m -> ST unit
			     (requires (fun h -> live h st /\ live h key))
			     (ensures (fun h0 _ h1 -> live h1 st /\ live h1 key /\ modifies (loc st) h0 h1))

inline_for_extraction
val xor_block: #m:m_spec -> out:lbuffer uint8 64ul -> st:state m -> b:lbuffer uint8 64ul -> ST unit
			     (requires (fun h -> live h st /\ live h out /\ live h b))
			     (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))

inline_for_extraction
val aes_enc: #m:m_spec -> st:state m -> key:key1 m -> ST unit
			     (requires (fun h -> live h st /\ live h key))
			     (ensures (fun h0 _ h1 -> live h1 st /\ live h1 key /\ modifies (loc st) h0 h1))


inline_for_extraction
val aes_enc_last: #m:m_spec -> st:state m -> key:key1 m -> ST unit
			     (requires (fun h -> live h st /\ live h key))
			     (ensures (fun h0 _ h1 -> live h1 st /\ live h1 key /\ modifies (loc st) h0 h1))

inline_for_extraction
val aes_keygen_assist: #m:m_spec -> ok:key1 m -> ik:key1 m -> rcon:uint8 -> ST unit
			     (requires (fun h -> live h ok /\ live h ik /\ disjoint ik ok))
			     (ensures (fun h0 _ h1 -> live h1 ok /\ live h1 ik /\ modifies (loc ok) h0 h1))

inline_for_extraction 
val key_expansion_step: #m:m_spec -> next:key1 m -> prev:key1 m -> ST unit
			     (requires (fun h -> live h prev /\ live h next))
			     (ensures (fun h0 _ h1 -> live h1 prev /\ live h1 next /\ modifies (loc next) h0 h1))

inline_for_extraction 
val key_expansion_step2: #m:m_spec -> next:key1 m -> prev:key1 m -> ST unit
			     (requires (fun h -> live h prev /\ live h next))
			     (ensures (fun h0 _ h1 -> live h1 prev /\ live h1 next /\ modifies (loc next) h0 h1))


