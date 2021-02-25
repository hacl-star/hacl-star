module Lib.ByteBuffer

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer

module B = LowStar.Buffer
module BS = Lib.ByteSequence

#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

/// Host to {little,big}-endian conversions
/// TODO: missing specifications

inline_for_extraction
val uint_to_be: #t:inttype{unsigned t /\ ~(U128? t)} -> #l:secrecy_level -> uint_t t l -> uint_t t l

inline_for_extraction
val uint_to_le: #t:inttype{unsigned t /\ ~(U128? t)} -> #l:secrecy_level -> uint_t t l -> uint_t t l

inline_for_extraction
val uint_from_be: #t:inttype{unsigned t /\ ~(U128? t)} -> #l:secrecy_level -> uint_t t l -> uint_t t l

inline_for_extraction
val uint_from_le: #t:inttype{unsigned t /\ ~(U128? t)} -> #l:secrecy_level -> uint_t t l -> uint_t t l

(** Constructs the equality mask for two buffers of secret integers in constant-time *)
inline_for_extraction
val buf_eq_mask:
    #t:inttype{~(S128? t)}
  -> #len1:size_t
  -> #len2:size_t
  -> b1:lbuffer (int_t t SEC) len1
  -> b2:lbuffer (int_t t SEC) len2
  -> len:size_t{v len <= v len1 /\ v len <= v len2}
  -> res:lbuffer (int_t t SEC) (size 1) ->
  Stack (int_t t SEC)
    (requires fun h ->
      live h b1 /\ live h b2 /\ live h res /\ disjoint res b1 /\ disjoint res b2 /\
      v (bget h res 0) == v (ones t SEC))
    (ensures fun h0 z h1 ->
      modifies1 res h0 h1 /\
      v z == v (BS.seq_eq_mask (as_seq h0 b1) (as_seq h0 b2) (v len)))

(** Compares two buffers of secret bytes of equal length in constant-time,
    declassifying the result *)
inline_for_extraction
val lbytes_eq: #len:size_t -> b1:lbuffer uint8 len -> b2:lbuffer uint8 len -> Stack bool
  (requires fun h -> live h b1 /\ live h b2)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\ r == BS.lbytes_eq (as_seq h0 b1) (as_seq h0 b2))

inline_for_extraction
val buf_mask_select:
    #t:inttype{~(S128? t)}
  -> #len:size_t
  -> b1:lbuffer (int_t t SEC) len
  -> b2:lbuffer (int_t t SEC) len
  -> mask:int_t t SEC{v mask = 0 \/ v mask = v (ones t SEC)}
  -> res:lbuffer (int_t t SEC) len ->
  Stack unit
    (requires fun h ->
      live h b1 /\ live h b2 /\ live h res /\
      eq_or_disjoint res b1 /\ eq_or_disjoint res b2)
    (ensures fun h0 _ h1 ->
      modifies1 res h0 h1 /\
      as_seq h1 res == BS.seq_mask_select (as_seq h0 b1) (as_seq h0 b2) mask)

inline_for_extraction
val uint_from_bytes_le:
    #t:inttype{unsigned t /\ ~(U1? t)}
  -> #l:secrecy_level
  -> i:lbuffer (uint_t U8 l) (size (numbytes t)) ->
  Stack (uint_t t l)
    (requires fun h0 -> live h0 i)
    (ensures  fun h0 o h1 ->
      h0 == h1 /\ live h1 i /\
      o == BS.uint_from_bytes_le #t #l (as_seq h0 i))

inline_for_extraction
val uint_from_bytes_be:
    #t:inttype{unsigned t /\ ~(U1? t)}
  -> #l:secrecy_level
  -> i:lbuffer (uint_t U8 l) (size (numbytes t)) ->
  Stack (uint_t t l)
    (requires fun h0 -> live h0 i)
    (ensures  fun h0 o h1 ->
      h0 == h1 /\ live h1 i /\
      o == BS.uint_from_bytes_be #t (as_seq h0 i))

inline_for_extraction
val uint_to_bytes_le:
    #t:inttype{unsigned t}
  -> #l:secrecy_level
  -> o:lbuffer (uint_t U8 l) (size (numbytes t))
  -> i:uint_t t l ->
  Stack unit
    (requires fun h0 -> live h0 o)
    (ensures  fun h0 _ h1 ->
      live h1 o /\ modifies (loc o) h0 h1 /\
      as_seq h1 o == BS.uint_to_bytes_le #t i)

inline_for_extraction
val uint_to_bytes_be:
    #t:inttype{unsigned t}
  -> #l:secrecy_level
  -> o:lbuffer (uint_t U8 l) (size (numbytes t))
  -> i:uint_t t l ->
  Stack unit
    (requires fun h0 -> live h0 o)
    (ensures  fun h0 _ h1 ->
      live h1 o /\ modifies (loc o) h0 h1 /\
      as_seq h1 o == BS.uint_to_bytes_be #t i)

inline_for_extraction
val uints_from_bytes_le:
    #t:inttype{unsigned t /\ ~(U1? t)}
  -> #l:secrecy_level
  -> #len:size_t{v len * numbytes t <= max_size_t}
  -> o:lbuffer (uint_t t l) len
  -> i:lbuffer (uint_t U8 l) (len *! size (numbytes t)) ->
  Stack unit
        (requires fun h0 -> live h0 o /\ live h0 i /\ disjoint o i)
        (ensures  fun h0 _ h1 ->
          modifies1 o h0 h1 /\
          as_seq h1 o == BS.uints_from_bytes_le #t #l #(v len) (as_seq h0 i))

inline_for_extraction
val uints_from_bytes_be:
    #t:inttype{unsigned t /\ ~(U1? t)}
  -> #l:secrecy_level
  -> #len:size_t{v len * numbytes t <= max_size_t}
  -> o:lbuffer (uint_t t l) len
  -> i:lbuffer (uint_t U8 l) (len *! size (numbytes t)) ->
  Stack unit
        (requires fun h0 -> live h0 o /\ live h0 i /\ disjoint o i)
        (ensures  fun h0 _ h1 ->
          modifies1 o h0 h1 /\
          as_seq h1 o == BS.uints_from_bytes_be #t #l #(v len) (as_seq h0 i))

inline_for_extraction
val uints_to_bytes_le:
    #t:inttype{unsigned t}
  -> #l:secrecy_level
  -> len:size_t{v len * numbytes t <= max_size_t}
  -> o:lbuffer (uint_t U8 l) (len *! size (numbytes t))
  -> i:lbuffer (uint_t t l) len ->
  Stack unit
        (requires fun h0 -> live h0 o /\ live h0 i /\ disjoint o i)
        (ensures  fun h0 _ h1 ->
          modifies1 o h0 h1 /\
          as_seq h1 o == BS.uints_to_bytes_le #t #l #(v len) (as_seq h0 i))

inline_for_extraction
val uints_to_bytes_be:
    #t:inttype{unsigned t}
  -> #l:secrecy_level
  -> len:size_t{v len * numbytes t <= max_size_t}
  -> o:lbuffer (uint_t U8 l) (len *! size (numbytes t))
  -> i:lbuffer (uint_t t l) len ->
  Stack unit
        (requires fun h0 -> live h0 o /\ live h0 i /\ disjoint o i)
        (ensures  fun h0 _ h1 ->
          modifies1 o h0 h1 /\
          as_seq h1 o == BS.uints_to_bytes_be #t #l #(v len) (as_seq h0 i))

inline_for_extraction
let uint32s_to_bytes_le len = uints_to_bytes_le #U32 #SEC len

inline_for_extraction
let uint32s_from_bytes_le #len = uints_from_bytes_le #U32 #SEC #len

inline_for_extraction
val uint_at_index_le:
    #t:inttype{unsigned t /\ ~(U1? t)}
  -> #l:secrecy_level
  -> #len:size_t{v len * numbytes t <= max_size_t}
  -> i:lbuffer (uint_t U8 l) (len *! size (numbytes t))
  -> idx:size_t{v idx < v len} ->
  Stack (uint_t t l)
        (requires fun h0 -> live h0 i)
        (ensures  fun h0 r h1 ->
          h0 == h1 /\
          r == BS.uint_at_index_le #t #l #(v len) (as_seq h0 i) (v idx))

inline_for_extraction
val uint_at_index_be:
    #t:inttype{unsigned t /\ ~(U1? t)}
  -> #l:secrecy_level
  -> #len:size_t{v len * numbytes t <= max_size_t}
  -> i:lbuffer (uint_t U8 l) (len *! size (numbytes t))
  -> idx:size_t{v idx < v len} ->
  Stack (uint_t t l)
        (requires fun h0 -> live h0 i)
        (ensures  fun h0 r h1 ->
          h0 == h1 /\
          r == BS.uint_at_index_be #t #l #(v len) (as_seq h0 i) (v idx))
