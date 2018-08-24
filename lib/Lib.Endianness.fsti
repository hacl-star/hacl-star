module Lib.Endianness

open FStar.HyperStack
open FStar.HyperStack.ST

open LowStar.Buffer

open Lib.IntTypes
open Lib.RawIntTypes
open Lib.PQ.Buffer

module B = LowStar.Buffer
module ByteSeq = Lib.ByteSequence

inline_for_extraction
val uint_from_bytes_le:
    #t:m_inttype{~(SIZE? t)}
  -> i:lbuffer uint8 (numbytes t)
  -> Stack (uint_t t)
    (requires fun h0 -> B.live h0 i)
    (ensures  fun h0 o h1 ->
      h0 == h1 /\ B.live h1 i /\
      o == ByteSeq.uint_from_bytes_le #t (B.as_seq h0 i))

inline_for_extraction
val uint_from_bytes_be:
    #t:m_inttype{~(SIZE? t)}
  -> i:lbuffer uint8 (numbytes t)
  -> Stack (uint_t t)
    (requires fun h0 -> B.live h0 i)
    (ensures  fun h0 o h1 ->
      h0 == h1 /\ B.live h1 i /\
      o == ByteSeq.uint_from_bytes_be #t (B.as_seq h0 i))

inline_for_extraction
val uint_to_bytes_le:
    #t:m_inttype{~(SIZE? t)}
  -> o:lbuffer uint8 (numbytes t)
  -> i:uint_t t
  -> Stack unit
    (requires fun h0 -> B.live h0 o)
    (ensures  fun h0 _ h1 ->
      B.live h1 o /\ modifies (loc_buffer o) h0 h1 /\
      B.as_seq h1 o == ByteSeq.uint_to_bytes_le #t i)

inline_for_extraction
val uint_to_bytes_be:
    #t:m_inttype{~(SIZE? t)}
  -> o:lbuffer uint8 (numbytes t)
  -> i:uint_t t
  -> Stack unit
    (requires fun h0 -> B.live h0 o)
    (ensures  fun h0 _ h1 ->
      B.live h1 o /\ modifies (loc_buffer o) h0 h1 /\
      B.as_seq h1 o == ByteSeq.uint_to_bytes_be #t i)
