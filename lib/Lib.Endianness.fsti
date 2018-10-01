module Lib.Endianness

open FStar.HyperStack
open FStar.HyperStack.ST
open LowStar.Buffer

open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Buffer

module B = LowStar.Buffer
module BS = Lib.ByteSequence



inline_for_extraction
val uint_from_bytes_le:
    #t:m_inttype{~(SIZE? t)}
  -> i:lbuffer uint8 (numbytes t)
  -> Stack (uint_t t)
    (requires fun h0 -> live h0 i)
    (ensures  fun h0 o h1 ->
      h0 == h1 /\ live h1 i /\
      o == BS.uint_from_bytes_le #t (as_seq h0 i))

inline_for_extraction
val uint_from_bytes_be:
    #t:m_inttype{~(SIZE? t)}
  -> i:lbuffer uint8 (numbytes t)
  -> Stack (uint_t t)
    (requires fun h0 -> live h0 i)
    (ensures  fun h0 o h1 ->
      h0 == h1 /\ live h1 i /\
      o == BS.uint_from_bytes_be #t (as_seq h0 i))

inline_for_extraction
val uint_to_bytes_le:
    #t:m_inttype{~(SIZE? t)}
  -> o:lbuffer uint8 (numbytes t)
  -> i:uint_t t
  -> Stack unit
    (requires fun h0 -> live h0 o)
    (ensures  fun h0 _ h1 ->
      live h1 o /\ modifies (loc_buffer o) h0 h1 /\
      as_seq h1 o == BS.uint_to_bytes_le #t i)

inline_for_extraction
val uint_to_bytes_be:
    #t:m_inttype{~(SIZE? t)}
  -> o:lbuffer uint8 (numbytes t)
  -> i:uint_t t
  -> Stack unit
    (requires fun h0 -> live h0 o)
    (ensures  fun h0 _ h1 ->
      live h1 o /\ modifies (loc_buffer o) h0 h1 /\
      as_seq h1 o == BS.uint_to_bytes_be #t i)

inline_for_extraction
val uints_from_bytes_le:
  #t:m_inttype
  -> #len:size_nat{len `op_Multiply` numbytes t <= max_size_t}
  -> o:lbuffer (uint_t t) len
  -> clen:size_t{size_v clen == len}
  -> i:lbuffer uint8 (len `op_Multiply` (numbytes t)) ->
  Stack unit
	(requires (fun h0 -> live h0 o /\ live h0 i))
	(ensures (fun h0 _ h1 -> modifies (loc_buffer o) h0 h1 /\
			      as_seq h1 o ==
			      (BS.uints_from_bytes_le #t #(len) (as_seq h0 i) )))

inline_for_extraction
val uints_from_bytes_be:
  #t:m_inttype -> #len:size_nat{len `op_Multiply` numbytes t <= max_size_t} ->
  o:lbuffer (uint_t t) len ->
  clen:size_t{size_v clen == len} ->
  i:lbuffer uint8 (len `op_Multiply` ((numbytes t))) ->
  Stack unit
	(requires (fun h0 -> live h0 o /\ live h0 i))
	(ensures (fun h0 _ h1 -> modifies (loc_buffer o) h0 h1 /\
			      as_seq h1 o ==
			      (BS.uints_from_bytes_be #t #(len) (as_seq h0 i) )))

inline_for_extraction
val uints_to_bytes_le:
  #t:m_inttype
  -> #len:size_nat{len `op_Multiply` numbytes t <= max_size_t}
  -> o:lbuffer uint8 (len `op_Multiply` ((numbytes t)))
  -> clen:size_t{size_v clen == len}
  -> i:lbuffer (uint_t t) len ->
  Stack unit
	(requires (fun h0 -> live h0 o /\ live h0 i))
	(ensures (fun h0 _ h1 -> modifies (loc_buffer o) h0 h1 /\
			      as_seq h1 o ==
			      (BS.uints_to_bytes_le #t #len (as_seq h0 i) )))

inline_for_extraction
val uints_to_bytes_be:
    #t:m_inttype
  -> #len:size_nat{len `op_Multiply` numbytes t <= max_size_t}
  -> o:lbuffer uint8 (len `op_Multiply` (numbytes t))
  -> clen:size_t{size_v clen == len}
  -> i:lbuffer (uint_t t) len ->
  Stack unit
	(requires (fun h0 -> live h0 o /\ live h0 i /\ disjoint o i))
	(ensures (fun h0 _ h1 -> modifies (loc_buffer o) h0 h1 /\
			      as_seq h1 o ==
			      (BS.uints_to_bytes_be #t #len (as_seq h0 i) )))

inline_for_extraction
let uint32s_to_bytes_le = uints_to_bytes_le #U32

inline_for_extraction
let uint32s_from_bytes_le = uints_from_bytes_le #U32
