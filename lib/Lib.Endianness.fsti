module Lib.Endianness

open FStar.HyperStack
open FStar.HyperStack.ST
open LowStar.Buffer

open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Buffer

module B = LowStar.Buffer
module BS = Lib.ByteSequence

open FStar.Mul

inline_for_extraction
val uint_from_bytes_le:
    #t:inttype{~(SIZE? t)}
  -> i:lbuffer uint8 (numbytes t)
  -> Stack (uint_t t)
    (requires fun h0 -> live h0 i)
    (ensures  fun h0 o h1 ->
      h0 == h1 /\ live h1 i /\
      o == BS.uint_from_bytes_le #t (as_seq h0 i))

inline_for_extraction
val uint_from_bytes_be:
    #t:inttype{~(SIZE? t)}
  -> i:lbuffer uint8 (numbytes t)
  -> Stack (uint_t t)
    (requires fun h0 -> live h0 i)
    (ensures  fun h0 o h1 ->
      h0 == h1 /\ live h1 i /\
      o == BS.uint_from_bytes_be #t (as_seq h0 i))

inline_for_extraction
val uint_to_bytes_le:
    #t:inttype{~(SIZE? t)}
  -> o:lbuffer uint8 (numbytes t)
  -> i:uint_t t
  -> Stack unit
    (requires fun h0 -> live h0 o)
    (ensures  fun h0 _ h1 ->
      live h1 o /\ modifies (loc_buffer o) h0 h1 /\
      as_seq h1 o == BS.uint_to_bytes_le #t i)

inline_for_extraction
val uint_to_bytes_be:
    #t:inttype{~(SIZE? t)}
  -> o:lbuffer uint8 (numbytes t)
  -> i:uint_t t
  -> Stack unit
    (requires fun h0 -> live h0 o)
    (ensures  fun h0 _ h1 ->
      live h1 o /\ modifies (loc_buffer o) h0 h1 /\
      as_seq h1 o == BS.uint_to_bytes_be #t i)

inline_for_extraction
val uints_from_bytes_le:
  #t:inttype
  -> #len:size_nat{len * numbytes t <= max_size_t}
  -> o:lbuffer (uint_t t) len
  -> clen:size_t{size_v clen == len}
  -> i:lbuffer uint8 (len * numbytes t) ->
  Stack unit
	(requires (fun h0 -> live h0 o /\ live h0 i))
	(ensures (fun h0 _ h1 -> modifies (loc_buffer o) h0 h1 /\
			      as_seq h1 o ==
			      (BS.uints_from_bytes_le #t #(len) (as_seq h0 i) )))

inline_for_extraction
val uints_from_bytes_be:
  #t:inttype -> #len:size_nat{len * numbytes t <= max_size_t} ->
  o:lbuffer (uint_t t) len ->
  clen:size_t{size_v clen == len} ->
  i:lbuffer uint8 (len * numbytes t) ->
  Stack unit
	(requires (fun h0 -> live h0 o /\ live h0 i))
	(ensures (fun h0 _ h1 -> modifies (loc_buffer o) h0 h1 /\
			      as_seq h1 o ==
			      (BS.uints_from_bytes_be #t #(len) (as_seq h0 i) )))

inline_for_extraction
val uints_to_bytes_le:
  #t:inttype
  -> #len:size_nat{len * numbytes t <= max_size_t}
  -> o:lbuffer uint8 (len * numbytes t)
  -> clen:size_t{size_v clen == len}
  -> i:lbuffer (uint_t t) len ->
  Stack unit
	(requires (fun h0 -> live h0 o /\ live h0 i))
	(ensures (fun h0 _ h1 -> modifies (loc_buffer o) h0 h1 /\
			      as_seq h1 o ==
			      (BS.uints_to_bytes_le #t #len (as_seq h0 i) )))

inline_for_extraction
val uints_to_bytes_be:
    #t:inttype
  -> #len:size_nat{len * numbytes t <= max_size_t}
  -> o:lbuffer uint8 (len * numbytes t)
  -> clen:size_t{size_v clen == len}
  -> i:lbuffer (uint_t t) len ->
  Stack unit
	(requires (fun h0 -> live h0 o /\ live h0 i /\ disjoint o i))
	(ensures (fun h0 _ h1 -> modifies (loc_buffer o) h0 h1 /\
			      as_seq h1 o ==
			      (BS.uints_to_bytes_be #t #len (as_seq h0 i) )))

inline_for_extraction
let uint32s_to_bytes_le (#len:size_nat{len * 32 <= max_size_t}) =
  uints_to_bytes_le #U32 #len

inline_for_extraction
let uint32s_from_bytes_le (#len:size_nat{len * 32 <= max_size_t}) = 
  uints_from_bytes_le #U32 #len
