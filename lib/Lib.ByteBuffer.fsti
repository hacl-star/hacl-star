module Lib.ByteBuffer

open FStar.HyperStack
open FStar.HyperStack.ST
open Lib.IntTypes
open Lib.Sequence
open Lib.Buffer

module ByteSeq = Lib.ByteSequence

(* Integer Parsing and Serialization *)

inline_for_extraction
val uint_from_bytes_le:
  #t:m_inttype ->
  i:lbuffer uint8 (numbytes t) ->
  Stack (uint_t t)
	(requires (fun h0 -> live h0 i))
	(ensures (fun h0 o h1 -> preserves_live h0 h1 /\
			      o == ByteSeq.uint_from_bytes_le #t (as_lseq i h0)))

inline_for_extraction
val uint_from_bytes_be:
  #t:m_inttype ->
  i:lbuffer uint8 (numbytes t) ->
  Stack (uint_t t)
	(requires (fun h0 -> live h0 i))
	(ensures (fun h0 o h1 -> preserves_live h0 h1 /\
			      o == ByteSeq.uint_from_bytes_be #t (as_lseq i h0)))

inline_for_extraction
val uint_to_bytes_le:
  #t:m_inttype ->
  o:lbuffer uint8 (numbytes t) ->
  i:uint_t t ->
  Stack unit
	(requires (fun h0 -> live h0 o))
	(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\
			      modifies1 o h0 h1 /\
			      as_lseq o h1 == ByteSeq.uint_to_bytes_le #t i))

inline_for_extraction
val uint_to_bytes_be:
  #t:m_inttype ->
  o:lbuffer uint8 (numbytes t) ->
  i:uint_t t ->
  Stack unit
	(requires (fun h0 -> live h0 o))
	(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\
			      modifies1 o h0 h1 /\
			      as_lseq o h1 == ByteSeq.uint_to_bytes_be #t i))


inline_for_extraction
val uints_from_bytes_le:
  #t:m_inttype -> #len:size_nat{len `op_Multiply` numbytes t <= max_size_t} ->
  o:lbuffer (uint_t t) (len) ->
  clen:size_t{size_v clen == len} ->
  i:lbuffer uint8 (len `op_Multiply` (numbytes t)) ->
  Stack unit
	(requires (fun h0 -> live h0 o /\ live h0 i))
	(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\
			      modifies1 o h0 h1 /\
			      as_lseq o h1 ==
			      (ByteSeq.uints_from_bytes_le #t #(len) (as_lseq i h0) )))

inline_for_extraction
val uints_from_bytes_be:
  #t:m_inttype -> #len:size_nat{len `op_Multiply` numbytes t <= max_size_t} ->
  o:lbuffer (uint_t t) (len) ->
  clen:size_t{size_v clen == len} ->
  i:lbuffer uint8 (len `op_Multiply` ((numbytes t))) ->
  Stack unit
	(requires (fun h0 -> live h0 o /\ live h0 i))
	(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\
			      modifies1 o h0 h1 /\
			      as_lseq o h1 ==
			      (ByteSeq.uints_from_bytes_be #t #(len) (as_lseq i h0) )))


inline_for_extraction
val uints_to_bytes_le:
  #t:m_inttype -> #len:size_nat{len `op_Multiply` numbytes t <= max_size_t} ->
  o:lbuffer uint8 (len `op_Multiply` ((numbytes t))) ->
  clen:size_t{size_v clen == len} ->
  i:lbuffer (uint_t t) (len) ->
  Stack unit
	(requires (fun h0 -> live h0 o /\ live h0 i))
	(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\
			      modifies1 o h0 h1 /\
			      as_lseq o h1 ==
			      (ByteSeq.uints_to_bytes_le #t #(len) (as_lseq i h0) )))

inline_for_extraction
val uints_to_bytes_be:
  #t:m_inttype -> #len:size_nat{len `op_Multiply` numbytes t <= max_size_t} ->
  o:lbuffer uint8 (len `op_Multiply` ((numbytes t))) ->
  clen:size_t{size_v clen == len} ->
  i:lbuffer (uint_t t) (len) ->
  Stack unit
	(requires (fun h0 -> live h0 o /\ live h0 i /\ disjoint o i))
	(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\
			      modifies1 o h0 h1 /\
			      as_lseq o h1 ==
			      (ByteSeq.uints_to_bytes_be #t #(len) (as_lseq i h0) )))

inline_for_extraction
let uint32s_to_bytes_le = uints_to_bytes_le #U32
inline_for_extraction
let uint32s_from_bytes_le = uints_from_bytes_le #U32
