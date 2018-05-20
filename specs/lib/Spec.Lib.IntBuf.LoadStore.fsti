module Spec.Lib.IntBuf.LoadStore

open FStar.HyperStack
open FStar.HyperStack.ST
open Spec.Lib.IntTypes

module LSeq = Spec.Lib.IntSeq
open Spec.Lib.IntBuf


inline_for_extraction
val uints_from_bytes_le:
  #t:m_inttype -> #len:size_nat{len `op_Multiply` numbytes t <= max_size_t} ->
  o:lbuffer (uint_t t) (len) ->
  i:lbuffer uint8 (len `op_Multiply` numbytes t) ->
  Stack unit
	(requires (fun h0 -> live h0 o /\ live h0 i))
	(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\
			      modifies1 o h0 h1 /\
			      as_lseq o h1 ==
			      (LSeq.uints_from_bytes_le #t #(len) (as_lseq i h0) )))

inline_for_extraction
val uints_from_bytes_be:
  #t:m_inttype -> #len:size_nat{len `op_Multiply` numbytes t <= max_size_t} ->
  o:lbuffer (uint_t t) (len) ->
  i:lbuffer uint8 (len `op_Multiply` numbytes t) ->
  Stack unit
	(requires (fun h0 -> live h0 o /\ live h0 i))
	(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\
			      modifies1 o h0 h1 /\
			      as_lseq o h1 ==
			      (LSeq.uints_from_bytes_be #t #(len) (as_lseq i h0) )))


inline_for_extraction
val uints_to_bytes_le:
  #t:m_inttype -> #len:size_nat{len `op_Multiply` numbytes t <= max_size_t} ->
  o:lbuffer uint8 (len `op_Multiply` numbytes t) ->
  i:lbuffer (uint_t t) (len) ->
  Stack unit
	(requires (fun h0 -> live h0 o /\ live h0 i))
	(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\
			      modifies1 o h0 h1 /\
			      as_lseq o h1 ==
			      (LSeq.uints_to_bytes_le #t #(len) (as_lseq i h0) )))

inline_for_extraction
val uints_to_bytes_be:
  #t:m_inttype -> #len:size_nat{len `op_Multiply` numbytes t <= max_size_t} ->
  o:lbuffer uint8 (len `op_Multiply` numbytes t) ->
  i:lbuffer (uint_t t) (len) ->
  Stack unit
	(requires (fun h0 -> live h0 o /\ live h0 i /\ disjoint o i))
	(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\
			      modifies1 o h0 h1 /\
			      as_lseq o h1 ==
			      (LSeq.uints_to_bytes_be #t #(len) (as_lseq i h0) )))

inline_for_extraction
let uint32s_to_bytes_le = uints_to_bytes_le #U32
inline_for_extraction
let uint32s_from_bytes_le = uints_from_bytes_le #U32
