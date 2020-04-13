module Lib.IntVector.Serialize

open FStar.Mul
open Lib.Sequence
open Lib.IntTypes
open Lib.IntVector

module BSeq = Lib.ByteSequence
module LSeq = Lib.Sequence

#set-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
val vecs_from_bytes_le: vt:v_inttype -> w:width -> len:nat{len * (numbytes vt * w) <= max_size_t}
  -> b:lseq uint8 (len * (numbytes vt * w)) -> lseq (vec_t vt w) len

val index_vecs_from_bytes_le: vt:v_inttype -> w:width -> len:nat{len * (numbytes vt * w) <= max_size_t}
  -> b:lseq uint8 (len * (numbytes vt * w)) -> i:nat{i < len} ->
  Lemma ((vecs_from_bytes_le vt w len b).[i] == vec_from_bytes_le vt w (LSeq.sub b (i * (numbytes vt * w)) (numbytes vt * w)))


inline_for_extraction noextract
val vecs_from_bytes_be: vt:v_inttype -> w:width -> len:nat{len * (numbytes vt * w) <= max_size_t}
  -> b:lseq uint8 (len * (numbytes vt * w)) -> lseq (vec_t vt w) len

val index_vecs_from_bytes_be: vt:v_inttype -> w:width -> len:nat{len * (numbytes vt * w) <= max_size_t}
  -> b:lseq uint8 (len * (numbytes vt * w)) -> i:nat{i < len} ->
  Lemma ((vecs_from_bytes_be vt w len b).[i] == vec_from_bytes_be vt w (LSeq.sub b (i * (numbytes vt * w)) (numbytes vt * w)))

inline_for_extraction noextract
val vecs_to_bytes_le: #vt:v_inttype -> #w:width -> #len:nat{len * (numbytes vt * w) <= max_size_t}
  -> vl:lseq (vec_t vt w) len -> lseq uint8 (len * (numbytes vt * w))

val index_vecs_to_bytes_le: #vt:v_inttype -> #w:width -> #len:nat{len * (numbytes vt * w) <= max_size_t}
  -> vl:lseq (vec_t vt w) len -> i:nat{i < len * (numbytes vt * w)} ->
  Lemma ((vecs_to_bytes_le #vt #w #len vl).[i] == (vec_to_bytes_le vl.[i / (numbytes vt * w)]).[i % (numbytes vt * w)])

inline_for_extraction noextract
val vecs_to_bytes_be: #vt:v_inttype -> #w:width -> #len:nat{len * (numbytes vt * w) <= max_size_t}
  -> vl:lseq (vec_t vt w) len -> lseq uint8 (len * (numbytes vt * w))

val index_vecs_to_bytes_be: #vt:v_inttype -> #w:width -> #len:nat{len * (numbytes vt * w) <= max_size_t}
  -> vl:lseq (vec_t vt w) len -> i:nat{i < len * (numbytes vt * w)} ->
  Lemma ((vecs_to_bytes_be #vt #w #len vl).[i] == (vec_to_bytes_be vl.[i / (numbytes vt * w)]).[i % (numbytes vt * w)])


open Lib.Buffer
open FStar.HyperStack
open FStar.HyperStack.ST
module B = Lib.Buffer
module ST = FStar.HyperStack.ST


inline_for_extraction noextract
val vecs_load_le:
    #vt:v_inttype
  -> #w:width
  -> #len:size_t{v len * (numbytes vt * w) <= max_size_t}
  -> o:lbuffer (vec_t vt w) len
  -> i:lbuffer uint8 (len *! (size (numbytes vt) *! size w)) ->
  Stack unit
    (requires fun h -> live h i /\ live h o /\ B.disjoint i o)
    (ensures  fun h0 _ h1 ->
      modifies1 o h0 h1 /\
      as_seq h1 o == vecs_from_bytes_le vt w (v len) (as_seq h0 i))


inline_for_extraction noextract
val vecs_load_be:
    #vt:v_inttype
  -> #w:width
  -> #len:size_t{v len * (numbytes vt * w) <= max_size_t}
  -> o:lbuffer (vec_t vt w) len
  -> i:lbuffer uint8 (len *! (size (numbytes vt) *! size w)) ->
  Stack unit
    (requires fun h -> live h i /\ live h o /\ B.disjoint i o)
    (ensures  fun h0 _ h1 ->
      modifies1 o h0 h1 /\
      as_seq h1 o == vecs_from_bytes_be vt w (v len) (as_seq h0 i))


inline_for_extraction noextract
val vecs_store_le:
    #vt:v_inttype
  -> #w:width
  -> #len:size_t{v len * (numbytes vt * w) <= max_size_t}
  -> o:lbuffer uint8 (len *! (size (numbytes vt) *! size w))
  -> i:lbuffer (vec_t vt w) len ->
  Stack unit
    (requires fun h -> live h i /\ live h o /\ B.disjoint i o)
    (ensures  fun h0 _ h1 ->
      modifies1 o h0 h1 /\
      as_seq h1 o == vecs_to_bytes_le #vt #w #(v len) (as_seq h0 i))


inline_for_extraction noextract
val vecs_store_be:
    #vt:v_inttype
  -> #w:width
  -> #len:size_t{v len * (numbytes vt * w) <= max_size_t}
  -> o:lbuffer uint8 (len *! (size (numbytes vt) *! size w))
  -> i:lbuffer (vec_t vt w) len ->
  Stack unit
    (requires fun h -> live h i /\ live h o /\ B.disjoint i o)
    (ensures  fun h0 _ h1 ->
      modifies1 o h0 h1 /\
      as_seq h1 o == vecs_to_bytes_be #vt #w #(v len) (as_seq h0 i))
