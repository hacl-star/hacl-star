module Lib.ByteSequence

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

/// Definition of byte-based sequences

unfold inline_for_extraction
type bytes_l (l:secrecy_level) = seq (uint_t U8 l)

unfold inline_for_extraction
type lbytes_l (l:secrecy_level) (len:size_nat) = lseq (uint_t U8 l) len

unfold inline_for_extraction let bytes = bytes_l SEC
unfold inline_for_extraction let lbytes (len:size_nat) = lbytes_l SEC len
unfold inline_for_extraction let pub_bytes = bytes_l PUB
unfold inline_for_extraction let pub_lbytes (len:size_nat) = lbytes_l PUB len

(** Compares two buffers and declassifies the result *)
inline_for_extraction
val lbytes_eq: #len:size_nat -> b1:lbytes len -> b2:lbytes len -> b:bool{b <==> b1 == b2}

/// Constant for empty lbytes

let lbytes_empty: lbytes 0 = create 0 (u8 0)

/// Conversions between natural numbers and sequences

inline_for_extraction
val nat_from_intseq_be: #t:inttype -> #l:secrecy_level -> b:seq (uint_t t l)
  -> n:nat{n < pow2 (length b * bits t)}

inline_for_extraction
val nat_from_intseq_le: #t:inttype -> #l:secrecy_level
  -> b:seq (uint_t t l) -> n:nat{n < pow2 (length b * bits t)}

inline_for_extraction
val nat_from_bytes_be: #l:secrecy_level -> b:bytes_l l -> n:nat{n < pow2 (length b * 8)}

inline_for_extraction
val nat_from_bytes_le: #l:secrecy_level -> b:bytes_l l -> n:nat{n < pow2 (length b * 8)}

inline_for_extraction
val nat_to_bytes_be: #l:secrecy_level -> len:nat -> n:nat{n < pow2 (8 * len)}
  -> b:bytes_l l{length b == len /\ n == nat_from_intseq_be #U8 b}

inline_for_extraction
val nat_to_bytes_le: #l:secrecy_level -> len:nat -> n:nat{n < pow2 (8 * len)}
  -> b:bytes_l l{length b == len /\ n == nat_from_intseq_le #U8 b}

inline_for_extraction
val uint_to_bytes_le: #t:inttype -> #l:secrecy_level -> uint_t t l -> lbytes_l l (numbytes t)

val index_uint_to_bytes_le: #t:inttype -> #l:secrecy_level -> u:uint_t t l
  -> Lemma
    (forall (i:nat{i < numbytes t}). index (uint_to_bytes_le #t #l u) i ==
                              uint #U8 #l (uint_v u / pow2 (op_Multiply 8 i) % pow2 8))

inline_for_extraction
val uint_to_bytes_be: #t:inttype -> #l:secrecy_level -> u:uint_t t l -> lbytes_l l (numbytes t)

inline_for_extraction
val uint_from_bytes_le: #t:inttype{~(t == U1)} -> #l:secrecy_level
  -> b:lbytes_l l (numbytes t) -> uint_t t l

inline_for_extraction
val uint_from_bytes_be: #t:inttype{~(t == U1)} -> #l:secrecy_level
  -> lbytes_l l (numbytes t) -> uint_t t l

inline_for_extraction
val uints_to_bytes_le: #t:inttype -> #l:secrecy_level -> #len:size_nat{len * numbytes t < pow2 32}
  -> lseq (uint_t t l) len -> lbytes_l l (len * numbytes t)

inline_for_extraction
val uints_to_bytes_be: #t:inttype -> #l:secrecy_level -> #len:size_nat{len * numbytes t < pow2 32}
  -> lseq (uint_t t l) len -> lbytes_l l (len * numbytes t)

inline_for_extraction
val uints_from_bytes_le: #t:inttype{~(t == U1)} -> #l:secrecy_level -> #len:size_nat{len * numbytes t < pow2 32}
  -> lbytes_l l (len * numbytes t) -> lseq (uint_t t l) len

inline_for_extraction
val uints_from_bytes_be: #t:inttype{~(t == U1)} -> #l:secrecy_level -> #len:size_nat{len * numbytes t < pow2 32}
  -> lbytes_l l (len * numbytes t) -> lseq (uint_t t l) len
