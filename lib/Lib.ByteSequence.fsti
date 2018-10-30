module Lib.ByteSequence

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

/// Definition of byte-based sequences

inline_for_extraction
type bytes = seq uint8

inline_for_extraction
type lbytes (len:size_nat) = lseq uint8 len

inline_for_extraction
let to_lbytes (b:bytes{length b > 0 /\ length b < max_size_t}) : lbytes (length b) =
  to_lseq #uint8 b

inline_for_extraction
val lbytes_eq:#len:size_nat -> lseq uint8 len -> lseq uint8 len -> bool

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
val nat_from_bytes_be: b:bytes -> n:nat{n < pow2 (length b * 8)}

inline_for_extraction
val nat_from_bytes_le: b:bytes -> n:nat{n < pow2 (length b * 8)}

inline_for_extraction
val nat_to_bytes_be: len:nat -> n:nat{n < pow2 (8 * len)}
  -> b:bytes{length b == len /\ n == nat_from_intseq_be #U8 b}

inline_for_extraction
val nat_to_bytes_le: len:nat -> n:nat{n < pow2 (8 * len)}
  -> b:bytes{length b == len /\ n == nat_from_intseq_le #U8 b}

inline_for_extraction
val uint_to_bytes_le: #t:inttype -> #l:secrecy_level -> uint_t t l -> lbytes (numbytes t)

val index_uint_to_bytes_le: #t:inttype -> #l:secrecy_level -> u:uint_t t l
  -> Lemma
    (forall (i:nat{i < numbytes t}). index (uint_to_bytes_le u) i ==
                              u8 (uint_v u / pow2 (op_Multiply 8 i) % pow2 8))

inline_for_extraction
val uint_to_bytes_be: #t:inttype -> #l:secrecy_level -> u:uint_t t l -> lbytes (numbytes t)

inline_for_extraction
val uint_from_bytes_le: #t:inttype{~(t == U1)} -> #l:secrecy_level
  -> b:lbytes (numbytes t) -> uint_t t l

inline_for_extraction
val uint_from_bytes_be: #t:inttype{~(t == U1)} -> #l:secrecy_level
  -> lbytes (numbytes t) -> uint_t t l

inline_for_extraction
val uints_to_bytes_le: #t:inttype -> #l:secrecy_level -> #len:size_nat{len * numbytes t < pow2 32}
  -> lseq (uint_t t l) len -> lbytes (len * numbytes t)

inline_for_extraction
val uints_to_bytes_be: #t:inttype -> #l:secrecy_level -> #len:size_nat{len * numbytes t < pow2 32}
  -> lseq (uint_t t l) len -> lbytes (len * numbytes t)

inline_for_extraction
val uints_from_bytes_le: #t:inttype{~(t == U1)} -> #l:secrecy_level -> #len:size_nat{len * numbytes t < pow2 32}
  -> lbytes (len * numbytes t) -> lseq (uint_t t l) len

inline_for_extraction
val uints_from_bytes_be: #t:inttype{~(t == U1)} -> #l:secrecy_level -> #len:size_nat{len * numbytes t < pow2 32}
  -> lbytes (len * numbytes t) -> lseq (uint_t t l) len
