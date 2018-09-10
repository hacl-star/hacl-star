module Lib.ByteSequence

open Lib.IntTypes
open Lib.Sequence

/// Definition of byte-based sequences
///

type bytes = seq uint8

type lbytes (len:size_nat) = lseq uint8 len

///
val to_lbytes: b:bytes -> lbytes (length b)

val to_bytes: #len:size_nat -> b:lbytes len -> o:bytes{length o == len}

/// Conversions between natural numbers and sequences
///

val nat_from_intseq_be: #t:m_inttype -> #len:size_nat -> b:intseq t len -> Tot (n:nat{n < pow2 (len `op_Multiply` bits t)})

val nat_from_intseq_le: #t:m_inttype -> #len:size_nat -> b:intseq t len -> Tot (n:nat{n < pow2 (len `op_Multiply` bits t)})

val nat_from_bytes_be: #len:size_nat -> b:lbytes len -> Tot (n:nat{n < pow2 (len `op_Multiply` 8)})

val nat_from_bytes_le: #len:size_nat -> b:lbytes len -> Tot (n:nat{n < pow2 (len `op_Multiply` 8)})

val nat_to_bytes_be: len:size_nat -> n:nat{n < pow2 (8 `op_Multiply` len)} ->  Tot (b:lbytes len {n == nat_from_intseq_be #U8 #len b})

val nat_to_bytes_le: len:size_nat -> n:nat{n < pow2 (8 `op_Multiply` len)} ->  Tot (b:lbytes len {n == nat_from_intseq_le #U8 #len b})

val uint_to_bytes_le: #t:m_inttype -> u:uint_t t -> lbytes (numbytes t)

val index_uint_to_bytes_le: #t:m_inttype -> u:uint_t t
  -> Lemma
    (forall (i:nat{i < numbytes t}). index (uint_to_bytes_le u) i ==
                              u8 (uint_v u / pow2 (op_Multiply 8 i) % pow2 8))
val uint_to_bytes_be: #t:m_inttype -> u:uint_t t -> lbytes (numbytes t)

val uint_from_bytes_le: #t:m_inttype -> lbytes (numbytes t) -> u:uint_t t

val uint_from_bytes_be: #t:m_inttype -> lbytes (numbytes t) -> u:uint_t t

val uints_to_bytes_le: #t:m_inttype -> #len:size_nat{len `op_Multiply` numbytes t <= max_size_t} -> intseq t len -> lbytes (len `op_Multiply` numbytes t)

val uints_to_bytes_be: #t:m_inttype -> #len:size_nat{len `op_Multiply` numbytes t <= max_size_t} -> intseq t len -> lbytes (len `op_Multiply` numbytes t)

val uints_from_bytes_le: #t:m_inttype -> #len:size_nat{len `op_Multiply` numbytes t <= max_size_t} -> lbytes (len `op_Multiply` numbytes t) -> intseq t len

val uints_from_bytes_be: #t:m_inttype -> #len:size_nat{len `op_Multiply` numbytes t <= max_size_t} -> lbytes (len `op_Multiply` numbytes t) -> intseq t len
