module Lib.ByteSequence.Tuples

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence



let size_nat_tuple = len:size_nat{2 <= len /\ len <= 14}

inline_for_extraction
let ltuple (a:Type0) (len:size_nat_tuple) =
  match len with
  | 2 -> tuple2 a a
  | 3 -> tuple3 a a a
  | 4 -> tuple4 a a a a
  | 5 -> tuple5 a a a a a
  | 6 -> tuple6 a a a a a a
  | 7 -> tuple7 a a a a a a a
  | 8 -> tuple8 a a a a a a a a
  | 9 -> tuple9 a a a a a a a a a
  | 10 -> tuple10 a a a a a a a a a a
  | 11 -> tuple11 a a a a a a a a a a a
  | 12 -> tuple12 a a a a a a a a a a a a
  | 13 -> tuple13 a a a a a a a a a a a a a
  | 14 -> tuple14 a a a a a a a a a a a a a a


inline_for_extraction
val expand: #a:Type0 -> #len:size_nat_tuple -> lseq a len -> ltuple a len

inline_for_extraction
val collapse: #a:Type0 -> #len:size_nat_tuple -> zero:a -> ltuple a len -> lseq a len

inline_for_extraction
val ltuple_uints_to_bytes_le: #t:inttype{unsigned t} -> #l:secrecy_level -> #len:size_nat_tuple
  -> ltuple (uint_t t l) len -> Tot (lbytes_l l (len * numbytes t))

inline_for_extraction
val ltuple_uints_to_bytes_be: #t:inttype{unsigned t} -> #l:secrecy_level -> #len:size_nat_tuple
  -> ltuple (uint_t t l) len -> Tot (lbytes_l l (len * numbytes t))

inline_for_extraction
val ltuple_uints_from_bytes_le: #t:inttype{unsigned t /\ ~(t == U1)} -> #l:secrecy_level -> #len:size_nat_tuple
  -> lbytes_l l (len * numbytes t) -> Tot (ltuple (uint_t t l) len)

inline_for_extraction
val ltuple_uints_from_bytes_be: #t:inttype{unsigned t /\ ~(t == U1)} -> #l:secrecy_level -> #len:size_nat_tuple
  -> lbytes_l l (len * numbytes t) -> Tot (ltuple (uint_t t l) len)
