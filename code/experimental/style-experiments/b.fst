module B
open Lib.IntTypes

type t = | M32 | M64

inline_for_extraction
let elem_t (v:t) = 
  match v with
  | M32 -> uint32
  | M64 -> uint64

inline_for_extraction
let elem_zero (v:t) : elem_t v = 
  match v with
  | M32 -> u32 0
  | M64 -> u64 0

