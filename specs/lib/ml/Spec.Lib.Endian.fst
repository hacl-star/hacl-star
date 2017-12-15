module Spec.Lib.Endian

open Spec.Lib.IntBuf
open Spec.Lib.IntBuf.Lemmas
open Spec.Lib.IntTypes
open FStar.HyperStack.ST

#reset-options "--z3rlimit 50"
let uint32_from_bytes_le (i:lbuffer uint8 4) = 
  let x0:uint32 = to_u32 #U8 i.(size 0) in
  let x1:uint32 = to_u32 #U8 i.(size 1) in
  let x2:uint32 = to_u32 #U8 i.(size 2) in
  let x3:uint32 = to_u32 #U8 i.(size 3) in
  (shift_left #U32 x0 (u32 24)) |. (x1 <<. u32 16) |. (x2 <<. u32 8) |. x3

