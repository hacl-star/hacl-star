module Spec.Lib.Endian

open Spec.Lib.IntBuf
open Spec.Lib.IntBuf.Lemmas
open Spec.Lib.IntTypes
open FStar.HyperStack.ST

#reset-options "--z3rlimit 50"
let uint32_from_bytes_le (i:lbuffer uint8 4) = C.load32_le i
let uint32_to_bytes_le (o:lbuffer uint8 4) i = C.store32_le o i

