module Spec.Lib.Endian

open Spec.Lib.IntBuf
open Spec.Lib.IntBuf.Lemmas
open Spec.Lib.IntTypes
open FStar.HyperStack.ST

#reset-options "--z3rlimit 50"
let uint32_from_bytes_le (i:lbuffer uint8 4) = C.load32_le i

let uint64_from_bytes_be (i:lbuffer uint8 8) = C.load64_be i

let uint64_to_bytes_be (i:lbuffer uint8 8) (z:uint64) = C.store64_be i z


