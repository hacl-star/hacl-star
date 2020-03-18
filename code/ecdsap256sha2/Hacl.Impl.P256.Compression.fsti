module Hacl.Impl.P256.Compression

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Spec.P256.Definitions


let notCompressedForm = lbuffer uint8 (size 64)
let compressedForm = lbuffer uint8 (size 64)

(* the name makes a lot of sense, doesnot it? *)
val decompressionNotCompressed: notCompressedForm -> result: point -> Stack bool 
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

val decompressionCompressed: compressedForm -> result: point -> Stack bool 
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)
