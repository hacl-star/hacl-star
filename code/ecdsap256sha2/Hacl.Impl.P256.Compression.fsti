module Hacl.Impl.P256.Compression

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Spec.P256.Definitions


let notCompressedForm = lbuffer uint8 (size 65)
let compressedForm = lbuffer uint8 (size 64)

(* the name makes a lot of sense, doesnot it? *)

(* the function is to decode publickey, so NOT SCA resistant *)

(*void uECC_decompress(const uint8_t *compressed, uint8_t *public_key, uECC_Curve curve)  *)

val decompressionNotCompressed: b: notCompressedForm -> result: lbuffer uint8 (size 64) -> Stack bool 
  (requires fun h -> live h b /\ live h result /\ disjoint b result)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1)

val decompressionNotCompressed2: b: notCompressedForm -> result: lbuffer uint8 (size 64) -> Stack uint8
  (requires fun h -> live h b /\ live h result /\ disjoint b result)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1)


val decompressionCompressed: compressedForm -> result: point -> Stack bool 
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)
