module Hacl.Blake2bUnkeyed

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Spec.P256.Definitions

open Hacl.Blake2b_32 


val blake2b_32_u: result: lbuffer uint8 (size 32) -> mLen: size_t -> m: lbuffer uint8 mLen -> 
  Stack unit 
    (requires fun h -> live h result /\ live h m /\ disjoint result m)
    (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\
      as_seq h1 result == Spec.Blake2.blake2b (as_seq h0 m) 0 Seq.Base.empty 32
    )


let blake2b_32_u result mLen m = 
  blake2b (size 32) result mLen m (size 0) (null uint8)
