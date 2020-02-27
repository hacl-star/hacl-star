module Hacl.Impl.PKCS11.External.KeyGen

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

val keyGenTest: b: lbuffer uint8 (size 32) ->
  Stack uint32 
    (requires fun h -> live h b)
    (ensures fun h0 _ h1 -> modifies (loc b) h0 h1)

let keyGenTest b = 
  memset b (u8 0) (size 32);
  (u32 0)
  
