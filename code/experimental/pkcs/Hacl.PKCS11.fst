module Hacl.PKCS11

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer
open FStar.Buffer.Quantifiers


val main_: unit -> Stack FStar.UInt32.t
      (requires (fun h -> True))
      (ensures (fun h0 _ h1 -> True))
      
let main_ () = 
	PKCS11.Test.a 10ul