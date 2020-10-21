module Hacl.Impl.P256.ECDSA.KeyGen

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteSequence


val ecdsa_p256_keyGen: random: lbuffer uint8 (size 32) 
  -> privateKey: lbuffer uint8 (size 32) 
  -> publicKey: lbuffer uint8 (size 64) -> 
  Stack bool
    (requires fun h -> live h random /\ live h privateKey /\ live h publicKey /\ 
      disjoint privateKey random /\ disjoint privateKey publicKey)
    (ensures fun h0 r h1 -> 
      modifies (loc publicKey |+| loc privateKey) h0 h1 /\ (
      let random = as_seq h0 random in 
      let prKey = as_seq h1 privateKey in 
      
      let prime = Spec.ECDSAP256.Definition.prime_p256_order in 
      
      if nat_from_bytes_be random > 0 && nat_from_bytes_be random < prime then
	prKey == random /\ (
	let pointX_n, pointY_n, pointZ_n = Spec.P256.secret_to_public prKey  in
	let pointX, pointY, flag = 
	if Spec.P256.isPointAtInfinity (pointX_n, pointY_n, pointZ_n) then
	  nat_to_bytes_be #SEC 32 pointX_n, nat_to_bytes_be #SEC 32 pointY_n, false
	else
	  nat_to_bytes_be 32 pointX_n, nat_to_bytes_be 32 pointY_n, true in 
	
	r == flag /\
	as_seq h1 (gsub publicKey (size 0) (size 32)) == pointX /\
	as_seq h1 (gsub publicKey (size 32) (size 32)) == pointY)
    else 
      r == false))
