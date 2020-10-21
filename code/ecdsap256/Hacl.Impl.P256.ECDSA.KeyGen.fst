module Hacl.Impl.P256.ECDSA.KeyGen


open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteSequence

open Hacl.Impl.P256.DH



#set-options "--fuel 0 --ifuel 0 --z3rlimit 200"

val ecdsa_p256_keyGen_privateKey: random: lbuffer uint8 (size 32)
  -> privateKey: lbuffer uint8 (size 32) -> 
  Stack bool 
    (requires fun h -> live h random /\ live h privateKey /\ disjoint random privateKey)
    (ensures fun h0 flag h1 -> modifies (loc privateKey) h0 h1 /\ (
      let random = as_seq h0 random in 
      let prime = Spec.ECDSAP256.Definition.prime_p256_order in 
      if nat_from_bytes_be random > 0 && nat_from_bytes_be random < prime
      then 
	as_seq h1 privateKey == random /\
	flag == true /\
	nat_from_bytes_be (as_seq h1 privateKey) > 0 && 
	nat_from_bytes_be (as_seq h1 privateKey) < prime 
      else 
	flag == false))


let ecdsa_p256_keyGen_privateKey random privateKey = 
  let flag = Hacl.Impl.P256.Signature.Common.isMoreThanZeroLessThanOrder random in 
  if flag then 
    begin
      copy privateKey random;
      true 
    end
  else
    false


open Lib.ByteSequence

val ecdsa_p256_keyGen_publicKey: privateKey: lbuffer uint8 (size 32) 
  -> publicKey: lbuffer uint8 (size 64) -> 
  Stack bool
    (requires fun h -> live h privateKey /\ live h publicKey /\ disjoint privateKey publicKey)
    (ensures fun h0 r h1 ->  
      let pointX_n, pointY_n, pointZ_n = Spec.P256.secret_to_public (as_seq h0 privateKey) in
      let pointX, pointY, flag = 
      if Spec.P256.isPointAtInfinity (pointX_n, pointY_n, pointZ_n) then
	nat_to_bytes_be #SEC 32 pointX_n, nat_to_bytes_be #SEC 32 pointY_n, false
      else
	nat_to_bytes_be 32 pointX_n, nat_to_bytes_be 32 pointY_n, true in 

      modifies (loc publicKey) h0 h1 /\
      r == flag /\
      as_seq h1 (gsub publicKey (size 0) (size 32)) == pointX /\
      as_seq h1 (gsub publicKey (size 32) (size 32)) == pointY
    )


let ecdsa_p256_keyGen_publicKey privateKey publicKey = 
  ecp256dh_i publicKey privateKey


let ecdsa_p256_keyGen random privateKey publicKey = 
  let flagPrivateKey = ecdsa_p256_keyGen_privateKey random privateKey in 
  if not flagPrivateKey then false else
  ecdsa_p256_keyGen_publicKey privateKey publicKey
