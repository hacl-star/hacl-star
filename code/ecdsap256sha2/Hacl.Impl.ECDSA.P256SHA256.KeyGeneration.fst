module Hacl.Impl.ECDSA.P256SHA256.KeyGeneration

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.P256.Definitions
open Hacl.Impl.LowLevel
open Hacl.Impl.P256
open Hacl.Spec.P256.MontgomeryMultiplication
open Hacl.Impl.ECDSA.MontgomeryMultiplication
open Hacl.Impl.ECDSA.MM.Exponent

open Hacl.Spec.ECDSAP256.Definition
open Hacl.Spec.ECDSA
open Hacl.Spec.P256 
open Hacl.Spec.P256.Lemmas

open Hacl.Impl.P256.PointAdd
open Hacl.Impl.P256.LowLevel

open Hacl.Impl.ECDSA.P256SHA256.Common
open Lib.ByteSequence

open FStar.Mul 


#set-options "--z3rlimit 100"

val key_gen: result: lbuffer uint8 (size 64) -> privKey: lbuffer uint8 (size 32) -> 
  Stack unit 
    (requires fun h -> 
      live h result /\ live h privKey /\
      disjoint result privKey /\
      nat_from_bytes_le (as_seq h privKey) < prime_p256_order
    )
    (ensures fun h0 _ h1 -> 
      modifies (loc result) h0 h1 /\
      (
	let publicKeyX = nat_from_bytes_le (as_seq h1 (gsub result (size 0) (size 32))) in 
	let publicKeyY = nat_from_bytes_le (as_seq h1 (gsub result (size 32) (size 32))) in 
	let xN, yN, _ = secret_to_public (as_seq h0 privKey) in 
	publicKeyX < prime256 /\ 
	publicKeyY < prime256 /\
	publicKeyX == xN /\
	publicKeyY == yN
      )
    )

let key_gen result privKey = 
  push_frame();
  let h0 = ST.get() in 
    let resultAsFelem = create (size 12) (u64 0) in 
      let resultFelemX = sub resultAsFelem (size 0) (size 4) in 
      let resultFelemY = sub resultAsFelem (size 4) (size 4) in 
    let tempBuffer = create (size 100) (u64 0) in 
      let resultX = sub result (size 0) (size 32) in 
      let resultY = sub result (size 32) (size 32) in 
    secretToPublic resultAsFelem privKey tempBuffer;
  let h1 = ST.get() in 

    toUint8 resultFelemX resultX;
    toUint8 resultFelemY resultY;
      lemma_core_1 resultFelemX h1;
      lemma_core_1 resultFelemY h1;
  pop_frame()
