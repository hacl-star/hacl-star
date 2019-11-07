module Spec.Frodo.KEM

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open Spec.Frodo.Params

module KeyGen = Spec.Frodo.KEM.KeyGen
module Encaps = Spec.Frodo.KEM.Encaps
module Decaps = Spec.Frodo.KEM.Decaps

val crypto_kem_keypair:
    state:Spec.Frodo.Random.state_t
  -> lbytes crypto_publickeybytes & lbytes crypto_secretkeybytes
let crypto_kem_keypair state = KeyGen.crypto_kem_keypair state

val crypto_kem_enc:
    state:Spec.Frodo.Random.state_t
  -> pk:lbytes crypto_publickeybytes
  -> lbytes crypto_ciphertextbytes & lbytes crypto_bytes
let crypto_kem_enc state pk = Encaps.crypto_kem_enc state pk

val crypto_kem_dec:
    ct:lbytes crypto_ciphertextbytes
  -> sk:lbytes crypto_secretkeybytes
  -> ss:lbytes crypto_bytes
let crypto_kem_dec ct sk = Decaps.crypto_kem_dec ct sk
