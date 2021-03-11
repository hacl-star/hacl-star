module Spec.Frodo.KEM

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open Spec.Frodo.Params

module KeyGen = Spec.Frodo.KEM.KeyGen
module Encaps = Spec.Frodo.KEM.Encaps
module Decaps = Spec.Frodo.KEM.Decaps

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val crypto_kem_keypair:
    a:frodo_alg
  -> gen_a:frodo_gen_a
  -> state:Spec.Frodo.Random.state_t
  -> lbytes (crypto_publickeybytes a) & lbytes (crypto_secretkeybytes a)

let crypto_kem_keypair a gen_a state = KeyGen.crypto_kem_keypair a gen_a state


val crypto_kem_enc:
    a:frodo_alg
  -> gen_a:frodo_gen_a
  -> state:Spec.Frodo.Random.state_t
  -> pk:lbytes (crypto_publickeybytes a)
  -> lbytes (crypto_ciphertextbytes a) & lbytes (crypto_bytes a)

let crypto_kem_enc a gen_a state pk = Encaps.crypto_kem_enc a gen_a state pk


val crypto_kem_dec:
    a:frodo_alg
  -> gen_a:frodo_gen_a
  -> ct:lbytes (crypto_ciphertextbytes a)
  -> sk:lbytes (crypto_secretkeybytes a)
  -> lbytes (crypto_bytes a)

let crypto_kem_dec a gen_a ct sk = Decaps.crypto_kem_dec a gen_a ct sk
