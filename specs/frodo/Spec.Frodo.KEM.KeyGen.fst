module Spec.Frodo.KEM.KeyGen

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open FStar.Mul

open Spec.Matrix
open Spec.Frodo.Params
open Spec.Frodo.Pack
open Spec.Frodo.Sample

module Seq = Lib.Sequence
module Matrix = Spec.Matrix

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let crypto_publicmatrixbytes: size_nat =
  params_logq * params_n * params_nbar / 8

val frodo_mul_add_as_plus_e_pack:
    seed_a:lbytes bytes_seed_a
  -> seed_e:lbytes crypto_bytes
  -> tuple2 (lbytes crypto_publicmatrixbytes) (lbytes (2 * params_n * params_nbar))
let frodo_mul_add_as_plus_e_pack seed_a seed_e =
  assert (2 * params_n * params_nbar <= max_size_t /\ params_nbar % 8 = 0);
  let a_matrix = frodo_gen_matrix params_n bytes_seed_a seed_a in
  let s_matrix = frodo_sample_matrix params_n params_nbar crypto_bytes seed_e (u16 1) in
  let s_bytes = matrix_to_lbytes s_matrix in
  let e_matrix = frodo_sample_matrix params_n params_nbar crypto_bytes seed_e (u16 2) in
  let b_matrix = Matrix.add (Matrix.mul_s a_matrix s_matrix) e_matrix in
  let b = frodo_pack params_logq b_matrix in
  b, s_bytes

val crypto_kem_keypair_:
    coins:lbytes (2 * crypto_bytes + bytes_seed_a)
  -> tuple2 (lbytes crypto_publickeybytes) (lbytes crypto_secretkeybytes)
let crypto_kem_keypair_ coins =
  assert (bytes_seed_a + crypto_publicmatrixbytes = crypto_publickeybytes);
  let s = Seq.sub coins 0 crypto_bytes in
  let seed_e = Seq.sub coins crypto_bytes crypto_bytes in
  let z = Seq.sub coins (2 * crypto_bytes) bytes_seed_a in
  let seed_a = frodo_prf_spec bytes_seed_a z (u16 0) bytes_seed_a in
  let b, s_bytes = frodo_mul_add_as_plus_e_pack seed_a seed_e in
  let pk = concat seed_a b in
  let sk = concat (concat s pk) s_bytes in
  pk, sk

val crypto_kem_keypair:
    state:Spec.Frodo.Random.state_t
  -> tuple2 (lbytes crypto_publickeybytes) (lbytes crypto_secretkeybytes)
let crypto_kem_keypair state =
  let coins, _ = Spec.Frodo.Random.randombytes_ state (2 * crypto_bytes + bytes_seed_a) in
  crypto_kem_keypair_ coins
