module Spec.Frodo.KEM.KeyGen

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open Spec.Matrix
open Spec.Frodo.Params
open Spec.Frodo.Pack
open Spec.Frodo.Sample

module LSeq = Lib.Sequence
module Matrix = Spec.Matrix

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val frodo_shake_r:
    a:frodo_alg
  -> c:uint8
  -> seed_se:lbytes (crypto_bytes a)
  -> output_len:size_nat
  -> lbytes output_len

let frodo_shake_r a c seed_se output_len =
  let tmp = LSeq.create 1 c in
  let shake_input_seed_se = LSeq.concat tmp seed_se in
  frodo_shake a (1 + crypto_bytes a) shake_input_seed_se output_len


val frodo_mul_add_as_plus_e:
    a:frodo_alg
  -> gen_a:frodo_gen_a
  -> seed_a:lbytes bytes_seed_a
  -> s_matrix:matrix (params_n a) params_nbar
  -> e_matrix:matrix (params_n a) params_nbar
  -> matrix (params_n a) params_nbar

let frodo_mul_add_as_plus_e a gen_a seed_a s_matrix e_matrix =
  params_n_sqr a;
  let a_matrix  = frodo_gen_matrix gen_a (params_n a) seed_a in
  let b_matrix  = Matrix.add (Matrix.mul_s a_matrix s_matrix) e_matrix in
  b_matrix


val frodo_mul_add_as_plus_e_pack:
    a:frodo_alg
  -> gen_a:frodo_gen_a
  -> seed_a:lbytes bytes_seed_a
  -> s_matrix:matrix (params_n a) params_nbar
  -> e_matrix:matrix (params_n a) params_nbar
  -> lbytes (publicmatrixbytes_len a)

let frodo_mul_add_as_plus_e_pack a gen_a seed_a s_matrix e_matrix =
  let b_matrix = frodo_mul_add_as_plus_e a gen_a seed_a s_matrix e_matrix in
  frodo_pack (params_logq a) b_matrix


val get_s_e_matrices:
    a:frodo_alg
  -> seed_se:lbytes (crypto_bytes a)
  -> matrix (params_n a) params_nbar & matrix (params_n a) params_nbar

let get_s_e_matrices a seed_se =
  let s_bytes_len = secretmatrixbytes_len a in
  let r = frodo_shake_r a (u8 0x5f) seed_se (2 * s_bytes_len) in
  let s_matrix = frodo_sample_matrix a (params_n a) params_nbar (LSeq.sub r 0 s_bytes_len) in
  let e_matrix = frodo_sample_matrix a (params_n a) params_nbar (LSeq.sub r s_bytes_len s_bytes_len) in
  s_matrix, e_matrix


val frodo_mul_add_as_plus_e_pack_shake:
    a:frodo_alg
  -> gen_a:frodo_gen_a
  -> seed_a:lbytes bytes_seed_a
  -> seed_se:lbytes (crypto_bytes a)
  -> tuple2 (lbytes (publicmatrixbytes_len a)) (lbytes (secretmatrixbytes_len a))

let frodo_mul_add_as_plus_e_pack_shake a gen_a seed_a seed_se =
  let s_matrix, e_matrix = get_s_e_matrices a seed_se in
  let b_bytes = frodo_mul_add_as_plus_e_pack a gen_a seed_a s_matrix e_matrix in
  let s_bytes = matrix_to_lbytes s_matrix in
  b_bytes, s_bytes


val crypto_kem_sk:
    a:frodo_alg
  -> s:lbytes (crypto_bytes a)
  -> pk:lbytes (crypto_publickeybytes a)
  -> s_bytes:lbytes (secretmatrixbytes_len a)
  -> lbytes (crypto_secretkeybytes a)

let crypto_kem_sk a s pk s_bytes =
  let sk = concat (concat s pk) s_bytes in
  let pkh = frodo_shake a (crypto_publickeybytes a) pk (bytes_pkhash a) in
  let sk_pkh = concat sk pkh in
  sk_pkh


val crypto_kem_keypair_:
    a:frodo_alg
  -> gen_a:frodo_gen_a
  -> coins:lbytes (2 * crypto_bytes a + bytes_seed_a)
  -> tuple2 (lbytes (crypto_publickeybytes a)) (lbytes (crypto_secretkeybytes a))

let crypto_kem_keypair_ a gen_a coins =
  expand_crypto_publickeybytes a;
  expand_crypto_secretkeybytes a;
  let s = LSeq.sub coins 0 (crypto_bytes a) in
  let seed_se = LSeq.sub coins (crypto_bytes a) (crypto_bytes a) in
  let z = LSeq.sub coins (2 * crypto_bytes a) bytes_seed_a in

  let seed_a = frodo_shake a bytes_seed_a z bytes_seed_a in
  let b_bytes, s_bytes = frodo_mul_add_as_plus_e_pack_shake a gen_a seed_a seed_se in

  let pk = concat seed_a b_bytes in
  let sk = crypto_kem_sk a s pk s_bytes in
  pk, sk


val crypto_kem_keypair:
    a:frodo_alg
  -> gen_a:frodo_gen_a
  -> state:Spec.Frodo.Random.state_t
  -> tuple2 (lbytes (crypto_publickeybytes a)) (lbytes (crypto_secretkeybytes a))

let crypto_kem_keypair a gen_a state =
  let coins, _ = Spec.Frodo.Random.randombytes_ state (2 * crypto_bytes a + bytes_seed_a) in
  crypto_kem_keypair_ a gen_a coins
