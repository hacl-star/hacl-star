module Spec.Frodo.KEM.KeyGen

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open FStar.Mul
open FStar.Math.Lemmas

open Spec.Matrix
open Spec.Frodo.Lemmas
open Spec.Frodo.Params
open Spec.Frodo.KEM
open Spec.Frodo.Encode
open Spec.Frodo.Pack
open Spec.Frodo.Sample

module Seq = Lib.Sequence
module Matrix = Spec.Matrix

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let crypto_publicmatrixbytes: size_nat =
  params_logq * params_n * params_nbar / 8

val update_pk:
    seed_a:lbytes bytes_seed_a
  -> b:lbytes crypto_publicmatrixbytes
  -> res:lbytes crypto_publickeybytes
    {Seq.sub res 0 bytes_seed_a == seed_a /\
     Seq.sub res bytes_seed_a crypto_publicmatrixbytes == b}
let update_pk seed_a b =
  let pk = Seq.create crypto_publickeybytes (u8 0) in
  let pk = update_sub pk 0 bytes_seed_a seed_a in
  let pk = update_sub pk bytes_seed_a crypto_publicmatrixbytes b in
  eq_intro (Seq.sub pk 0 bytes_seed_a) seed_a;
  pk

val lemma_update_pk:
    seed_a:lbytes bytes_seed_a
  -> b:lbytes crypto_publicmatrixbytes
  -> pk:lbytes crypto_publickeybytes
  -> Lemma
    (requires
      Seq.sub pk 0 bytes_seed_a == seed_a /\
      Seq.sub pk bytes_seed_a crypto_publicmatrixbytes == b)
    (ensures pk == update_pk seed_a b)
let lemma_update_pk seed_a b pk =
  let pk1 = update_pk seed_a b in
  FStar.Seq.Properties.lemma_split pk bytes_seed_a;
  FStar.Seq.Properties.lemma_split pk1 bytes_seed_a

val update_sk:
    s:lbytes crypto_bytes
  -> pk:lbytes crypto_publickeybytes
  -> s_bytes:lbytes (2 * params_n * params_nbar)
  -> res:lbytes crypto_secretkeybytes
    {Seq.sub res 0 crypto_bytes == s /\
     Seq.sub res crypto_bytes crypto_publickeybytes == pk /\
     Seq.sub res (crypto_bytes + crypto_publickeybytes) (2 * params_n * params_nbar) == s_bytes}
let update_sk s pk s_bytes =
  let sk = Seq.create crypto_secretkeybytes (u8 0) in
  let sk = update_sub sk 0 crypto_bytes s in
  let sk = update_sub sk crypto_bytes crypto_publickeybytes pk in
  eq_intro (Seq.sub sk 0 crypto_bytes) s;
  let sk = update_sub sk (crypto_bytes + crypto_publickeybytes) (2 * params_n * params_nbar) s_bytes in
  eq_intro (Seq.sub sk 0 crypto_bytes) s;
  eq_intro (Seq.sub sk crypto_bytes crypto_publickeybytes) pk;
  sk

val lemma_update_sk:
    s:lbytes crypto_bytes
  -> pk:lbytes crypto_publickeybytes
  -> s_bytes:lbytes (2 * params_n * params_nbar)
  -> sk:lbytes crypto_secretkeybytes
  -> Lemma
    (requires
      Seq.sub sk 0 crypto_bytes == s /\
      Seq.sub sk crypto_bytes crypto_publickeybytes == pk /\
      Seq.sub sk (crypto_bytes + crypto_publickeybytes) (2 * params_n * params_nbar) == s_bytes)
    (ensures sk == update_sk s pk s_bytes)
let lemma_update_sk s pk s_bytes sk =
  let sk1 = update_sk s pk s_bytes in
  FStar.Seq.Properties.lemma_split (Seq.sub sk 0 (crypto_bytes + crypto_publickeybytes)) crypto_bytes;
  FStar.Seq.Properties.lemma_split (Seq.sub sk1 0 (crypto_bytes + crypto_publickeybytes)) crypto_bytes;
  FStar.Seq.Properties.lemma_split sk (crypto_bytes + crypto_publickeybytes);
  FStar.Seq.Properties.lemma_split sk1 (crypto_bytes + crypto_publickeybytes)

val frodo_mul_add_as_plus_e_pack:
    seed_a:lbytes bytes_seed_a
  -> seed_e:lbytes crypto_bytes
  -> tuple2 (lbytes crypto_publicmatrixbytes) (lbytes (2 * params_n * params_nbar))
let frodo_mul_add_as_plus_e_pack seed_a seed_e =
  assert (params_logq * (params_n * params_nbar / 8) =
          params_logq * params_n * params_nbar / 8);
  assert (params_n * params_nbar <= max_size_t /\ params_nbar % 8 = 0);
  assert (forall (j:nat{j < params_n * params_nbar / 8}).
      params_logq * j + params_logq <= params_logq * (params_n * params_nbar / 8) /\
      0 <= params_logq * j);
  let a_matrix = frodo_gen_matrix params_n bytes_seed_a seed_a in
  let s_matrix = frodo_sample_matrix params_n params_nbar crypto_bytes seed_e (u16 1) in
  let s_bytes = matrix_to_lbytes s_matrix in
  let e_matrix = frodo_sample_matrix params_n params_nbar crypto_bytes seed_e (u16 2) in
  let b_matrix = Matrix.add (Matrix.mul_s a_matrix s_matrix) e_matrix in
  let b = frodo_pack b_matrix params_logq in
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
  let pk = update_pk seed_a b in
  let sk = update_sk s pk s_bytes in
  pk, sk

val crypto_kem_keypair: state:Spec.Frodo.Random.state_t
  -> tuple2 (lbytes crypto_publickeybytes) (lbytes crypto_secretkeybytes)
let crypto_kem_keypair state =
  let coins, _ = Spec.Frodo.Random.randombytes_ state (2 * crypto_bytes + bytes_seed_a) in
  crypto_kem_keypair_ coins
