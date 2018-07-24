module Spec.Frodo

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open FStar.Mul
open FStar.Math.Lemmas

open Spec.Matrix
open Spec.Frodo.Keccak
open Spec.Frodo.Lemmas
open Spec.Frodo.Params
open Spec.Frodo.Encode
open Spec.Frodo.Pack

module Seq = Lib.Sequence

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.* +FStar.Pervasives -Spec.* +Spec.Frodo +Spec.Frodo.Params'"

val lbytes_eq:
    #len: size_nat
  -> a: lbytes len
  -> b: lbytes len
  -> bool
let lbytes_eq #len a b =
  let open Lib.RawIntTypes in
  repeati len
  (fun i res ->
    res && (uint_to_nat a.[i] = uint_to_nat b.[i])
  ) true

let cshake_frodo = cshake128_frodo

let params_q: size_nat =
  pow2_lt_compat 32 params_logq;
  pow2 params_logq

let bytes_mu: size_nat =
  (params_extracted_bits * params_nbar * params_nbar) / 8

let crypto_publickeybytes: size_nat =
  bytes_seed_a + (params_logq * params_n * params_nbar) / 8

let crypto_secretkeybytes: size_nat =
  crypto_bytes + crypto_publickeybytes + 2 * params_n * params_nbar

let crypto_ciphertextbytes: size_nat =
  ((params_nbar * params_n + params_nbar * params_nbar) * params_logq) / 8 + crypto_bytes

val frodo_sample: r:uint16 -> uint16
let frodo_sample r =
  let open Lib.RawIntTypes in
  let t = r >>. u32 1 in
  let r0 = r &. u16 1 in
  mod_mask_lemma r (u32 1);
  uintv_extensionality (mod_mask (u32 1)) (u16 1);
  assert (uint_v r0 == 0 \/ uint_v r0 == 1);
  let e = 0 in
  let e =
    repeati_inductive
      (cdf_table_len - 1)
      (fun z e -> 0 <= e /\ e <= z /\ z < cdf_table_len)
      (fun z e -> let e = if (uint_to_nat t > cdf_table.[z]) then e + 1 else e in e)
      e
  in
  let e = (FStar.Math.Lib.powx (-1) (uint_to_nat r0)) * e in
  assert_norm (FStar.Math.Lib.powx (-1) 1 == -1);
  assert_norm (FStar.Math.Lib.powx (-1) 0 == 1);
  assert (-cdf_table_len < e /\ e < cdf_table_len);
  u16 (e % modulus U16)

val frodo_sample_matrix:
    n1:size_nat
  -> n2:size_nat{2 * n1 * n2 < max_size_t}
  -> seedLen:size_nat
  -> seed:lbytes seedLen
  -> ctr:uint16
  -> matrix n1 n2
let frodo_sample_matrix n1 n2 seedLen seed ctr =
  let r = cshake_frodo seedLen seed ctr (2 * n1 * n2) in
  let res = Matrix.create n1 n2 in
  repeati n1
  (fun i res ->
    repeati n2
    (fun j res ->
      lemma_matrix_index_repeati1 n1 n2 i j;
      let res_ij = Seq.sub r (2 * (n2 * i + j)) 2 in
      res.(i, j) <- frodo_sample (uint_from_bytes_le #U16 res_ij)
    ) res
  ) res

val frodo_sample_matrix_tr:
    n1: size_nat
  -> n2: size_nat{2 * n1 * n2 < max_size_t}
  -> seedLen: size_nat
  -> seed: lbytes seedLen
  -> ctr:uint16
  -> matrix n1 n2
let frodo_sample_matrix_tr n1 n2 seedLen seed ctr =
  let r = cshake_frodo seedLen seed ctr (2 * n1 * n2) in
  let res = Matrix.create n1 n2 in
  repeati n1
  (fun i res ->
    repeati n2
    (fun j res ->
      lemma_matrix_index_repeati2 n1 n2 i j;
      let res_ij = Seq.sub r (2 * (n1 * j + i)) 2 in
      res.(i, j) <- frodo_sample (uint_from_bytes_le res_ij)
    ) res
  ) res

val frodo_gen_matrix_cshake:
    n: size_nat{2 * n < max_size_t /\ 256 + n < maxint U16 /\ n * n < max_size_t}
  -> seedLen: size_nat
  -> seed: lbytes seedLen
  -> matrix n n
let frodo_gen_matrix_cshake n seedLen seed =
  let res = Matrix.create n n in
  repeati n
  (fun i res ->
    let res_i = cshake128_frodo seedLen seed (u16 (256 + i)) (2 * n) in
    repeati n
    (fun j res ->
      res.(i, j) <- uint_from_bytes_le (Seq.sub res_i (j * 2) 2)
    ) res
  ) res

let frodo_gen_matrix = frodo_gen_matrix_cshake

val matrix_to_lbytes:
    #n1: size_nat
  -> #n2: size_nat{2 * n1 * n2 < max_size_t}
  -> m: matrix n1 n2
  -> lbytes (2 * n1 * n2)
let matrix_to_lbytes #n1 #n2 m =
  let res = Seq.create (2 * n1 * n2) (u8 0) in
  repeati n1
  (fun i res ->
    repeati n2
    (fun j res ->
      lemma_matrix_index_repeati2 n1 n2 i j;
      update_sub res (2 * (j * n1 + i)) 2 (uint_to_bytes_le m.(i, j))
    ) res
  ) res

val matrix_from_lbytes:
    n1: size_nat
  -> n2: size_nat{2 * n1 * n2 < max_size_t}
  -> lbytes (2 * n1 * n2)
  -> matrix n1 n2
let matrix_from_lbytes n1 n2 b =
  let res = Matrix.create n1 n2 in
  repeati n1
  (fun i res ->
    repeati n2
    (fun j res ->
      lemma_matrix_index_repeati2 n1 n2 i j;
      res.(i, j) <- uint_from_bytes_le (Seq.sub b (2 * (j * n1 + i)) 2)
    ) res
  ) res

val crypto_kem_keypair:
    coins: lbytes (2 * crypto_bytes + bytes_seed_a)
  -> tuple2 (lbytes crypto_publickeybytes) (lbytes crypto_secretkeybytes)
let crypto_kem_keypair coins =
  let s = Seq.sub coins 0 crypto_bytes in
  let seed_e = Seq.sub coins crypto_bytes crypto_bytes in
  let z = Seq.sub coins (2 * crypto_bytes) bytes_seed_a in
  let seed_a = cshake_frodo bytes_seed_a z (u16 0) bytes_seed_a in

  let a_matrix = frodo_gen_matrix params_n bytes_seed_a seed_a in
  let s_matrix = frodo_sample_matrix_tr params_n params_nbar crypto_bytes seed_e (u16 1) in
  let e_matrix = frodo_sample_matrix params_n params_nbar crypto_bytes seed_e (u16 2) in
  let b_matrix = Matrix.add (Matrix.mul a_matrix s_matrix) e_matrix in
  let b = frodo_pack params_n params_nbar b_matrix params_logq in

  let pk = concat seed_a b in
  let sk = concat s (concat pk (matrix_to_lbytes s_matrix)) in
  (pk, sk)

val crypto_kem_enc:
    coins: lbytes bytes_mu
  -> pk: lbytes crypto_publickeybytes
  -> tuple2 (lbytes crypto_ciphertextbytes) (lbytes crypto_bytes)
let crypto_kem_enc coins pk =
  let seed_a = Seq.sub pk 0 bytes_seed_a in
  let b = Seq.sub pk bytes_seed_a (crypto_publickeybytes - bytes_seed_a) in

  let g = cshake_frodo (crypto_publickeybytes + bytes_mu) (concat pk coins) (u16 3) (3 * crypto_bytes) in
  let seed_e = Seq.sub g 0 crypto_bytes in
  let k = Seq.sub g crypto_bytes crypto_bytes in
  let d = Seq.sub g (2*crypto_bytes) crypto_bytes in

  let sp_matrix = frodo_sample_matrix params_nbar params_n crypto_bytes seed_e (u16 4) in
  let ep_matrix = frodo_sample_matrix params_nbar params_n crypto_bytes seed_e (u16 5) in
  let a_matrix = frodo_gen_matrix params_n bytes_seed_a seed_a in
  let bp_matrix = Matrix.add (Matrix.mul sp_matrix a_matrix) ep_matrix in
  let c1 = frodo_pack params_nbar params_n bp_matrix params_logq in

  let epp_matrix = frodo_sample_matrix params_nbar params_nbar crypto_bytes seed_e (u16 6) in
  let b_matrix = frodo_unpack params_n params_nbar params_logq b in
  let v_matrix = Matrix.add (Matrix.mul sp_matrix b_matrix) epp_matrix in
  let mu_encode = frodo_key_encode params_extracted_bits coins in
  let c_matrix = Matrix.add v_matrix mu_encode in
  let c2 = frodo_pack params_nbar params_nbar c_matrix params_logq in

  let ss_init = concat c1 (concat c2 (concat k d)) in
  let ss_init_len = (params_logq * params_nbar * params_n) / 8 + (params_logq * params_nbar * params_nbar) / 8 + 2 * crypto_bytes in
  let ss = cshake_frodo ss_init_len ss_init (u16 7) crypto_bytes in
  let ct = concat c1 (concat c2 d) in
  (ct, ss)

val crypto_kem_dec:
    ct:lbytes crypto_ciphertextbytes
  -> sk:lbytes crypto_secretkeybytes
  -> lbytes crypto_bytes
let crypto_kem_dec ct sk =
  let c1Len = (params_logq * params_nbar * params_n) / 8 in
  let c2Len = (params_logq * params_nbar * params_nbar) / 8 in
  let c1 = Seq.sub ct 0 c1Len in
  let c2 = Seq.sub ct c1Len c2Len in
  let d = Seq.sub ct (c1Len+c2Len) crypto_bytes in

  let s = Seq.sub sk 0 crypto_bytes in
  let pk = Seq.sub sk crypto_bytes crypto_publickeybytes in
  let s_matrix = matrix_from_lbytes params_n params_nbar
    (Seq.sub sk (crypto_bytes + crypto_publickeybytes) (2*params_n*params_nbar)) in
  let seed_a = Seq.sub pk 0 bytes_seed_a in
  let b = Seq.sub pk bytes_seed_a (crypto_publickeybytes - bytes_seed_a) in

  let bp_matrix = frodo_unpack params_nbar params_n params_logq c1 in
  let c_matrix = frodo_unpack params_nbar params_nbar params_logq c2 in
  let m_matrix = Matrix.sub c_matrix (Matrix.mul bp_matrix s_matrix) in
  let mu_decode = frodo_key_decode params_extracted_bits m_matrix in

  let g = cshake_frodo (crypto_publickeybytes + (params_nbar * params_nbar * params_extracted_bits) / 8) (concat pk mu_decode)  (u16 3) (3 * crypto_bytes) in
  let seed_ep = Seq.sub g 0 crypto_bytes in
  let kp = Seq.sub g crypto_bytes crypto_bytes in
  let dp = Seq.sub g (2*crypto_bytes) crypto_bytes in

  let sp_matrix = frodo_sample_matrix params_nbar params_n crypto_bytes seed_ep (u16 4) in
  let ep_matrix = frodo_sample_matrix params_nbar params_n crypto_bytes seed_ep (u16 5) in
  let a_matrix = frodo_gen_matrix params_n bytes_seed_a seed_a in
  let bpp_matrix = Matrix.add (Matrix.mul sp_matrix a_matrix) ep_matrix in

  let epp_matrix = frodo_sample_matrix params_nbar params_nbar crypto_bytes seed_ep (u16 6) in
  let b_matrix = frodo_unpack params_n params_nbar params_logq b in
  let v_matrix = Matrix.add (Matrix.mul sp_matrix b_matrix) epp_matrix in

  let mu_encode = frodo_key_encode params_extracted_bits mu_decode in
  let cp_matrix = Matrix.add v_matrix mu_encode in

  let ss_init = concat c1 c2 in
  let ss_init_len = (params_logq * params_nbar * params_n) / 8
                    + (params_logq * params_nbar * params_nbar) / 8 + 2 * crypto_bytes in
  let ss_init1:lbytes ss_init_len = concat ss_init (concat kp d) in
  let ss_init2:lbytes ss_init_len = concat ss_init (concat s d) in

  let bcond = lbytes_eq d dp
              && matrix_eq params_logq bp_matrix bpp_matrix
              && matrix_eq params_logq c_matrix cp_matrix in
  let ss_init = if bcond then ss_init1 else ss_init2 in
  let ss = cshake_frodo ss_init_len ss_init (u16 7) crypto_bytes in
  ss
