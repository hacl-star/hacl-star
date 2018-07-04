module Spec.Frodo

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.RawIntTypes
open FStar.Math.Lemmas

open Spec.PQ.Lib
open Spec.Keccak
open Spec.Frodo.Lemmas

val matrix_eq:
  #t:numeric_t -> #n1:size_nat -> #n2:size_nat ->
  m:size_nat{m > 0} ->
  a:matrix_t t n1 n2 -> b:matrix_t t n1 n2 -> Tot bool
let matrix_eq #t #n1 #n2 m a b =
  repeati n1
  (fun i res ->
    repeati n2
    (fun j res ->
      res && (uint_to_nat (mget a i j) % m = uint_to_nat (mget b i j) % m)
    ) res
  ) true

val lbytes_eq:
  #len:size_nat -> a:lbytes len -> b:lbytes len -> Tot bool
let lbytes_eq #len a b =
  repeati len
  (fun i res ->
    res && (uint_to_nat a.[i] = uint_to_nat b.[i])
  ) true

val cshake128_frodo:
  input_len:size_nat -> input:lbytes input_len ->
  cstm:uint16 -> output_len:size_nat -> Tot (lbytes output_len)
let cshake128_frodo input_len input cstm output_len =
  let s = create 25 (u64 0) in
  let s = s.[0] <- (u64 0x10010001a801) |. (shift_left (to_u64 cstm) (u32 48)) in
  let s = state_permute s in
  let s = absorb s 168 input_len input (u8 0x04) in
  squeeze s 168 output_len

val cshake256_frodo:
  input_len:size_nat -> input:lbytes input_len ->
  cstm:uint16 -> output_len:size_nat -> Tot (lbytes output_len)
let cshake256_frodo input_len input cstm output_len =
  let s = create 25 (u64 0) in
  let s = s.[0] <- (u64 0x100100018801) |. (shift_left (to_u64 cstm) (u32 48)) in
  let s = state_permute s in
  let s = absorb s 136 input_len input (u8 0x04) in
  squeeze s 136 output_len

//FrodoKEM-640
let params_n:size_nat = 64 //640
let params_logq:size_nat = 15
let params_extracted_bits:size_nat = 2
let crypto_bytes:size_nat = 16
let cshake_frodo = cshake128_frodo
let cdf_table_len:size_nat = 12
let cdf_table : lseq size_nat cdf_table_len =
  let cdf_table0: list size_nat = [4727; 13584; 20864; 26113; 29434; 31278; 32176; 32560; 32704; 32751; 32764; 32767] in
  assert_norm (List.Tot.length cdf_table0 = cdf_table_len);
  createL cdf_table0

let bytes_seed_a:size_nat = 16
let params_nbar:size_nat = 8
let params_q:size_nat =
  pow2_lt_compat 32 params_logq;
  pow2 params_logq
let bytes_mu:size_nat = (params_extracted_bits * params_nbar * params_nbar) / 8
let crypto_publickeybytes:size_nat  = bytes_seed_a + (params_logq * params_n * params_nbar) / 8
let crypto_secretkeybytes:size_nat  = crypto_bytes + crypto_publickeybytes + 2 * params_n * params_nbar
let crypto_ciphertextbytes:size_nat = ((params_nbar * params_n + params_nbar * params_nbar) * params_logq) / 8 + crypto_bytes

//unfold type elem_t:numeric_t = NATm params_q
unfold type elem_t:numeric_t = U16

val ec:
  b:size_nat{b <= params_logq} -> k:uint16{uint_v k < pow2 b} ->
  Tot (r:uint16{uint_v r < pow2 params_logq /\ uint_v r = (uint_v k) * pow2 (params_logq - b)})
  #reset-options "--z3rlimit 50 --max_fuel 0"
let ec b k =
  let res = k <<. u32 (params_logq - b) in
  assert (uint_v res = (uint_v k * pow2 (params_logq - b)) % modulus U16);
  assert (uint_v k * pow2 (params_logq - b) < pow2 b * pow2 (params_logq - b));
  pow2_plus b (params_logq - b);
  //assert (uint_v k * pow2 (params_logq - b) < pow2 params_logq);
  //assert (uint_v res < pow2 params_logq);
  pow2_le_compat 16 params_logq;
  //assert (pow2 params_logq <= modulus U16);
  small_modulo_lemma_2 (uint_v res) (modulus U16);
  res

val dc:
  b:size_nat{b < params_logq} -> c:uint16 ->
  Tot (r:uint16{uint_v r < pow2 b /\ uint_v r = ((uint_v c + pow2 (params_logq - b - 1)) / pow2 (params_logq - b)) % pow2 b})
  #reset-options "--z3rlimit 50 --max_fuel 0"
let dc b c =
  let res1 = (c +. (u16 1 <<. u32 (params_logq - b - 1))) >>. u32 (params_logq - b) in
  assert (uint_v res1 = (((uint_v c + pow2 (params_logq - b - 1) % modulus U16) % modulus U16) / pow2 (params_logq - b)) % modulus U16);
  lemma_mod_plus_distr_l (pow2 (params_logq - b - 1)) (uint_v c) (modulus U16);
  assert (uint_v res1 = (((uint_v c + pow2 (params_logq - b - 1)) % modulus U16) / pow2 (params_logq - b)) % modulus U16);
  pow2_modulo_division_lemma_1 (uint_v c + pow2 (params_logq - b - 1)) (params_logq - b) 16;
  assert (uint_v res1 = (((uint_v c + pow2 (params_logq - b - 1)) / pow2 (params_logq - b)) % pow2 (16 - params_logq + b)) % modulus U16);
  pow2_modulo_modulo_lemma_1 ((uint_v c + pow2 (params_logq - b - 1)) / pow2 (params_logq - b)) (16 - params_logq + b) 16;
  assert (uint_v res1 = ((uint_v c + pow2 (params_logq - b - 1)) / pow2 (params_logq - b)) % pow2 (16 - params_logq + b));
  let res = res1 &. ((u16 1 <<. u32 b) -. u16 1) in
  modulo_pow2_u16 res1 b;
  assert (uint_v res1 % pow2 b = uint_v (res1 &. ((u16 1 <<. u32 b) -. u16 1)));
  pow2_modulo_modulo_lemma_1 ((uint_v c + pow2 (params_logq - b - 1)) / pow2 (params_logq - b)) b (16 - params_logq + b);
  //assert (uint_v res = ((uint_v c + pow2 (params_logq - b - 1)) / pow2 (params_logq - b)) % pow2 b);
  res

val frodo_key_encode:
  b:size_nat{(params_nbar * params_nbar * b) / 8 < max_size_t /\ b <= 8} ->
  a:lbytes ((params_nbar * params_nbar * b) / 8) ->
  Tot (matrix_t elem_t params_nbar params_nbar)
  #reset-options "--z3rlimit 50 --max_fuel 0"
let frodo_key_encode b a =
  let res = matrix_create elem_t params_nbar params_nbar in
  repeati params_nbar
  (fun i res ->
    repeati (params_nbar / 8)
    (fun j res ->
      let v8 = create 8 (u8 0) in
      let v8 = update_sub v8 0 b (sub a ((i+j)*b) b) in
      let vij = uint_from_bytes_le v8 in
      repeati 8
      (fun k res ->
        let ak = (vij >>. u32 (b * k)) &. ((u64 1 <<. u32 b) -. u64 1) in
	modulo_pow2_u64 (vij >>. u32 (b * k)) b;
        let resij = ec b (to_u16 ak) in
        mset res i (8*j+k) (to_numeric elem_t resij)
      ) res
    ) res
  ) res

val frodo_key_decode:
  b:size_nat{(params_nbar * params_nbar * b) / 8 < max_size_t /\ b <= 8} ->
  a:matrix_t elem_t params_nbar params_nbar ->
  Tot (lbytes ((params_nbar * params_nbar * b) / 8))
  #reset-options "--z3rlimit 50 --max_fuel 0"
let frodo_key_decode b a =
  let resLen = (params_nbar * params_nbar * b) / 8 in
  let res = create resLen (u8 0) in
  repeati params_nbar
  (fun i res ->
    repeati (params_nbar / 8)
    (fun j res ->
      let templong = repeati 8
      (fun k templong ->
        let aij = dc b (to_numeric U16 (mget a i (8*j+k))) in
        templong |. (to_u64 aij <<. u32 (b*k))
      ) (u64 0) in
      update_sub res ((i+j)*b) b (sub (uint_to_bytes_le templong) 0 b)
    ) res
  ) res

val frodo_pack:
  n1:size_nat -> n2:size_nat{n1 * n2 < max_size_t /\ n2 % 8 = 0} ->
  a:matrix_t elem_t n1 n2 ->
  d:size_nat{(d * n1 * n2) / 8 < max_size_t /\ d <= 16} -> Tot (lbytes ((d * n1 * n2) / 8))
  #reset-options "--z3rlimit 50 --max_fuel 0"
let frodo_pack n1 n2 a d =
  let maskd = (u128 1 <<. u32 d) -. u128 1 in
  let resLen = (d * n1 * n2) / 8 in
  let res = create resLen (u8 0) in
  repeati n1
  (fun i res ->
    repeati (n2 / 8)
    (fun j res ->
      let templong = repeati 8
      (fun k templong ->
        let aij = to_numeric U16 (mget a i (8*j+k)) in
        templong |. ((to_u128 aij &. maskd) <<. u32 (7*d - d*k))
      ) (u128 0) in
      lemma_matrix_index_repeati n1 n2 d i j;
      update_sub res ((i*n2/8+j)*d) d (sub (uint_to_bytes_be templong) (16 - d) d)
    ) res
  ) res

val frodo_unpack:
  n1:size_nat -> n2:size_nat{n2 % 8 = 0} ->
  d:size_nat{(d * n1 * n2) / 8 < max_size_t /\ d <= 16} -> b:lbytes ((d * n1 * n2) / 8) ->
  Tot (matrix_t elem_t n1 n2)
let frodo_unpack n1 n2 d b =
  let maskd = (u128 1 <<. u32 d) -. u128 1 in
  let res = matrix_create elem_t n1 n2 in
  repeati n1
  (fun i res ->
    repeati (n2 / 8)
    (fun j res ->
      lemma_matrix_index_repeati n1 n2 d i j;
      let vij = sub b ((i*n2/8+j)*d) d in
      let v16 = create 16 (u8 0) in
      let v16 = uint_from_bytes_be (update_sub v16 (16-d) d vij) in
      repeati 8
      (fun k res ->
        let resij = to_u16 ((v16 >>. u32 (7*d - d*k)) &. maskd) in
        mset res i (8*j+k) (to_numeric elem_t resij)
      ) res
    ) res
  ) res

val frodo_sample: r:uint16 -> Tot (uint_t elem_t)
#reset-options "--z3rlimit 50 --max_fuel 1"
let frodo_sample r =
  let t = r >>. u32 1 in
  let e = 0 in
  let r0 = r &. u16 1 in

  let e = repeati (cdf_table_len - 1)
  (fun z e ->
    let e = if (uint_to_nat t > cdf_table.[z]) then e + 1 else e in e
  ) e in
  let e = (FStar.Math.Lib.powx (-1) (uint_to_nat r0)) * e in
  numeric (e % modulus elem_t)

val frodo_sample_matrix:
  n1:size_nat -> n2:size_nat{2 * n1 * n2 < max_size_t} ->
  seedLen:size_nat -> seed:lbytes seedLen ->
  ctr:uint16 -> Tot (matrix_t elem_t n1 n2)
let frodo_sample_matrix n1 n2 seedLen seed ctr =
  let r = cshake_frodo seedLen seed ctr (2 * n1 * n2) in
  let res = matrix_create elem_t n1 n2 in
  repeati n1
  (fun i res ->
    repeati n2
    (fun j res ->
      lemma_matrix_index_repeati1 n1 n2 i j;
      let res_ij = sub r (2 * (n2 * i + j)) 2 in
      mset res i j (frodo_sample (uint_from_bytes_le #U16 res_ij))
    ) res
  ) res

val frodo_sample_matrix_tr:
  n1:size_nat -> n2:size_nat{2 * n1 * n2 < max_size_t} ->
  seedLen:size_nat -> seed:lbytes seedLen ->
  ctr:uint16 -> Tot (matrix_t elem_t n1 n2)
let frodo_sample_matrix_tr n1 n2 seedLen seed ctr =
  let r = cshake_frodo seedLen seed ctr (2 * n1 * n2) in
  let res = matrix_create elem_t n1 n2 in
  repeati n1
  (fun i res ->
    repeati n2
    (fun j res ->
      lemma_matrix_index_repeati2 n1 n2 i j;
      let res_ij = sub r (2 * (n1 * j + i)) 2 in
      mset res i j (frodo_sample (uint_from_bytes_le #U16 res_ij))
    ) res
  ) res

val frodo_gen_matrix_cshake:
  n:size_nat{2 * n < max_size_t /\ 256 + n < maxint U16} ->
  seedLen:size_nat -> seed:lbytes seedLen ->
  Tot (matrix_t elem_t n n)
let frodo_gen_matrix_cshake n seedLen seed =
  let res = matrix_create elem_t n n in
  repeati n
  (fun i res ->
    let res_i = cshake128_frodo seedLen seed (u16 (256 + i)) (2 * n) in
    repeati n
    (fun j res ->
      let res_ij = uint_from_bytes_le #U16 (sub res_i (j * 2) 2) in
      mset res i j (to_numeric elem_t res_ij)
    ) res
  ) res

let frodo_gen_matrix = frodo_gen_matrix_cshake

val matrix_to_lbytes:
  #n1:size_nat -> #n2:size_nat{2 * n1 * n2 < max_size_t} ->
  m:matrix_t elem_t n1 n2 -> Tot (lbytes (2 * n1 * n2))
let matrix_to_lbytes #n1 #n2 m =
  let res = create (2*n1*n2) (u8 0) in
  repeati n1
  (fun i res ->
    repeati n2
    (fun j res ->
      lemma_matrix_index_repeati2 n1 n2 i j;
      update_sub res (2*(j*n1+i)) 2 (uint_to_bytes_le (to_numeric U16 (mget m i j)))
    ) res
  ) res

val matrix_from_lbytes:
  n1:size_nat -> n2:size_nat{2 * n1 * n2 < max_size_t} ->
  lbytes (2 * n1 * n2) -> Tot (matrix_t elem_t n1 n2)
let matrix_from_lbytes n1 n2 b =
  let res = matrix_create elem_t n1 n2 in
  repeati n1
  (fun i res ->
    repeati n2
    (fun j res ->
      lemma_matrix_index_repeati2 n1 n2 i j;
      mset res i j (to_numeric elem_t (uint_from_bytes_le #U16 (sub b (2*(j*n1+i)) 2)))
    ) res
  ) res

val crypto_kem_keypair:
  coins:lbytes (2 * crypto_bytes + bytes_seed_a) ->
  Tot (tuple2 (lbytes crypto_publickeybytes) (lbytes crypto_secretkeybytes))
let crypto_kem_keypair coins =
  let s = sub coins 0 crypto_bytes in
  let seed_e = sub coins crypto_bytes crypto_bytes in
  let z = sub coins (2 * crypto_bytes) bytes_seed_a in
  let seed_a = cshake_frodo bytes_seed_a z (u16 0) bytes_seed_a in

  let a_matrix = frodo_gen_matrix params_n bytes_seed_a seed_a in
  let s_matrix = frodo_sample_matrix_tr params_n params_nbar crypto_bytes seed_e (u16 1) in
  let e_matrix = frodo_sample_matrix params_n params_nbar crypto_bytes seed_e (u16 2) in
  let b_matrix = matrix_add (matrix_mul a_matrix s_matrix) e_matrix in
  let b = frodo_pack params_n params_nbar b_matrix params_logq in

  let pk = concat seed_a b in
  let sk = concat s (concat pk (matrix_to_lbytes s_matrix)) in
  (pk, sk)

val crypto_kem_enc:
  coins:lbytes bytes_mu -> pk:lbytes crypto_publickeybytes ->
  Tot (tuple2 (lbytes crypto_ciphertextbytes) (lbytes crypto_bytes))
let crypto_kem_enc coins pk =
  let seed_a = sub pk 0 bytes_seed_a in
  let b = sub pk bytes_seed_a (crypto_publickeybytes - bytes_seed_a) in

  let g = cshake_frodo (crypto_publickeybytes + bytes_mu) (concat pk coins) (u16 3) (3 * crypto_bytes) in
  let seed_e = sub g 0 crypto_bytes in
  let k = sub g crypto_bytes crypto_bytes in
  let d = sub g (2*crypto_bytes) crypto_bytes in

  let sp_matrix = frodo_sample_matrix params_nbar params_n crypto_bytes seed_e (u16 4) in
  let ep_matrix = frodo_sample_matrix params_nbar params_n crypto_bytes seed_e (u16 5) in
  let a_matrix = frodo_gen_matrix params_n bytes_seed_a seed_a in
  let bp_matrix = matrix_add (matrix_mul sp_matrix a_matrix) ep_matrix in
  let c1 = frodo_pack params_nbar params_n bp_matrix params_logq in

  let epp_matrix = frodo_sample_matrix params_nbar params_nbar crypto_bytes seed_e (u16 6) in
  let b_matrix = frodo_unpack params_n params_nbar params_logq b in
  let v_matrix = matrix_add (matrix_mul sp_matrix b_matrix) epp_matrix in
  let mu_encode = frodo_key_encode params_extracted_bits coins in
  let c_matrix = matrix_add v_matrix mu_encode in
  let c2 = frodo_pack params_nbar params_nbar c_matrix params_logq in

  let ss_init = concat c1 (concat c2 (concat k d)) in
  let ss_init_len = (params_logq * params_nbar * params_n) / 8 + (params_logq * params_nbar * params_nbar) / 8 + 2 * crypto_bytes in
  let ss = cshake_frodo ss_init_len ss_init (u16 7) crypto_bytes in
  let ct = concat c1 (concat c2 d) in
  (ct, ss)

val crypto_kem_dec:
  ct:lbytes crypto_ciphertextbytes -> sk:lbytes crypto_secretkeybytes ->
  Tot (lbytes crypto_bytes)
let crypto_kem_dec ct sk =
  let c1Len = (params_logq * params_nbar * params_n) / 8 in
  let c2Len = (params_logq * params_nbar * params_nbar) / 8 in
  let c1 = sub ct 0 c1Len in
  let c2 = sub ct c1Len c2Len in
  let d = sub ct (c1Len+c2Len) crypto_bytes in

  let s = sub sk 0 crypto_bytes in
  let pk = sub sk crypto_bytes crypto_publickeybytes in
  let s_matrix = matrix_from_lbytes params_n params_nbar (sub sk (crypto_bytes + crypto_publickeybytes) (2*params_n*params_nbar)) in
  let seed_a = sub pk 0 bytes_seed_a in
  let b = sub pk bytes_seed_a (crypto_publickeybytes - bytes_seed_a) in

  let bp_matrix = frodo_unpack params_nbar params_n params_logq c1 in
  let c_matrix = frodo_unpack params_nbar params_nbar params_logq c2 in
  let m_matrix = matrix_sub c_matrix (matrix_mul bp_matrix s_matrix) in
  let mu_decode = frodo_key_decode params_extracted_bits m_matrix in

  let g = cshake_frodo (crypto_publickeybytes + (params_nbar * params_nbar * params_extracted_bits) / 8) (concat pk mu_decode)  (u16 3) (3 * crypto_bytes) in
  let seed_ep = sub g 0 crypto_bytes in
  let kp = sub g crypto_bytes crypto_bytes in
  let dp = sub g (2*crypto_bytes) crypto_bytes in

  let sp_matrix = frodo_sample_matrix params_nbar params_n crypto_bytes seed_ep (u16 4) in
  let ep_matrix = frodo_sample_matrix params_nbar params_n crypto_bytes seed_ep (u16 5) in
  let a_matrix = frodo_gen_matrix params_n bytes_seed_a seed_a in
  let bpp_matrix = matrix_add (matrix_mul sp_matrix a_matrix) ep_matrix in

  let epp_matrix = frodo_sample_matrix params_nbar params_nbar crypto_bytes seed_ep (u16 6) in
  let b_matrix = frodo_unpack params_n params_nbar params_logq b in
  let v_matrix = matrix_add (matrix_mul sp_matrix b_matrix) epp_matrix in

  let mu_encode = frodo_key_encode params_extracted_bits mu_decode in
  let cp_matrix = matrix_add v_matrix mu_encode in

  let ss_init = concat c1 c2 in
  let ss_init_len = (params_logq * params_nbar * params_n) / 8 + (params_logq * params_nbar * params_nbar) / 8 + 2 * crypto_bytes in
  let ss_init1:lbytes ss_init_len = concat ss_init (concat kp d) in
  let ss_init2:lbytes ss_init_len = concat ss_init (concat s d) in

  let bcond = (lbytes_eq d dp) && (matrix_eq params_q bp_matrix bpp_matrix) && (matrix_eq params_q c_matrix cp_matrix) in
  let ss_init = if (bcond) then ss_init1 else ss_init2 in
  let ss = cshake_frodo ss_init_len ss_init (u16 7) crypto_bytes in
  ss
