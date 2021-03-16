module Spec.Frodo.Params

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open Spec.Matrix

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

type frodo_alg =
  | Frodo64 (* this variant is used only for testing purposes *)
  | Frodo640
  | Frodo976
  | Frodo1344

type frodo_gen_a =
  | SHAKE128
  | AES128

let _: squash (inversion frodo_alg) = allow_inversion frodo_alg
let _: squash (inversion frodo_gen_a) = allow_inversion frodo_gen_a


inline_for_extraction
let params_n (a:frodo_alg) : x:size_pos{x % 8 = 0 /\ x <= 1344} =
  match a with
  | Frodo64 -> 64
  | Frodo640 -> 640
  | Frodo976 -> 976
  | Frodo1344 -> 1344


inline_for_extraction
let params_logq (a:frodo_alg) : x:size_pos{x <= 16} =
  match a with
  | Frodo64 | Frodo640 -> 15
  | Frodo976 | Frodo1344 -> 16


inline_for_extraction
let params_extracted_bits (a:frodo_alg) : x:size_pos{x < params_logq a /\ x <= 8} =
  match a with
  | Frodo64 | Frodo640 -> 2
  | Frodo976 -> 3
  | Frodo1344 -> 4


inline_for_extraction
let crypto_bytes (a:frodo_alg) : x:size_pos{x <= 32} =
  match a with
  | Frodo64 | Frodo640 -> 16
  | Frodo976 -> 24
  | Frodo1344 -> 32


let params_nbar = 8
let bytes_seed_a = 16

let bytes_pkhash (a:frodo_alg) : size_pos =
  crypto_bytes a

let bytes_mu (a:frodo_alg) : size_pos =
  params_extracted_bits a * params_nbar * params_nbar / 8

let publicmatrixbytes_len (a:frodo_alg) : size_pos =
  params_logq a * (params_n a * params_nbar / 8)

let secretmatrixbytes_len (a:frodo_alg) : size_pos =
  2 * params_n a * params_nbar

let ct1bytes_len (a:frodo_alg) : size_pos =
  params_logq a * (params_nbar * params_n a / 8)

let ct2bytes_len (a:frodo_alg) : size_pos =
  params_logq a * (params_nbar * params_nbar / 8)

let crypto_publickeybytes (a:frodo_alg) : size_pos =
  bytes_seed_a + publicmatrixbytes_len a

let crypto_secretkeybytes (a:frodo_alg) : size_pos =
  crypto_bytes a + crypto_publickeybytes a + secretmatrixbytes_len a + bytes_pkhash a

let crypto_ciphertextbytes (a:frodo_alg) : size_pos =
  ct1bytes_len a + ct2bytes_len a

val expand_crypto_publickeybytes: a:frodo_alg ->
  Lemma (crypto_publickeybytes a == bytes_seed_a + publicmatrixbytes_len a)
let expand_crypto_publickeybytes a = ()

val expand_crypto_secretkeybytes: a:frodo_alg ->
  Lemma (crypto_secretkeybytes a ==
    crypto_bytes a + crypto_publickeybytes a + secretmatrixbytes_len a + bytes_pkhash a)
let expand_crypto_secretkeybytes a = ()

val expand_crypto_ciphertextbytes: a:frodo_alg ->
  Lemma (crypto_ciphertextbytes a == ct1bytes_len a + ct2bytes_len a)
let expand_crypto_ciphertextbytes a = ()

val params_n_sqr: a:frodo_alg ->
  Lemma (params_n a * params_n a <= max_size_t /\ params_n a <= maxint U16)
let params_n_sqr a =
  assert (params_n a <= maxint U16);
  Math.Lemmas.lemma_mult_lt_sqr (params_n a) (params_n a) (maxint U16);
  Math.Lemmas.pow2_plus 16 16


inline_for_extraction noextract
let frodo_shake_st =
    inputByteLen:nat
  -> input:bytes{length input == inputByteLen}
  -> outputByteLen:size_nat
  -> lbytes outputByteLen


inline_for_extraction
let frodo_shake (a:frodo_alg) : frodo_shake_st =
  match a with
  | Frodo64 | Frodo640 -> Spec.SHA3.shake128
  | Frodo976 | Frodo1344 -> Spec.SHA3.shake256


inline_for_extraction noextract
let frodo_gen_matrix_st =
    n:size_nat{n * n <= max_size_t /\ n <= maxint U16 /\ n % 4 = 0}
  -> seed:lbytes 16
  -> matrix n n


inline_for_extraction
let frodo_gen_matrix (a:frodo_gen_a) : frodo_gen_matrix_st =
  match a with
  | SHAKE128 -> Spec.Frodo.Gen.frodo_gen_matrix_shake
  | AES128 -> Spec.Frodo.Gen.frodo_gen_matrix_aes


(** CDF tables *)
unfold let cdf_list_640: list uint16 =
  [ u16 4643; u16 13363; u16 20579; u16 25843; u16 29227; u16 31145; u16 32103; u16 32525;
    u16 32689; u16 32745; u16 32762; u16 32766; u16 32767 ]

unfold let cdf_list_976: list uint16 =
  [ u16 5638; u16 15915; u16 23689; u16 28571; u16 31116; u16 32217;  u16 32613; u16 32731;
    u16 32760; u16 32766; u16 32767 ]

unfold let cdf_list_1344: list uint16 =
  [ u16 9142; u16 23462; u16 30338; u16 32361; u16 32725; u16 32765; u16 32767 ]


inline_for_extraction
let cdf_table_len (a:frodo_alg) : size_pos =
  match a with
  | Frodo64 | Frodo640 -> 13
  | Frodo976 -> 11
  | Frodo1344 -> 7


inline_for_extraction
let cdf_list (a:frodo_alg) : x:list uint16{List.Tot.length x == cdf_table_len a} =
  match a with
  | Frodo64 | Frodo640 ->
    assert_norm (List.Tot.length cdf_list_640 = 13);
    cdf_list_640
  | Frodo976 ->
    assert_norm (List.Tot.length cdf_list_976 = 11);
    cdf_list_976
  | Frodo1344 ->
    assert_norm (List.Tot.length cdf_list_1344 = 7);
    cdf_list_1344


inline_for_extraction
let cdf_table (a:frodo_alg) : lseq uint16 (cdf_table_len a) =
  createL (cdf_list a)


val lemma_cdf_list_640: i:size_nat{i < List.Tot.length cdf_list_640} ->
  Lemma (uint_v (List.Tot.index cdf_list_640 i) < pow2 15)
let lemma_cdf_list_640 i =
  assert_norm (List.Tot.length cdf_list_640 = 13);
  assert_norm (uint_v (List.Tot.index cdf_list_640 0) < pow2 15);
  assert_norm (uint_v (List.Tot.index cdf_list_640 1) < pow2 15);
  assert_norm (uint_v (List.Tot.index cdf_list_640 2) < pow2 15);
  assert_norm (uint_v (List.Tot.index cdf_list_640 3) < pow2 15);
  assert_norm (uint_v (List.Tot.index cdf_list_640 4) < pow2 15);
  assert_norm (uint_v (List.Tot.index cdf_list_640 5) < pow2 15);
  assert_norm (uint_v (List.Tot.index cdf_list_640 6) < pow2 15);
  assert_norm (uint_v (List.Tot.index cdf_list_640 7) < pow2 15);
  assert_norm (uint_v (List.Tot.index cdf_list_640 8) < pow2 15);
  assert_norm (uint_v (List.Tot.index cdf_list_640 9) < pow2 15);
  assert_norm (uint_v (List.Tot.index cdf_list_640 10) < pow2 15);
  assert_norm (uint_v (List.Tot.index cdf_list_640 11) < pow2 15);
  assert_norm (uint_v (List.Tot.index cdf_list_640 12) < pow2 15)


val lemma_cdf_list_976: i:size_nat{i < List.Tot.length cdf_list_976} ->
  Lemma (uint_v (List.Tot.index cdf_list_976 i) < pow2 15)
let lemma_cdf_list_976 i =
  assert_norm (List.Tot.length cdf_list_976 = 11);
  assert_norm (uint_v (List.Tot.index cdf_list_976 0) < pow2 15);
  assert_norm (uint_v (List.Tot.index cdf_list_976 1) < pow2 15);
  assert_norm (uint_v (List.Tot.index cdf_list_976 2) < pow2 15);
  assert_norm (uint_v (List.Tot.index cdf_list_976 3) < pow2 15);
  assert_norm (uint_v (List.Tot.index cdf_list_976 4) < pow2 15);
  assert_norm (uint_v (List.Tot.index cdf_list_976 5) < pow2 15);
  assert_norm (uint_v (List.Tot.index cdf_list_976 6) < pow2 15);
  assert_norm (uint_v (List.Tot.index cdf_list_976 7) < pow2 15);
  assert_norm (uint_v (List.Tot.index cdf_list_976 8) < pow2 15);
  assert_norm (uint_v (List.Tot.index cdf_list_976 9) < pow2 15);
  assert_norm (uint_v (List.Tot.index cdf_list_976 10) < pow2 15)


val lemma_cdf_list_1344: i:size_nat{i < List.Tot.length cdf_list_1344} ->
  Lemma (uint_v (List.Tot.index cdf_list_1344 i) < pow2 15)
let lemma_cdf_list_1344 i =
  assert_norm (List.Tot.length cdf_list_1344 = 7);
  assert_norm (uint_v (List.Tot.index cdf_list_1344 0) < pow2 15);
  assert_norm (uint_v (List.Tot.index cdf_list_1344 1) < pow2 15);
  assert_norm (uint_v (List.Tot.index cdf_list_1344 2) < pow2 15);
  assert_norm (uint_v (List.Tot.index cdf_list_1344 3) < pow2 15);
  assert_norm (uint_v (List.Tot.index cdf_list_1344 4) < pow2 15);
  assert_norm (uint_v (List.Tot.index cdf_list_1344 5) < pow2 15);
  assert_norm (uint_v (List.Tot.index cdf_list_1344 6) < pow2 15)


val lemma_cdf_list: a:frodo_alg -> i:size_nat{i < cdf_table_len a} ->
  Lemma (uint_v (List.Tot.index (cdf_list a) i) < pow2 15)

let lemma_cdf_list a i =
  match a with
  | Frodo64 | Frodo640 ->
    assert_norm (List.Tot.length cdf_list_640 = 13);
    lemma_cdf_list_640 i
  | Frodo976 ->
    assert_norm (List.Tot.length cdf_list_976 = 11);
    lemma_cdf_list_976 i
  | Frodo1344 ->
    assert_norm (List.Tot.length cdf_list_1344 = 7);
    lemma_cdf_list_1344 i
