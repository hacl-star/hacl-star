module Hacl.Impl.Frodo.Params

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Hacl.Impl.Matrix

module S = Spec.Frodo.Params

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let params_n (a:S.frodo_alg) : x:size_t{v x == S.params_n a} =
  match a with
  | S.Frodo64 -> 64ul
  | S.Frodo640 -> 640ul
  | S.Frodo976 -> 976ul
  | S.Frodo1344 -> 1344ul


inline_for_extraction noextract
let params_logq (a:S.frodo_alg) : x:size_t{v x == S.params_logq a} =
  match a with
  | S.Frodo64 | S.Frodo640 -> 15ul
  | S.Frodo976 | S.Frodo1344 -> 16ul


inline_for_extraction noextract
let params_extracted_bits (a:S.frodo_alg) : x:size_t{v x == S.params_extracted_bits a} =
  match a with
  | S.Frodo64 | S.Frodo640 -> 2ul
  | S.Frodo976 -> 3ul
  | S.Frodo1344 -> 4ul


inline_for_extraction noextract
let crypto_bytes (a:S.frodo_alg) : x:size_t{v x == S.crypto_bytes a} =
  match a with
  | S.Frodo64 | S.Frodo640 -> 16ul
  | S.Frodo976 -> 24ul
  | S.Frodo1344 -> 32ul


inline_for_extraction noextract
let params_nbar = 8ul

inline_for_extraction noextract
let bytes_seed_a = 16ul

inline_for_extraction noextract
let bytes_pkhash (a:S.frodo_alg) =
  crypto_bytes a

inline_for_extraction noextract
let bytes_mu (a:S.frodo_alg) =
  params_extracted_bits a *! params_nbar *! params_nbar /. 8ul

inline_for_extraction noextract
let publicmatrixbytes_len (a:S.frodo_alg) =
  params_logq a *! (params_n a *! params_nbar /. 8ul)

inline_for_extraction noextract
let secretmatrixbytes_len (a:S.frodo_alg) =
  2ul *! params_n a *! params_nbar

inline_for_extraction noextract
let ct1bytes_len (a:S.frodo_alg) =
  params_logq a *! (params_nbar *! params_n a /. 8ul)

inline_for_extraction noextract
let ct2bytes_len (a:S.frodo_alg) =
  params_logq a *! (params_nbar *! params_nbar /. 8ul)

inline_for_extraction noextract
let crypto_publickeybytes (a:S.frodo_alg) =
  bytes_seed_a +! publicmatrixbytes_len a

inline_for_extraction noextract
let crypto_secretkeybytes (a:S.frodo_alg) =
  crypto_bytes a +! crypto_publickeybytes a +! secretmatrixbytes_len a +! bytes_pkhash a

inline_for_extraction noextract
let crypto_ciphertextbytes (a:S.frodo_alg) =
  ct1bytes_len a +! ct2bytes_len a


inline_for_extraction noextract
let frodo_shake_st (a:S.frodo_alg) =
    inputByteLen:size_t
  -> input:lbuffer uint8 inputByteLen
  -> outputByteLen:size_t
  -> output:lbuffer uint8 outputByteLen
  -> Stack unit
    (requires fun h ->
      live h input /\ live h output /\ disjoint input output)
    (ensures  fun h0 _ h1 -> modifies (loc output) h0 h1 /\
      as_seq h1 output == S.frodo_shake a (v inputByteLen) (as_seq h0 input) (v outputByteLen))


inline_for_extraction noextract
let frodo_shake (a:S.frodo_alg) : frodo_shake_st a =
  match a with
  | S.Frodo64 | S.Frodo640 -> Hacl.SHA3.shake128_hacl
  | S.Frodo976 | S.Frodo1344 -> Hacl.SHA3.shake256_hacl


inline_for_extraction noextract
let is_supported (a:S.frodo_gen_a) =
  match a with
  | S.SHAKE128 -> true
  | S.AES128 -> false (* unfortunately, we don't have a verified impl of aes128 in Low* *)


val frodo_gen_matrix:
    a:S.frodo_gen_a{is_supported a}
  -> n:size_t{0 < v n /\ v n * v n <= max_size_t /\ v n <= maxint U16 /\ v n % 4 = 0}
  -> seed:lbuffer uint8 16ul
  -> a_matrix:matrix_t n n
  -> Stack unit
    (requires fun h ->
      live h seed /\ live h a_matrix /\ disjoint seed a_matrix)
    (ensures  fun h0 _ h1 -> modifies1 a_matrix h0 h1 /\
      as_matrix h1 a_matrix == S.frodo_gen_matrix a (v n) (as_seq h0 seed))

[@CInline]
let frodo_gen_matrix a n seed a_matrix =
  match a with
  | S.SHAKE128 -> Hacl.Impl.Frodo.Gen.frodo_gen_matrix_shake_4x n seed a_matrix
(*  | S.AES128 -> Hacl.Impl.Frodo.Gen.frodo_gen_matrix_aes n seed a_matrix *)


(** CDF tables *)

let cdf_table640 :x:glbuffer uint16 13ul{witnessed x (S.cdf_table S.Frodo640) /\ recallable x} =
  createL_global S.cdf_list_640

let cdf_table976 :x:glbuffer uint16 11ul{witnessed x (S.cdf_table S.Frodo976) /\ recallable x} =
  createL_global S.cdf_list_976

let cdf_table1344 :x:glbuffer uint16 7ul{witnessed x (S.cdf_table S.Frodo1344) /\ recallable x} =
  createL_global S.cdf_list_1344


inline_for_extraction noextract
let cdf_table_len (a:S.frodo_alg) : x:size_t{v x = S.cdf_table_len a} =
  allow_inversion S.frodo_alg;
  match a with
  | S.Frodo64 | S.Frodo640 -> 13ul
  | S.Frodo976 -> 11ul
  | S.Frodo1344 -> 7ul


inline_for_extraction noextract
let cdf_table (a:S.frodo_alg) :x:glbuffer uint16 (cdf_table_len a)
  {witnessed x (S.cdf_table a) /\ recallable x}
 =
  allow_inversion S.frodo_alg;
  match a with
  | S.Frodo64 | S.Frodo640 -> cdf_table640
  | S.Frodo976 -> cdf_table976
  | S.Frodo1344 -> cdf_table1344
