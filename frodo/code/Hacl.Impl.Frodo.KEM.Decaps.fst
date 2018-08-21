module Hacl.Impl.Frodo.KEM.Decaps

open FStar.HyperStack.All
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer
open LowStar.BufferOps

open Lib.IntTypes
open Lib.PQ.Buffer

open Hacl.Impl.Matrix
open Hacl.Impl.Frodo.Params
open Hacl.Impl.Frodo.KEM
open Hacl.Impl.Frodo.KEM.Encaps
open Hacl.Impl.Frodo.Encode
open Hacl.Impl.Frodo.Pack
open Hacl.Impl.Frodo.Sample
open Hacl.Frodo.Random
open Hacl.Frodo.Clear

module ST = FStar.HyperStack.ST
module Lemmas = Spec.Frodo.Lemmas
module S = Spec.Frodo.KEM.Decaps
module M = Spec.Matrix
module LSeq = Lib.Sequence

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val frodo_sub_mul_c_minus_bs:
    sk:lbytes crypto_secretkeybytes
  -> bp_matrix:matrix_t params_nbar params_n
  -> c_matrix:matrix_t params_nbar params_nbar
  -> mu_decode:lbytes (params_nbar *! params_nbar *! params_extracted_bits /. size 8)
  -> Stack unit
    (requires fun h ->
      live h sk /\ live h bp_matrix /\ live h c_matrix /\ live h mu_decode)
    (ensures fun h0 r h1 -> live h1 mu_decode /\ modifies (loc_buffer mu_decode) h0 h1)
[@"c_inline"]
let frodo_sub_mul_c_minus_bs sk bp_matrix c_matrix mu_decode =
  push_frame();
  assert_norm (v crypto_secretkeybytes =
    v crypto_bytes + v crypto_publickeybytes + 2 * v params_n * v params_nbar);
  let s_matrix = matrix_create params_n params_nbar in
  matrix_from_lbytes
    (sub sk (crypto_bytes +! crypto_publickeybytes) (size 2 *! params_n *! params_nbar))
    s_matrix;

  let m_matrix = matrix_create params_nbar params_nbar in
  matrix_mul_s bp_matrix s_matrix m_matrix;
  matrix_sub c_matrix m_matrix;
  frodo_key_decode params_extracted_bits m_matrix mu_decode;
  pop_frame()

val crypto_kem_dec_ss:
    ct:lbytes crypto_ciphertextbytes
  -> g:lbytes (size 3 *! crypto_bytes)
  -> kp_s:lbytes crypto_bytes
  -> ss:lbytes crypto_bytes
  -> Stack unit
    (requires fun h ->
      live h ct /\ live h g /\ live h kp_s /\ live h ss /\
      disjoint ss ct /\ disjoint ss g /\ disjoint ss kp_s)
    (ensures fun h0 r h1 -> live h1 ss /\ modifies (loc_buffer ss) h0 h1)
[@"c_inline"]
let crypto_kem_dec_ss ct g kp_s ss =
  push_frame();
  assert_norm (v crypto_ciphertextbytes =
    (v params_nbar * v params_n + v params_nbar * v params_nbar)
      * v params_logq / 8 + v crypto_bytes);
  let c1Len = params_logq *! params_nbar *! params_n /. size 8 in
  let c2Len = params_logq *! params_nbar *! params_nbar /. size 8 in
  let c1 = sub #uint8 #_ #(v c1Len) ct (size 0) c1Len in
  let c2 = sub #uint8 #_ #(v c2Len) ct c1Len c2Len in
  let d = sub #uint8 #_ #(v crypto_bytes) ct (c1Len +! c2Len) crypto_bytes in

  let ss_init_len = c1Len +! c2Len +! size 2 *! crypto_bytes in
  let ss_init:lbytes ss_init_len = create ss_init_len (u8 0) in
  update_sub ss_init (size 0) c1Len c1;
  update_sub ss_init c1Len c2Len c2;
  update_sub ss_init (c1Len +! c2Len) crypto_bytes kp_s;
  update_sub ss_init (ss_init_len -! crypto_bytes) crypto_bytes d;

  cshake_frodo ss_init_len ss_init (u16 7) crypto_bytes ss;
  pop_frame()

let pk_mu_decode_len =
  assert_norm (v crypto_publickeybytes + v params_nbar * v params_nbar * v params_extracted_bits / 8 < max_size_t);
  normalize_term (crypto_publickeybytes +! params_nbar *! params_nbar *! params_extracted_bits /. size 8)

val crypto_kem_dec_ss1:
    pk_mu_decode:lbytes pk_mu_decode_len
  -> bp_matrix:matrix_t params_nbar params_n
  -> c_matrix:matrix_t params_nbar params_nbar
  -> sk:lbytes crypto_secretkeybytes
  -> ct:lbytes crypto_ciphertextbytes
  -> ss:lbytes crypto_bytes
  -> Stack unit
    (requires fun h ->
      live h pk_mu_decode /\ live h bp_matrix /\
      live h c_matrix /\ live h sk /\ live h ct /\ live h ss /\
      disjoint ss ct /\ disjoint ss sk)
    (ensures fun h0 r h1 -> live h1 ss /\ modifies (loc_buffer ss) h0 h1)
[@"c_inline"]
let crypto_kem_dec_ss1 pk_mu_decode bp_matrix c_matrix sk ct ss =
  // TODO: this proof is fragile. It failed after adding [clear_matrix]
  admit();
  push_frame();
  assert_norm (v crypto_ciphertextbytes =
    (v params_nbar * v params_n + v params_nbar * v params_nbar) * v params_logq / 8 + v crypto_bytes);
  assert_norm (v crypto_secretkeybytes =
    v crypto_bytes + v crypto_publickeybytes + 2 * v params_n * v params_nbar);
  assert_norm (v crypto_publickeybytes =
    v bytes_seed_a + v params_logq * v params_n * v params_nbar / 8);
  assert_norm (v pk_mu_decode_len =
    v crypto_publickeybytes + v params_nbar * v params_nbar * v params_extracted_bits / 8);
  let s = sub #uint8 #_ #(v crypto_bytes) sk (size 0) crypto_bytes in
  let pk = sub #uint8 #_ #(v crypto_publickeybytes) sk crypto_bytes crypto_publickeybytes in
  let seed_a = sub #uint8 #_ #(v bytes_seed_a) pk (size 0) bytes_seed_a in
  let b = sub #uint8 #_ #(v ((params_logq *! params_n *! params_nbar) /. size 8)) pk bytes_seed_a (crypto_publickeybytes -! bytes_seed_a) in

  let mu_decode_len = params_nbar *! params_nbar *! params_extracted_bits /. size 8 in
  let g = create (size 3 *! crypto_bytes) (u8 0) in
  cshake_frodo (crypto_publickeybytes +! mu_decode_len) pk_mu_decode (u16 3) (size 3 *! crypto_bytes) g;
  let seed_ep = sub #uint8 #_ #(v crypto_bytes) g (size 0) crypto_bytes in
  let kp = sub #uint8 #_ #(v crypto_bytes) g crypto_bytes crypto_bytes in
  let dp = sub #uint8 #_ #(v crypto_bytes) g (size 2 *! crypto_bytes) crypto_bytes in

  let sp_matrix  = matrix_create params_nbar params_n in
  frodo_sample_matrix params_nbar params_n crypto_bytes seed_ep (u16 4) sp_matrix;

  let bpp_matrix = matrix_create params_nbar params_n in
  frodo_mul_add_sa_plus_e_main seed_a seed_ep sp_matrix bpp_matrix;

  let v_matrix   = matrix_create params_nbar params_nbar in
  let mu_decode  = sub pk_mu_decode crypto_publickeybytes (params_nbar *! params_nbar *! params_extracted_bits /. size 8) in
  frodo_mul_add_sb_plus_e_plus_mu b seed_ep mu_decode sp_matrix v_matrix;

  let c1Len = params_logq *! params_nbar *! params_n /. size 8 in
  let c2Len = params_logq *! params_nbar *! params_nbar /. size 8 in
  let d = sub #uint8 #_ #(v crypto_bytes) ct (c1Len +! c2Len) crypto_bytes in
  let b1 = lbytes_eq d dp in
  let b2 = matrix_eq params_logq bp_matrix bpp_matrix in
  let b3 = matrix_eq params_logq c_matrix v_matrix in
  let kp_s = if (b1 && b2 && b3) then kp else s in
  crypto_kem_dec_ss ct g kp_s ss;
  clear_matrix sp_matrix;
  clear_words_u8 (size 2 *! crypto_bytes) (sub #_ #_ #(2 * v crypto_bytes) g (size 0) (size 2 *! crypto_bytes));
  pop_frame()

inline_for_extraction noextract
val crypto_kem_dec:
    ss:lbytes crypto_bytes
  -> ct:lbytes crypto_ciphertextbytes
  -> sk:lbytes crypto_secretkeybytes
  -> Stack uint32
    (requires fun h ->
      live h ss /\ live h ct /\ live h sk /\
      disjoint ss ct /\ disjoint ss sk)
    (ensures  fun h0 r h1 -> live h1 ss /\ modifies (loc_buffer ss) h0 h1)
let crypto_kem_dec ss ct sk =
  // TODO: this proof doesn't verify anymore. Fix
  admit();
  push_frame();
  assert_norm (v crypto_ciphertextbytes =
    (v params_nbar * v params_n + v params_nbar * v params_nbar) * v params_logq / 8 + v crypto_bytes);
  assert_norm (v crypto_secretkeybytes =
    v crypto_bytes + v crypto_publickeybytes + 2 * v params_n * v params_nbar);
  assert_norm (v crypto_publickeybytes =
    v bytes_seed_a + v params_logq * v params_n * v params_nbar / 8);
  assert_norm (v pk_mu_decode_len =
    v crypto_publickeybytes + v params_nbar * v params_nbar * v params_extracted_bits / 8);

  let c1Len = params_logq *! params_nbar *! params_n /. size 8 in
  let c2Len = params_logq *! params_nbar *! params_nbar /. size 8 in
  let c1 = sub #uint8 #_ #(v c1Len) ct (size 0) c1Len in
  let c2 = sub #uint8 #_ #(v c2Len) ct c1Len c2Len in
  let d = sub #uint8 #_ #(v crypto_bytes) ct (c1Len +! c2Len) crypto_bytes in

  let bp_matrix = matrix_create params_nbar params_n in
  let c_matrix  = matrix_create params_nbar params_nbar in
  frodo_unpack params_nbar params_n params_logq c1 bp_matrix;
  frodo_unpack params_nbar params_nbar params_logq c2 c_matrix;

  let mu_decode_len = params_nbar *! params_nbar *! params_extracted_bits /. size 8 in
  let mu_decode = create (params_nbar *! params_nbar *! params_extracted_bits /. size 8) (u8 0) in
  frodo_sub_mul_c_minus_bs sk bp_matrix c_matrix mu_decode;

  let pk_mu_decode = create (crypto_publickeybytes +! mu_decode_len) (u8 0) in
  let pk = sub #uint8 #_ #(v crypto_publickeybytes) sk crypto_bytes crypto_publickeybytes in
  update_sub pk_mu_decode (size 0) crypto_publickeybytes pk;
  update_sub pk_mu_decode crypto_publickeybytes mu_decode_len mu_decode;

  crypto_kem_dec_ss1 pk_mu_decode bp_matrix c_matrix sk ct ss;
  pop_frame();
  u32 0
