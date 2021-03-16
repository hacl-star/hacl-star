module Hacl.Impl.Frodo.KEM.Decaps

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Matrix
open Hacl.Impl.Frodo.Params
open Hacl.Impl.Frodo.KEM
open Hacl.Impl.Frodo.KEM.Encaps
open Hacl.Impl.Frodo.Encode
open Hacl.Impl.Frodo.Pack
open Hacl.Impl.Frodo.Sample
open Hacl.Frodo.Random

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence

module FP = Spec.Frodo.Params
module KG = Hacl.Impl.Frodo.KEM.KeyGen
module S = Spec.Frodo.KEM.Decaps
module M = Spec.Matrix

#set-options "--z3rlimit 100 --fuel 0 --ifuel 0"

inline_for_extraction noextract
val get_bp_c_matrices:
     a:FP.frodo_alg
  -> ct:lbytes (crypto_ciphertextbytes a)
  -> bp_matrix:matrix_t params_nbar (params_n a)
  -> c_matrix:matrix_t params_nbar params_nbar
  -> Stack unit
    (requires fun h ->
      live h ct /\ live h bp_matrix /\ live h c_matrix /\
      disjoint bp_matrix ct /\ disjoint c_matrix ct /\ disjoint bp_matrix c_matrix)
    (ensures  fun h0 _ h1 -> modifies (loc bp_matrix |+| loc c_matrix) h0 h1 /\
      (as_matrix h1 bp_matrix, as_matrix h1 c_matrix) == S.get_bp_c_matrices a (as_seq h0 ct))

let get_bp_c_matrices a ct bp_matrix c_matrix =
  let c1 = sub ct 0ul (ct1bytes_len a) in
  let c2 = sub ct (ct1bytes_len a) (ct2bytes_len a) in
  frodo_unpack params_nbar (params_n a) (params_logq a) c1 bp_matrix;
  frodo_unpack params_nbar params_nbar (params_logq a) c2 c_matrix


inline_for_extraction noextract
val frodo_mu_decode:
    a:FP.frodo_alg
  -> s_bytes:lbytes (secretmatrixbytes_len a)
  -> bp_matrix:matrix_t params_nbar (params_n a)
  -> c_matrix:matrix_t params_nbar params_nbar
  -> mu_decode:lbytes (bytes_mu a)
  -> Stack unit
    (requires fun h ->
      live h s_bytes /\ live h bp_matrix /\
      live h c_matrix /\ live h mu_decode /\
      disjoint mu_decode s_bytes /\
      as_seq h (mu_decode) == Seq.create (v (bytes_mu a)) (u8 0))
    (ensures fun h0 _ h1 -> modifies (loc mu_decode) h0 h1 /\
      as_seq h1 mu_decode ==
      S.frodo_mu_decode a (as_seq h0 s_bytes) (as_matrix h0 bp_matrix) (as_matrix h0 c_matrix))

let frodo_mu_decode a s_bytes bp_matrix c_matrix mu_decode =
  push_frame();
  let s_matrix = matrix_create (params_n a) params_nbar in
  let m_matrix = matrix_create params_nbar params_nbar in
  matrix_from_lbytes s_bytes s_matrix;
  matrix_mul_s bp_matrix s_matrix m_matrix;
  matrix_sub c_matrix m_matrix;
  frodo_key_decode (params_logq a) (params_extracted_bits a) params_nbar m_matrix mu_decode;
  clear_matrix s_matrix;
  clear_matrix m_matrix;
  pop_frame()


inline_for_extraction noextract
val get_bpp_cp_matrices_:
    a:FP.frodo_alg
  -> gen_a:FP.frodo_gen_a{is_supported gen_a}
  -> mu_decode:lbytes (bytes_mu a)
  -> sk:lbytes (crypto_secretkeybytes a)
  -> bpp_matrix:matrix_t params_nbar (params_n a)
  -> cp_matrix:matrix_t params_nbar params_nbar
  -> sp_matrix:matrix_t params_nbar (params_n a)
  -> ep_matrix:matrix_t params_nbar (params_n a)
  -> epp_matrix:matrix_t params_nbar params_nbar
  -> Stack unit
    (requires fun h ->
      live h mu_decode /\ live h sk /\
      live h bpp_matrix /\ live h cp_matrix /\
      live h sp_matrix /\ live h ep_matrix /\ live h epp_matrix /\
      loc_pairwise_disjoint [loc mu_decode; loc sk; loc bpp_matrix;
        loc cp_matrix; loc sp_matrix; loc ep_matrix; loc epp_matrix])
    (ensures fun h0 _ h1 -> modifies (loc bpp_matrix |+| loc cp_matrix) h0 h1 /\
      (as_matrix h1 bpp_matrix, as_matrix h1 cp_matrix) ==
      S.get_bpp_cp_matrices_ a gen_a (as_seq h0 mu_decode) (as_seq h0 sk)
        (as_matrix h0 sp_matrix) (as_matrix h0 ep_matrix) (as_matrix h0 epp_matrix))

let get_bpp_cp_matrices_ a gen_a mu_decode sk bpp_matrix cp_matrix sp_matrix ep_matrix epp_matrix =
  FP.expand_crypto_secretkeybytes a;
  FP.expand_crypto_publickeybytes a;
  let pk = sub sk (crypto_bytes a) (crypto_publickeybytes a) in
  let seed_a = sub pk 0ul bytes_seed_a in
  let b = sub pk bytes_seed_a (crypto_publickeybytes a -! bytes_seed_a) in

  frodo_mul_add_sa_plus_e a gen_a seed_a sp_matrix ep_matrix bpp_matrix;
  frodo_mul_add_sb_plus_e_plus_mu a mu_decode b sp_matrix epp_matrix cp_matrix;
  mod_pow2 (params_logq a) bpp_matrix;
  mod_pow2 (params_logq a) cp_matrix


#push-options "--z3rlimit 150"
inline_for_extraction noextract
val get_bpp_cp_matrices:
    a:FP.frodo_alg
  -> gen_a:FP.frodo_gen_a{is_supported gen_a}
  -> mu_decode:lbytes (bytes_mu a)
  -> seed_se:lbytes (crypto_bytes a)
  -> sk:lbytes (crypto_secretkeybytes a)
  -> bpp_matrix:matrix_t params_nbar (params_n a)
  -> cp_matrix:matrix_t params_nbar params_nbar
  -> Stack unit
    (requires fun h ->
      live h seed_se /\ live h mu_decode /\ live h sk /\
      live h bpp_matrix /\ live h cp_matrix /\
      loc_pairwise_disjoint [loc mu_decode; loc seed_se; loc sk; loc bpp_matrix; loc cp_matrix])
    (ensures fun h0 _ h1 -> modifies (loc bpp_matrix |+| loc cp_matrix) h0 h1 /\
      (as_matrix h1 bpp_matrix, as_matrix h1 cp_matrix) ==
      S.get_bpp_cp_matrices a gen_a (as_seq h0 mu_decode) (as_seq h0 seed_se) (as_seq h0 sk))

let get_bpp_cp_matrices a gen_a mu_decode seed_se sk bpp_matrix cp_matrix =
  push_frame ();
  let sp_matrix  = matrix_create params_nbar (params_n a) in
  let ep_matrix  = matrix_create params_nbar (params_n a) in
  let epp_matrix = matrix_create params_nbar params_nbar in
  get_sp_ep_epp_matrices a seed_se sp_matrix ep_matrix epp_matrix;
  get_bpp_cp_matrices_ a gen_a mu_decode sk bpp_matrix cp_matrix sp_matrix ep_matrix epp_matrix;
  clear_matrix3 a sp_matrix ep_matrix epp_matrix;
  pop_frame ()
#pop-options


inline_for_extraction noextract
val crypto_kem_dec_kp_s_cond:
    a:FP.frodo_alg
  -> bp_matrix:matrix_t params_nbar (params_n a)
  -> bpp_matrix:matrix_t params_nbar (params_n a)
  -> c_matrix:matrix_t params_nbar params_nbar
  -> cp_matrix:matrix_t params_nbar params_nbar
  -> Stack uint16
    (requires fun h ->
      live h bp_matrix /\ live h bpp_matrix /\
      live h c_matrix /\ live h cp_matrix)
    (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
      r == S.crypto_kem_dec_kp_s_cond a (as_matrix h0 bp_matrix) (as_matrix h0 bpp_matrix)
        (as_matrix h0 c_matrix) (as_matrix h0 cp_matrix))

let crypto_kem_dec_kp_s_cond a bp_matrix bpp_matrix c_matrix cp_matrix =
  let b1 = matrix_eq bp_matrix bpp_matrix in
  let b2 = matrix_eq c_matrix cp_matrix in
  b1 &. b2


inline_for_extraction noextract
val crypto_kem_dec_kp_s:
    a:FP.frodo_alg
  -> gen_a:FP.frodo_gen_a{is_supported gen_a}
  -> mu_decode:lbytes (bytes_mu a)
  -> seed_se:lbytes (crypto_bytes a)
  -> sk:lbytes (crypto_secretkeybytes a)
  -> bp_matrix:matrix_t params_nbar (params_n a)
  -> c_matrix:matrix_t params_nbar params_nbar
  -> Stack uint16
    (requires fun h ->
      live h mu_decode /\ live h bp_matrix /\ live h seed_se /\
      live h c_matrix /\ live h sk /\
      loc_pairwise_disjoint [loc mu_decode; loc seed_se; loc sk])
    (ensures fun h0 r h1 -> modifies0 h0 h1 /\
      r == S.crypto_kem_dec_kp_s a gen_a (as_seq h0 mu_decode) (as_seq h0 seed_se)
        (as_seq h0 sk) (as_matrix h0 bp_matrix) (as_matrix h0 c_matrix))

let crypto_kem_dec_kp_s a gen_a mu_decode seed_se sk bp_matrix c_matrix =
  push_frame ();
  let bpp_matrix = matrix_create params_nbar (params_n a) in
  let cp_matrix  = matrix_create params_nbar params_nbar in
  get_bpp_cp_matrices a gen_a mu_decode seed_se sk bpp_matrix cp_matrix;
  let mask = crypto_kem_dec_kp_s_cond a bp_matrix bpp_matrix c_matrix cp_matrix in
  pop_frame ();
  mask


inline_for_extraction noextract
val crypto_kem_dec_ss0:
    a:FP.frodo_alg
  -> ct:lbytes (crypto_ciphertextbytes a)
  -> mask:uint16{v mask == 0 \/ v mask == v (ones U16 SEC)}
  -> kp:lbytes (crypto_bytes a)
  -> s:lbytes (crypto_bytes a)
  -> ss:lbytes (crypto_bytes a)
  -> Stack unit
    (requires fun h ->
      live h ct /\ live h kp /\ live h s /\ live h ss /\
      disjoint ss ct /\ disjoint ss kp /\ disjoint ss s /\
      disjoint kp s)
    (ensures fun h0 _ h1 -> modifies (loc ss) h0 h1 /\
      as_seq h1 ss == S.crypto_kem_dec_ss0 a (as_seq h0 ct) mask (as_seq h0 kp) (as_seq h0 s))

let crypto_kem_dec_ss0 a ct mask kp s ss =
  push_frame ();
  let kp_s = create (crypto_bytes a) (u8 0) in
  Lib.ByteBuffer.buf_mask_select kp s (to_u8 mask) kp_s;

  let ss_init_len = crypto_ciphertextbytes a +! crypto_bytes a in
  let ss_init = create ss_init_len (u8 0) in
  concat2 (crypto_ciphertextbytes a) ct (crypto_bytes a) kp_s ss_init;
  frodo_shake a ss_init_len ss_init (crypto_bytes a) ss;
  clear_words_u8 ss_init;
  clear_words_u8 kp_s;
  pop_frame ()


inline_for_extraction noextract
val crypto_kem_dec_seed_se_k:
    a:FP.frodo_alg
  -> mu_decode:lbytes (bytes_mu a)
  -> sk:lbytes (crypto_secretkeybytes a)
  -> seed_se_k:lbytes (2ul *! crypto_bytes a)
  -> Stack unit
    (requires fun h ->
      live h mu_decode /\ live h sk /\ live h seed_se_k /\
      disjoint mu_decode seed_se_k /\ disjoint sk seed_se_k)
    (ensures fun h0 _ h1 -> modifies (loc seed_se_k) h0 h1 /\
      as_seq h1 seed_se_k == S.crypto_kem_dec_seed_se_k a (as_seq h0 mu_decode) (as_seq h0 sk))

let crypto_kem_dec_seed_se_k a mu_decode sk seed_se_k =
  push_frame ();
  let pkh_mu_decode_len = bytes_pkhash a +! bytes_mu a in
  let pkh_mu_decode = create pkh_mu_decode_len (u8 0) in
  let pkh = sub sk (crypto_secretkeybytes a -! bytes_pkhash a) (bytes_pkhash a) in

  concat2 (bytes_pkhash a) pkh (bytes_mu a) mu_decode pkh_mu_decode;
  frodo_shake a pkh_mu_decode_len pkh_mu_decode (2ul *! crypto_bytes a) seed_se_k;
  pop_frame ()


inline_for_extraction noextract
val crypto_kem_dec_ss1:
    a:FP.frodo_alg
  -> gen_a:FP.frodo_gen_a{is_supported gen_a}
  -> ct:lbytes (crypto_ciphertextbytes a)
  -> sk:lbytes (crypto_secretkeybytes a)
  -> mu_decode:lbytes (bytes_mu a)
  -> seed_se_k:lbytes (2ul *! crypto_bytes a)
  -> bp_matrix:matrix_t params_nbar (params_n a)
  -> c_matrix:matrix_t params_nbar params_nbar
  -> ss:lbytes (crypto_bytes a)
  -> Stack unit
    (requires fun h ->
      live h mu_decode /\ live h bp_matrix /\ live h seed_se_k /\
      live h c_matrix /\ live h sk /\ live h ct /\ live h ss /\
      loc_pairwise_disjoint [loc ct; loc sk; loc seed_se_k;
        loc mu_decode; loc bp_matrix; loc c_matrix; loc ss])
    (ensures fun h0 _ h1 -> modifies (loc ss) h0 h1 /\
      as_seq h1 ss == S.crypto_kem_dec_ss1 a gen_a (as_seq h0 ct) (as_seq h0 sk)
        (as_seq h0 mu_decode) (as_seq h0 seed_se_k) (as_matrix h0 bp_matrix) (as_matrix h0 c_matrix))

let crypto_kem_dec_ss1 a gen_a ct sk mu_decode seed_se_k bp_matrix c_matrix ss =
  let seed_se = sub seed_se_k 0ul (crypto_bytes a) in
  let kp = sub seed_se_k (crypto_bytes a) (crypto_bytes a) in
  let s = sub sk 0ul (crypto_bytes a) in

  let mask = crypto_kem_dec_kp_s a gen_a mu_decode seed_se sk bp_matrix c_matrix in
  crypto_kem_dec_ss0 a ct mask kp s ss


inline_for_extraction noextract
val crypto_kem_dec_ss2:
    a:FP.frodo_alg
  -> gen_a:FP.frodo_gen_a{is_supported gen_a}
  -> ct:lbytes (crypto_ciphertextbytes a)
  -> sk:lbytes (crypto_secretkeybytes a)
  -> mu_decode:lbytes (bytes_mu a)
  -> bp_matrix:matrix_t params_nbar (params_n a)
  -> c_matrix:matrix_t params_nbar params_nbar
  -> ss:lbytes (crypto_bytes a)
  -> Stack unit
    (requires fun h ->
      live h mu_decode /\ live h bp_matrix /\
      live h c_matrix /\ live h sk /\ live h ct /\ live h ss /\
      loc_pairwise_disjoint [loc ct; loc sk;
        loc mu_decode; loc bp_matrix; loc c_matrix; loc ss])
    (ensures fun h0 _ h1 -> modifies (loc ss) h0 h1 /\
      as_seq h1 ss == S.crypto_kem_dec_ss2 a gen_a (as_seq h0 ct) (as_seq h0 sk)
        (as_seq h0 mu_decode) (as_matrix h0 bp_matrix) (as_matrix h0 c_matrix))

let crypto_kem_dec_ss2 a gen_a ct sk mu_decode bp_matrix c_matrix ss =
  push_frame ();
  let seed_se_k = create (2ul *! crypto_bytes a) (u8 0) in
  crypto_kem_dec_seed_se_k a mu_decode sk seed_se_k;
  crypto_kem_dec_ss1 a gen_a ct sk mu_decode seed_se_k bp_matrix c_matrix ss;
  clear_words_u8 seed_se_k;
  pop_frame ()


inline_for_extraction noextract
val crypto_kem_dec_mu:
     a:FP.frodo_alg
  -> sk:lbytes (crypto_secretkeybytes a)
  -> bp_matrix:matrix_t params_nbar (params_n a)
  -> c_matrix:matrix_t params_nbar params_nbar
  -> mu_decode:lbytes (bytes_mu a)
  -> Stack unit
    (requires fun h ->
      live h sk /\ live h mu_decode /\
      live h bp_matrix /\ live h c_matrix /\
      as_seq h (mu_decode) == Seq.create (v (bytes_mu a)) (u8 0) /\
      loc_pairwise_disjoint [loc sk; loc mu_decode; loc bp_matrix; loc c_matrix])
    (ensures  fun h0 _ h1 -> modifies (loc mu_decode) h0 h1 /\
      as_seq h1 mu_decode == S.crypto_kem_dec_mu a (as_seq h0 sk)
        (as_matrix h0 bp_matrix) (as_matrix h0 c_matrix))

let crypto_kem_dec_mu a sk bp_matrix c_matrix mu_decode =
  FP.expand_crypto_secretkeybytes a;
  let s_bytes = sub sk (crypto_bytes a +! crypto_publickeybytes a) (secretmatrixbytes_len a) in
  frodo_mu_decode a s_bytes bp_matrix c_matrix mu_decode


inline_for_extraction noextract
val crypto_kem_dec0:
     a:FP.frodo_alg
  -> gen_a:FP.frodo_gen_a{is_supported gen_a}
  -> ss:lbytes (crypto_bytes a)
  -> ct:lbytes (crypto_ciphertextbytes a)
  -> sk:lbytes (crypto_secretkeybytes a)
  -> bp_matrix:matrix_t params_nbar (params_n a)
  -> c_matrix:matrix_t params_nbar params_nbar
  -> mu_decode:lbytes (bytes_mu a)
  -> Stack unit
    (requires fun h ->
      live h ss /\ live h ct /\ live h sk /\ live h mu_decode /\
      live h bp_matrix /\ live h c_matrix /\
      as_seq h (mu_decode) == Seq.create (v (bytes_mu a)) (u8 0) /\
      loc_pairwise_disjoint [loc ss; loc ct; loc sk;
        loc mu_decode; loc bp_matrix; loc c_matrix])
    (ensures  fun h0 _ h1 -> modifies (loc ss |+| loc mu_decode) h0 h1 /\
      as_seq h1 ss == S.crypto_kem_dec_ a gen_a (as_seq h0 ct)
        (as_seq h0 sk) (as_matrix h0 bp_matrix) (as_matrix h0 c_matrix))

let crypto_kem_dec0 a gen_a ss ct sk bp_matrix c_matrix mu_decode =
  crypto_kem_dec_mu a sk bp_matrix c_matrix mu_decode;
  crypto_kem_dec_ss2 a gen_a ct sk mu_decode bp_matrix c_matrix ss


inline_for_extraction noextract
val crypto_kem_dec1:
     a:FP.frodo_alg
  -> gen_a:FP.frodo_gen_a{is_supported gen_a}
  -> ss:lbytes (crypto_bytes a)
  -> ct:lbytes (crypto_ciphertextbytes a)
  -> sk:lbytes (crypto_secretkeybytes a)
  -> bp_matrix:matrix_t params_nbar (params_n a)
  -> c_matrix:matrix_t params_nbar params_nbar
  -> Stack unit
    (requires fun h ->
      live h ss /\ live h ct /\ live h sk /\
      live h bp_matrix /\ live h c_matrix /\
      loc_pairwise_disjoint [loc ss; loc ct; loc sk; loc bp_matrix; loc c_matrix])
    (ensures  fun h0 _ h1 -> modifies (loc ss) h0 h1 /\
      as_seq h1 ss == S.crypto_kem_dec_ a gen_a (as_seq h0 ct)
        (as_seq h0 sk) (as_matrix h0 bp_matrix) (as_matrix h0 c_matrix))

let crypto_kem_dec1 a gen_a ss ct sk bp_matrix c_matrix =
  push_frame ();
  let mu_decode = create (bytes_mu a) (u8 0) in
  crypto_kem_dec0 a gen_a ss ct sk bp_matrix c_matrix mu_decode;
  clear_words_u8 mu_decode;
  pop_frame ()


inline_for_extraction noextract
val crypto_kem_dec:
     a:FP.frodo_alg
  -> gen_a:FP.frodo_gen_a{is_supported gen_a}
  -> ss:lbytes (crypto_bytes a)
  -> ct:lbytes (crypto_ciphertextbytes a)
  -> sk:lbytes (crypto_secretkeybytes a)
  -> Stack uint32
    (requires fun h ->
      live h ss /\ live h ct /\ live h sk /\
      disjoint ss ct /\ disjoint ss sk /\ disjoint ct sk)
    (ensures  fun h0 _ h1 -> modifies (loc ss) h0 h1 /\
      as_seq h1 ss == S.crypto_kem_dec a gen_a (as_seq h0 ct) (as_seq h0 sk))

let crypto_kem_dec a gen_a ss ct sk =
  push_frame ();
  let bp_matrix = matrix_create params_nbar (params_n a) in
  let c_matrix  = matrix_create params_nbar params_nbar in

  get_bp_c_matrices a ct bp_matrix c_matrix;
  crypto_kem_dec1 a gen_a ss ct sk bp_matrix c_matrix;
  pop_frame ();
  u32 0
