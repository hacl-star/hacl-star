module Hacl.Impl.Frodo.KEM.Encaps

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Matrix
open Hacl.Impl.Frodo.Params
open Hacl.Impl.Frodo.KEM
open Hacl.Impl.Frodo.Encode
open Hacl.Impl.Frodo.Pack
open Hacl.Impl.Frodo.Sample
open Hacl.Frodo.Random

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module LB = Lib.ByteSequence

module FP = Spec.Frodo.Params
module S = Spec.Frodo.KEM.Encaps
module M = Spec.Matrix
module KG = Hacl.Impl.Frodo.KEM.KeyGen

#set-options "--z3rlimit 100 --fuel 0 --ifuel 0"

inline_for_extraction noextract
val frodo_mul_add_sa_plus_e:
    a:FP.frodo_alg
  -> gen_a:FP.frodo_gen_a{is_supported gen_a}
  -> seed_a:lbytes bytes_seed_a
  -> sp_matrix:matrix_t params_nbar (params_n a)
  -> ep_matrix:matrix_t params_nbar (params_n a)
  -> bp_matrix:matrix_t params_nbar (params_n a)
  -> Stack unit
    (requires fun h ->
      live h seed_a /\ live h ep_matrix /\ live h sp_matrix /\ live h bp_matrix /\
      disjoint bp_matrix seed_a /\ disjoint bp_matrix ep_matrix /\ disjoint bp_matrix sp_matrix)
    (ensures  fun h0 _ h1 -> modifies (loc bp_matrix) h0 h1 /\
      as_matrix h1 bp_matrix ==
      S.frodo_mul_add_sa_plus_e a gen_a (as_seq h0 seed_a) (as_matrix h0 sp_matrix) (as_matrix h0 ep_matrix))

let frodo_mul_add_sa_plus_e a gen_a seed_a sp_matrix ep_matrix bp_matrix =
  push_frame ();
  let a_matrix  = matrix_create (params_n a) (params_n a) in
  frodo_gen_matrix gen_a (params_n a) seed_a a_matrix;
  matrix_mul sp_matrix a_matrix bp_matrix;
  matrix_add bp_matrix ep_matrix;
  pop_frame ()


inline_for_extraction noextract
val crypto_kem_enc_ct_pack_c1:
    a:FP.frodo_alg
  -> gen_a:FP.frodo_gen_a{is_supported gen_a}
  -> seed_a:lbytes bytes_seed_a
  -> sp_matrix:matrix_t params_nbar (params_n a)
  -> ep_matrix:matrix_t params_nbar (params_n a)
  -> c1:lbytes (ct1bytes_len a)
  -> Stack unit
    (requires fun h ->
      live h seed_a /\ live h ep_matrix /\ live h sp_matrix /\ live h c1 /\
      disjoint seed_a c1 /\ disjoint ep_matrix c1 /\ disjoint sp_matrix c1)
    (ensures fun h0 _ h1 -> modifies (loc c1) h0 h1 /\
      as_seq h1 c1 ==
      S.crypto_kem_enc_ct_pack_c1 a gen_a (as_seq h0 seed_a) (as_matrix h0 sp_matrix) (as_matrix h0 ep_matrix))

let crypto_kem_enc_ct_pack_c1 a gen_a seed_a sp_matrix ep_matrix c1 =
  push_frame ();
  let bp_matrix = matrix_create params_nbar (params_n a) in
  frodo_mul_add_sa_plus_e a gen_a seed_a sp_matrix ep_matrix bp_matrix;
  frodo_pack (params_logq a) bp_matrix c1;
  pop_frame ()


inline_for_extraction noextract
val frodo_mul_add_sb_plus_e:
    a:FP.frodo_alg
  -> b:lbytes (publicmatrixbytes_len a)
  -> sp_matrix:matrix_t params_nbar (params_n a)
  -> epp_matrix:matrix_t params_nbar params_nbar
  -> v_matrix:matrix_t params_nbar params_nbar
  -> Stack unit
    (requires fun h ->
      live h b /\ live h epp_matrix /\ live h v_matrix /\ live h sp_matrix /\
      disjoint v_matrix b /\ disjoint v_matrix epp_matrix /\ disjoint v_matrix sp_matrix)
    (ensures fun h0 _ h1 -> modifies (loc v_matrix) h0 h1 /\
      as_matrix h1 v_matrix ==
      S.frodo_mul_add_sb_plus_e a (as_seq h0 b) (as_matrix h0 sp_matrix) (as_matrix h0 epp_matrix))

let frodo_mul_add_sb_plus_e a b sp_matrix epp_matrix v_matrix =
  push_frame ();
  let b_matrix = matrix_create (params_n a) params_nbar in
  frodo_unpack (params_n a) params_nbar (params_logq a) b b_matrix;
  matrix_mul sp_matrix b_matrix v_matrix;
  matrix_add v_matrix epp_matrix;
  pop_frame ()


inline_for_extraction noextract
val frodo_mul_add_sb_plus_e_plus_mu:
    a:FP.frodo_alg
  -> mu:lbytes (bytes_mu a)
  -> b:lbytes (publicmatrixbytes_len a)
  -> sp_matrix:matrix_t params_nbar (params_n a)
  -> epp_matrix:matrix_t params_nbar params_nbar
  -> v_matrix:matrix_t params_nbar params_nbar
  -> Stack unit
    (requires fun h ->
      live h b /\ live h mu /\ live h v_matrix /\
      live h sp_matrix /\ live h epp_matrix /\
      disjoint v_matrix b /\ disjoint v_matrix sp_matrix /\
      disjoint v_matrix mu /\ disjoint v_matrix epp_matrix)
    (ensures fun h0 _ h1 -> modifies (loc v_matrix) h0 h1 /\
      as_matrix h1 v_matrix ==
      S.frodo_mul_add_sb_plus_e_plus_mu a (as_seq h0 mu) (as_seq h0 b) (as_matrix h0 sp_matrix) (as_matrix h0 epp_matrix))

let frodo_mul_add_sb_plus_e_plus_mu a mu b sp_matrix epp_matrix v_matrix =
  push_frame ();
  frodo_mul_add_sb_plus_e a b sp_matrix epp_matrix v_matrix;
  let mu_encode = matrix_create params_nbar params_nbar in
  frodo_key_encode (params_logq a) (params_extracted_bits a) params_nbar mu mu_encode;
  matrix_add v_matrix mu_encode;
  clear_matrix mu_encode;
  pop_frame ()


inline_for_extraction noextract
val crypto_kem_enc_ct_pack_c2:
    a:FP.frodo_alg
  -> mu:lbytes (bytes_mu a)
  -> b:lbytes (publicmatrixbytes_len a)
  -> sp_matrix:matrix_t params_nbar (params_n a)
  -> epp_matrix:matrix_t params_nbar params_nbar
  -> c2:lbytes (ct2bytes_len a)
  -> Stack unit
    (requires fun h ->
      live h mu /\ live h b /\ live h sp_matrix /\
      live h epp_matrix /\ live h c2 /\
      disjoint mu c2 /\ disjoint b c2 /\
      disjoint sp_matrix c2 /\ disjoint epp_matrix c2)
    (ensures fun h0 _ h1 -> modifies (loc c2) h0 h1 /\
      as_seq h1 c2 ==
      S.crypto_kem_enc_ct_pack_c2 a (as_seq h0 mu) (as_seq h0 b) (as_matrix h0 sp_matrix) (as_matrix h0 epp_matrix))

#push-options "--z3rlimit 200"
let crypto_kem_enc_ct_pack_c2 a mu b sp_matrix epp_matrix c2 =
  push_frame ();
  let v_matrix = matrix_create params_nbar params_nbar in
  frodo_mul_add_sb_plus_e_plus_mu a mu b sp_matrix epp_matrix v_matrix;
  frodo_pack (params_logq a) v_matrix c2;
  clear_matrix v_matrix;
  pop_frame ()
#pop-options

inline_for_extraction noextract
val get_sp_ep_epp_matrices:
    a:FP.frodo_alg
  -> seed_se:lbytes (crypto_bytes a)
  -> sp_matrix:matrix_t params_nbar (params_n a)
  -> ep_matrix:matrix_t params_nbar (params_n a)
  -> epp_matrix:matrix_t params_nbar params_nbar
  -> Stack unit
    (requires fun h ->
      live h seed_se /\ live h sp_matrix /\
      live h ep_matrix /\ live h epp_matrix /\
      disjoint seed_se sp_matrix /\ disjoint seed_se ep_matrix /\
      disjoint seed_se epp_matrix /\ disjoint sp_matrix ep_matrix /\
      disjoint sp_matrix epp_matrix /\ disjoint ep_matrix epp_matrix)
    (ensures  fun h0 _ h1 -> modifies (loc sp_matrix |+| loc ep_matrix |+| loc epp_matrix) h0 h1 /\
      (as_matrix h1 sp_matrix, as_matrix h1 ep_matrix, as_matrix h1 epp_matrix) ==
      S.get_sp_ep_epp_matrices a (as_seq h0 seed_se))

let get_sp_ep_epp_matrices a seed_se sp_matrix ep_matrix epp_matrix =
  push_frame ();
  [@inline_let] let s_bytes_len = secretmatrixbytes_len a in
  let r = create (2ul *! s_bytes_len +! 2ul *! params_nbar *! params_nbar) (u8 0) in
  KG.frodo_shake_r a (u8 0x96) seed_se (2ul *! s_bytes_len +! 2ul *! params_nbar *! params_nbar) r;
  frodo_sample_matrix a params_nbar (params_n a) (sub r 0ul s_bytes_len) sp_matrix;
  frodo_sample_matrix a params_nbar (params_n a) (sub r s_bytes_len s_bytes_len) ep_matrix;
  frodo_sample_matrix a params_nbar params_nbar (sub r (2ul *! s_bytes_len) (2ul *! params_nbar *! params_nbar)) epp_matrix;
  pop_frame ()


inline_for_extraction noextract
val crypto_kem_enc_ct0:
    a:FP.frodo_alg
  -> gen_a:FP.frodo_gen_a{is_supported gen_a}
  -> seed_a:lbytes bytes_seed_a
  -> b:lbytes (publicmatrixbytes_len a)
  -> mu:lbytes (bytes_mu a)
  -> sp_matrix:matrix_t params_nbar (params_n a)
  -> ep_matrix:matrix_t params_nbar (params_n a)
  -> epp_matrix:matrix_t params_nbar params_nbar
  -> ct:lbytes (crypto_ciphertextbytes a)
  -> Stack unit
    (requires fun h ->
      live h seed_a /\ live h b /\ live h mu /\ live h ct /\
      live h sp_matrix /\ live h ep_matrix /\ live h epp_matrix /\
      disjoint ct seed_a /\ disjoint ct b /\ disjoint ct mu /\
      disjoint ct sp_matrix /\ disjoint ct ep_matrix /\ disjoint ct epp_matrix)
    (ensures fun h0 _ h1 -> modifies (loc ct) h0 h1 /\
      (let c1:LB.lbytes (FP.ct1bytes_len a) = S.crypto_kem_enc_ct_pack_c1 a gen_a (as_seq h0 seed_a) (as_seq h0 sp_matrix) (as_seq h0 ep_matrix) in
      let c2:LB.lbytes (FP.ct2bytes_len a) = S.crypto_kem_enc_ct_pack_c2 a (as_seq h0 mu) (as_seq h0 b) (as_seq h0 sp_matrix) (as_seq h0 epp_matrix) in
      v (crypto_ciphertextbytes a) == FP.ct1bytes_len a + FP.ct2bytes_len a /\
      as_seq h1 ct `Seq.equal` LSeq.concat #_ #(FP.ct1bytes_len a) #(FP.ct2bytes_len a) c1 c2))

let crypto_kem_enc_ct0 a gen_a seed_a b mu sp_matrix ep_matrix epp_matrix ct =
  let c1 = sub ct 0ul (ct1bytes_len a) in
  let c2 = sub ct (ct1bytes_len a) (ct2bytes_len a) in
  let h0 = ST.get () in
  crypto_kem_enc_ct_pack_c1 a gen_a seed_a sp_matrix ep_matrix c1;
  let h1 = ST.get () in
  crypto_kem_enc_ct_pack_c2 a mu b sp_matrix epp_matrix c2;
  let h2 = ST.get () in
  LSeq.eq_intro
    (LSeq.sub (as_seq h2 ct) 0 (v (ct1bytes_len a)))
    (LSeq.sub (as_seq h1 ct) 0 (v (ct1bytes_len a)));
  LSeq.lemma_concat2
    (v (ct1bytes_len a)) (LSeq.sub (as_seq h1 ct) 0 (v (ct1bytes_len a)))
    (v (ct2bytes_len a)) (LSeq.sub (as_seq h2 ct) (v (ct1bytes_len a)) (v (ct2bytes_len a))) (as_seq h2 ct)


inline_for_extraction noextract
val clear_matrix3:
    a:FP.frodo_alg
  -> sp_matrix:matrix_t params_nbar (params_n a)
  -> ep_matrix:matrix_t params_nbar (params_n a)
  -> epp_matrix:matrix_t params_nbar params_nbar
  -> Stack unit
    (requires fun h ->
      live h sp_matrix /\ live h ep_matrix /\ live h epp_matrix /\
      disjoint sp_matrix ep_matrix /\ disjoint sp_matrix epp_matrix /\
      disjoint ep_matrix epp_matrix)
    (ensures  fun h0 _ h1 ->
      modifies (loc sp_matrix |+| loc ep_matrix |+| loc epp_matrix) h0 h1)

let clear_matrix3 a sp_matrix ep_matrix epp_matrix =
  clear_matrix sp_matrix;
  clear_matrix ep_matrix;
  clear_matrix epp_matrix

inline_for_extraction noextract
val crypto_kem_enc_ct:
    a:FP.frodo_alg
  -> gen_a:FP.frodo_gen_a{is_supported gen_a}
  -> mu:lbytes (bytes_mu a)
  -> pk:lbytes (crypto_publickeybytes a)
  -> seed_se:lbytes (crypto_bytes a)
  -> ct:lbytes (crypto_ciphertextbytes a)
  -> Stack unit
    (requires fun h ->
      live h mu /\ live h pk /\ live h seed_se /\ live h ct /\
      disjoint ct mu /\ disjoint ct pk /\ disjoint ct seed_se)
    (ensures fun h0 _ h1 -> modifies (loc ct) h0 h1 /\
      as_seq h1 ct == S.crypto_kem_enc_ct a gen_a (as_seq h0 mu) (as_seq h0 pk) (as_seq h0 seed_se))

#push-options "--z3rlimit 200"
let crypto_kem_enc_ct a gen_a mu pk seed_se ct =
  push_frame ();
  let h0 = ST.get () in
  FP.expand_crypto_publickeybytes a;
  let seed_a = sub pk 0ul bytes_seed_a in
  let b = sub pk bytes_seed_a (publicmatrixbytes_len a) in

  let sp_matrix = matrix_create params_nbar (params_n a) in
  let ep_matrix = matrix_create params_nbar (params_n a) in
  let epp_matrix = matrix_create params_nbar params_nbar in
  get_sp_ep_epp_matrices a seed_se sp_matrix ep_matrix epp_matrix;
  crypto_kem_enc_ct0 a gen_a seed_a b mu sp_matrix ep_matrix epp_matrix ct;

  clear_matrix3 a sp_matrix ep_matrix epp_matrix;
  let h1 = ST.get () in
  LSeq.eq_intro
    (as_seq h1 ct)
    (S.crypto_kem_enc_ct a gen_a (as_seq h0 mu) (as_seq h0 pk) (as_seq h0 seed_se));
  pop_frame ()
#pop-options

inline_for_extraction noextract
val crypto_kem_enc_ss:
    a:FP.frodo_alg
  -> k:lbytes (crypto_bytes a)
  -> ct:lbytes (crypto_ciphertextbytes a)
  -> ss:lbytes (crypto_bytes a)
  -> Stack unit
    (requires fun h ->
      live h k /\ live h ct /\ live h ss /\
      disjoint ct ss /\ disjoint k ct /\ disjoint k ss)
    (ensures  fun h0 _ h1 -> modifies (loc ss) h0 h1 /\
      as_seq h1 ss == S.crypto_kem_enc_ss a (as_seq h0 k) (as_seq h0 ct))

let crypto_kem_enc_ss a k ct ss =
  push_frame ();
  let ss_init_len = crypto_ciphertextbytes a +! crypto_bytes a in
  let shake_input_ss = create ss_init_len (u8 0) in
  concat2 (crypto_ciphertextbytes a) ct (crypto_bytes a) k shake_input_ss;
  frodo_shake a ss_init_len shake_input_ss (crypto_bytes a) ss;
  clear_words_u8 shake_input_ss;
  pop_frame ()


inline_for_extraction noextract
val crypto_kem_enc_seed_se_k:
    a:FP.frodo_alg
  -> mu:lbytes (bytes_mu a)
  -> pk:lbytes (crypto_publickeybytes a)
  -> seed_se_k:lbytes (2ul *! crypto_bytes a)
  -> Stack unit
    (requires fun h ->
      live h mu /\ live h pk /\ live h seed_se_k /\
      disjoint seed_se_k mu /\ disjoint seed_se_k pk)
    (ensures  fun h0 _ h1 -> modifies (loc seed_se_k) h0 h1 /\
      as_seq h1 seed_se_k == S.crypto_kem_enc_seed_se_k a (as_seq h0 mu) (as_seq h0 pk))

let crypto_kem_enc_seed_se_k a mu pk seed_se_k =
  push_frame ();
  let pkh_mu = create (bytes_pkhash a +! bytes_mu a) (u8 0) in
  let h0 = ST.get () in
  update_sub_f h0 pkh_mu 0ul (bytes_pkhash a)
    (fun h -> FP.frodo_shake a (v (crypto_publickeybytes a)) (as_seq h0 pk) (v (bytes_pkhash a)))
    (fun _ -> frodo_shake a (crypto_publickeybytes a) pk (bytes_pkhash a) (sub pkh_mu 0ul (bytes_pkhash a)));

  let h1 = ST.get () in
  update_sub pkh_mu (bytes_pkhash a) (bytes_mu a) mu;
  let h2 = ST.get () in
  LSeq.eq_intro
    (LSeq.sub (as_seq h2 pkh_mu) 0 (v (bytes_pkhash a)))
    (LSeq.sub (as_seq h1 pkh_mu) 0 (v (bytes_pkhash a)));
  LSeq.lemma_concat2
    (v (bytes_pkhash a)) (LSeq.sub (as_seq h1 pkh_mu) 0 (v (bytes_pkhash a)))
    (v (bytes_mu a)) (as_seq h0 mu) (as_seq h2 pkh_mu);
  //concat2 (bytes_pkhash a) pkh (bytes_mu a) mu pkh_mu;
  frodo_shake a (bytes_pkhash a +! bytes_mu a) pkh_mu (2ul *! crypto_bytes a) seed_se_k;
  pop_frame ()


inline_for_extraction noextract
val crypto_kem_enc_ct_ss:
    a:FP.frodo_alg
  -> gen_a:FP.frodo_gen_a{is_supported gen_a}
  -> seed_se_k:lbytes (2ul *! crypto_bytes a)
  -> mu:lbytes (bytes_mu a)
  -> ct:lbytes (crypto_ciphertextbytes a)
  -> ss:lbytes (crypto_bytes a)
  -> pk:lbytes (crypto_publickeybytes a)
  -> Stack unit
    (requires fun h ->
      live h seed_se_k /\ live h ct /\ live h ss /\ live h pk /\ live h mu /\
      disjoint ct ss /\ disjoint ct pk /\ disjoint ss pk /\
      disjoint mu ss /\ disjoint mu ct /\ disjoint seed_se_k ct /\ disjoint seed_se_k ss)
    (ensures  fun h0 _ h1 -> modifies (loc ct |+| loc ss) h0 h1 /\
     (let seed_se = LSeq.sub (as_seq h0 seed_se_k) 0 (v (crypto_bytes a)) in
      let k = LSeq.sub (as_seq h0 seed_se_k) (v (crypto_bytes a)) (v (crypto_bytes a)) in
      as_seq h1 ct == S.crypto_kem_enc_ct a gen_a (as_seq h0 mu) (as_seq h0 pk) seed_se /\
      as_seq h1 ss == S.crypto_kem_enc_ss a k (as_seq h1 ct)))

let crypto_kem_enc_ct_ss a gen_a seed_se_k mu ct ss pk =
  let seed_se = sub seed_se_k 0ul (crypto_bytes a) in
  let k = sub seed_se_k (crypto_bytes a) (crypto_bytes a) in
  crypto_kem_enc_ct a gen_a mu pk seed_se ct;
  crypto_kem_enc_ss a k ct ss


inline_for_extraction noextract
val crypto_kem_enc0:
     a:FP.frodo_alg
  -> gen_a:FP.frodo_gen_a{is_supported gen_a}
  -> mu:lbytes (bytes_mu a)
  -> ct:lbytes (crypto_ciphertextbytes a)
  -> ss:lbytes (crypto_bytes a)
  -> pk:lbytes (crypto_publickeybytes a)
  -> seed_se_k:lbytes (2ul *! crypto_bytes a)
  -> Stack unit
    (requires fun h ->
      live h ct /\ live h ss /\ live h pk /\ live h mu /\ live h seed_se_k /\
      loc_pairwise_disjoint [loc mu; loc ct; loc ss; loc pk; loc seed_se_k])
    (ensures  fun h0 _ h1 -> modifies (loc ct |+| loc ss |+| loc seed_se_k) h0 h1 /\
      (as_seq h1 ct, as_seq h1 ss) == S.crypto_kem_enc_ a gen_a (as_seq h0 mu) (as_seq h0 pk))

#push-options "--z3rlimit 200"
let crypto_kem_enc0 a gen_a mu ct ss pk seed_se_k =
  crypto_kem_enc_seed_se_k a mu pk seed_se_k;
  crypto_kem_enc_ct_ss a gen_a seed_se_k mu ct ss pk
#pop-options

inline_for_extraction noextract
val crypto_kem_enc_:
     a:FP.frodo_alg
  -> gen_a:FP.frodo_gen_a{is_supported gen_a}
  -> mu:lbytes (bytes_mu a)
  -> ct:lbytes (crypto_ciphertextbytes a)
  -> ss:lbytes (crypto_bytes a)
  -> pk:lbytes (crypto_publickeybytes a)
  -> Stack unit
    (requires fun h ->
      live h ct /\ live h ss /\ live h pk /\ live h mu /\
      disjoint ct ss /\ disjoint ct pk /\ disjoint ss pk /\
      disjoint mu ss /\ disjoint mu ct /\ disjoint mu pk)
    (ensures  fun h0 _ h1 -> modifies (loc ct |+| loc ss) h0 h1 /\
      (as_seq h1 ct, as_seq h1 ss) == S.crypto_kem_enc_ a gen_a (as_seq h0 mu) (as_seq h0 pk))

let crypto_kem_enc_ a gen_a mu ct ss pk =
  push_frame ();
  let seed_se_k = create (2ul *! crypto_bytes a) (u8 0) in
  crypto_kem_enc0 a gen_a mu ct ss pk seed_se_k;
  clear_words_u8 seed_se_k;
  pop_frame ()


inline_for_extraction noextract
val crypto_kem_enc:
     a:FP.frodo_alg
  -> gen_a:FP.frodo_gen_a{is_supported gen_a}
  -> ct:lbytes (crypto_ciphertextbytes a)
  -> ss:lbytes (crypto_bytes a)
  -> pk:lbytes (crypto_publickeybytes a)
  -> Stack uint32
    (requires fun h ->
      disjoint state ct /\ disjoint state ss /\ disjoint state pk /\
      live h ct /\ live h ss /\ live h pk /\
      disjoint ct ss /\ disjoint ct pk /\ disjoint ss pk)
    (ensures  fun h0 _ h1 -> modifies (loc state |+| (loc ct |+| loc ss)) h0 h1 /\
      (as_seq h1 ct, as_seq h1 ss) == S.crypto_kem_enc a gen_a (as_seq h0 state) (as_seq h0 pk))

let crypto_kem_enc a gen_a ct ss pk =
  recall state;
  push_frame ();
  let coins = create (bytes_mu a) (u8 0) in
  recall state;
  randombytes_ (bytes_mu a) coins;
  crypto_kem_enc_ a gen_a coins ct ss pk;
  clear_words_u8 coins;
  pop_frame ();
  u32 0
