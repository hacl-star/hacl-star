module Hacl.Impl.Frodo.KEM.Encaps

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
open Hacl.Impl.Frodo.Encode
open Hacl.Impl.Frodo.Pack
open Hacl.Impl.Frodo.Sample
open Hacl.Frodo.Random
open Hacl.Frodo.Clear

module ST = FStar.HyperStack.ST
module Lemmas = Spec.Frodo.Lemmas
module S = Spec.Frodo.KEM.Encaps
module M = Spec.Matrix
module LSeq = Lib.Sequence

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val frodo_mul_add_sa_plus_e:
    seed_a:lbytes bytes_seed_a
  -> sp_matrix:matrix_t params_nbar params_n
  -> ep_matrix:matrix_t params_nbar params_n
  -> bp_matrix:matrix_t params_nbar params_n
  -> a_matrix:matrix_t params_n params_n
  -> Stack unit
    (requires fun h ->
      live h a_matrix /\ live h seed_a /\ live h ep_matrix /\
      live h bp_matrix /\ live h sp_matrix /\
      disjoint seed_a a_matrix /\ disjoint a_matrix bp_matrix /\
      disjoint sp_matrix bp_matrix /\ disjoint bp_matrix ep_matrix /\
      disjoint sp_matrix a_matrix /\ disjoint ep_matrix a_matrix /\
      disjoint sp_matrix ep_matrix)
    (ensures  fun h0 _ h1 ->
      modifies (loc_union (loc_buffer bp_matrix) (loc_buffer a_matrix)) h0 h1 /\
      as_matrix h1 a_matrix == Spec.Frodo.Params.frodo_gen_matrix (v params_n) (v bytes_seed_a) (as_seq h0 seed_a) /\
      as_matrix h1 bp_matrix == M.add (M.mul (as_matrix h0 sp_matrix) (as_matrix h1 a_matrix)) (as_matrix h0 ep_matrix))
[@"c_inline"]
let frodo_mul_add_sa_plus_e seed_a sp_matrix ep_matrix bp_matrix a_matrix =
  frodo_gen_matrix params_n bytes_seed_a seed_a a_matrix;
  matrix_mul sp_matrix a_matrix bp_matrix;
  matrix_add bp_matrix ep_matrix

inline_for_extraction noextract
val frodo_mul_add_sa_plus_e_inner:
    seed_a:lbytes bytes_seed_a
  -> sp_matrix:matrix_t params_nbar params_n
  -> ep_matrix:matrix_t params_nbar params_n
  -> bp_matrix:matrix_t params_nbar params_n
  -> a_matrix:matrix_t params_n params_n
  -> Stack unit
    (requires fun h ->
      live h a_matrix /\ live h seed_a /\ live h ep_matrix /\
      live h bp_matrix /\ live h sp_matrix /\
      disjoint seed_a a_matrix /\ disjoint a_matrix bp_matrix /\
      disjoint sp_matrix bp_matrix /\ disjoint bp_matrix ep_matrix /\
      disjoint sp_matrix a_matrix /\ disjoint ep_matrix a_matrix /\
      disjoint sp_matrix ep_matrix)
    (ensures  fun h0 _ h1 ->
      modifies (loc_union (loc_buffer ep_matrix) (loc_union (loc_buffer bp_matrix) (loc_buffer a_matrix))) h0 h1 /\
      as_matrix h1 a_matrix == Spec.Frodo.Params.frodo_gen_matrix (v params_n) (v bytes_seed_a) (as_seq h0 seed_a) /\
      as_matrix h1 bp_matrix == M.add (M.mul (as_matrix h0 sp_matrix) (as_matrix h1 a_matrix)) (as_matrix h0 ep_matrix))
let frodo_mul_add_sa_plus_e_inner seed_a sp_matrix ep_matrix bp_matrix a_matrix =
  frodo_mul_add_sa_plus_e seed_a sp_matrix ep_matrix bp_matrix a_matrix;
  assert_norm (v params_nbar * v params_n % 2 = 0);
  clear_matrix ep_matrix

inline_for_extraction noextract
val frodo_mul_add_sa_plus_e_main:
    seed_a:lbytes bytes_seed_a
  -> seed_e:lbytes crypto_bytes
  -> sp_matrix:matrix_t params_nbar params_n
  -> bp_matrix:matrix_t params_nbar params_n
  -> Stack unit
    (requires fun h ->
      live h seed_a /\ live h seed_e /\ live h bp_matrix /\ live h sp_matrix /\
      disjoint bp_matrix sp_matrix /\ disjoint bp_matrix seed_a /\ disjoint bp_matrix seed_e)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer bp_matrix) h0 h1 /\
      as_matrix h1 bp_matrix == S.frodo_mul_add_sa_plus_e (as_seq h0 seed_a) (as_seq h0 seed_e) (as_matrix h0 sp_matrix))
let frodo_mul_add_sa_plus_e_main seed_a seed_e sp_matrix bp_matrix =
  push_frame();
  let a_matrix = matrix_create params_n params_n in
  let ep_matrix = matrix_create params_nbar params_n in

  frodo_sample_matrix params_nbar params_n crypto_bytes seed_e (u16 5) ep_matrix;
  frodo_mul_add_sa_plus_e_inner seed_a sp_matrix ep_matrix bp_matrix a_matrix;
  pop_frame()

val frodo_mul_add_sb_plus_e:
    sp_matrix:matrix_t params_nbar params_n
  -> epp_matrix:matrix_t params_nbar params_nbar
  -> b_matrix:matrix_t params_n params_nbar
  -> v_matrix:matrix_t params_nbar params_nbar
  -> Stack unit
    (requires fun h ->
      live h sp_matrix /\ live h epp_matrix /\ live h b_matrix /\ live h v_matrix /\
      disjoint v_matrix sp_matrix /\ disjoint b_matrix v_matrix /\ disjoint v_matrix epp_matrix)
    (ensures fun h0 _ h1 -> modifies (loc_buffer v_matrix) h0 h1 /\
      as_matrix h1 v_matrix == M.add (M.mul (as_matrix h0 sp_matrix) (as_matrix h0 b_matrix)) (as_matrix h0 epp_matrix))
[@"c_inline"]
let frodo_mul_add_sb_plus_e sp_matrix epp_matrix b_matrix v_matrix =
  matrix_mul sp_matrix b_matrix v_matrix;
  matrix_add v_matrix epp_matrix

inline_for_extraction noextract
val frodo_mul_add_sb_plus_e_inner:
    sp_matrix:matrix_t params_nbar params_n
  -> epp_matrix:matrix_t params_nbar params_nbar
  -> b_matrix:matrix_t params_n params_nbar
  -> v_matrix:matrix_t params_nbar params_nbar
  -> Stack unit
    (requires fun h ->
      live h sp_matrix /\ live h epp_matrix /\ live h b_matrix /\ live h v_matrix /\
      disjoint v_matrix sp_matrix /\ disjoint b_matrix v_matrix /\ disjoint v_matrix epp_matrix)
    (ensures fun h0 _ h1 -> modifies (loc_union (loc_buffer v_matrix) (loc_buffer epp_matrix)) h0 h1 /\
      as_matrix h1 v_matrix == M.add (M.mul (as_matrix h0 sp_matrix) (as_matrix h0 b_matrix)) (as_matrix h0 epp_matrix))
let frodo_mul_add_sb_plus_e_inner sp_matrix epp_matrix b_matrix v_matrix =
  frodo_mul_add_sb_plus_e sp_matrix epp_matrix b_matrix v_matrix;
  assert_norm (v params_nbar * v params_nbar % 2 == 0);
  clear_matrix epp_matrix

inline_for_extraction noextract
val frodo_mul_add_sb_plus_e_main:
    b:lbytes (params_logq *! params_n *! params_nbar /. size 8)
  -> seed_e:lbytes crypto_bytes
  -> sp_matrix:matrix_t params_nbar params_n
  -> v_matrix:matrix_t params_nbar params_nbar
  -> Stack unit
    (requires fun h ->
      live h b /\ live h seed_e /\ live h v_matrix /\ live h sp_matrix /\
      disjoint v_matrix b /\ disjoint v_matrix seed_e /\ disjoint v_matrix sp_matrix)
    (ensures fun h0 _ h1 -> modifies (loc_buffer v_matrix) h0 h1 /\
      as_matrix h1 v_matrix == S.frodo_mul_add_sb_plus_e (as_seq h0 b) (as_seq h0 seed_e) (as_matrix h0 sp_matrix))
let frodo_mul_add_sb_plus_e_main b seed_e sp_matrix v_matrix =
  push_frame();
  let b_matrix   = matrix_create params_n params_nbar in
  let epp_matrix = matrix_create params_nbar params_nbar in

  frodo_sample_matrix params_nbar params_nbar crypto_bytes seed_e (u16 6) epp_matrix;
  assert (v params_nbar % 8 = 0);
  frodo_unpack params_n params_nbar params_logq b b_matrix;

  frodo_mul_add_sb_plus_e_inner sp_matrix epp_matrix b_matrix v_matrix;
  pop_frame()

inline_for_extraction noextract
val frodo_mul_add_sb_plus_e_plus_mu_inner:
    coins:lbytes (params_nbar *! params_nbar *! params_extracted_bits /. size 8)
  -> v_matrix:matrix_t params_nbar params_nbar
  -> Stack unit
    (requires fun h ->
      live h coins /\ live h v_matrix /\ disjoint v_matrix coins)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer v_matrix) h0 h1 /\
      (let mu_encode = Spec.Frodo.Encode.frodo_key_encode (v params_extracted_bits) (as_seq h0 coins) in
       as_matrix h1 v_matrix == M.add (as_matrix h0 v_matrix) mu_encode))
let frodo_mul_add_sb_plus_e_plus_mu_inner coins v_matrix =
  push_frame();
  let mu_encode  = matrix_create params_nbar params_nbar in
  frodo_key_encode params_extracted_bits coins mu_encode;
  matrix_add v_matrix mu_encode;
  pop_frame()

val frodo_mul_add_sb_plus_e_plus_mu:
    b:lbytes (params_logq *! params_n *! params_nbar /. size 8)
  -> seed_e:lbytes crypto_bytes
  -> coins:lbytes (params_nbar *! params_nbar *! params_extracted_bits /. size 8)
  -> sp_matrix:matrix_t params_nbar params_n
  -> v_matrix:matrix_t params_nbar params_nbar
  -> Stack unit
    (requires fun h ->
      live h b /\ live h seed_e /\ live h coins /\ live h v_matrix /\ live h sp_matrix /\
      disjoint v_matrix b /\ disjoint v_matrix seed_e /\ disjoint v_matrix sp_matrix /\
      disjoint v_matrix coins)
    (ensures fun h0 _ h1 -> modifies (loc_buffer v_matrix) h0 h1 /\
      as_matrix h1 v_matrix == S.frodo_mul_add_sb_plus_e_plus_mu (as_seq h0 b) (as_seq h0 seed_e) (as_seq h0 coins) (as_matrix h0 sp_matrix))
[@"c_inline"]
let frodo_mul_add_sb_plus_e_plus_mu b seed_e coins sp_matrix v_matrix =
  frodo_mul_add_sb_plus_e_main b seed_e sp_matrix v_matrix;
  frodo_mul_add_sb_plus_e_plus_mu_inner coins v_matrix

inline_for_extraction noextract
val crypto_kem_enc_ct_pack_c1:
    seed_a:lbytes bytes_seed_a
  -> seed_e:lbytes crypto_bytes
  -> sp_matrix:matrix_t params_nbar params_n
  -> c1:lbytes (params_logq *! params_nbar *! params_n /. size 8)
  -> Stack unit
    (requires fun h ->
      live h seed_a /\ live h seed_e /\ live h sp_matrix /\ live h c1 /\
      disjoint seed_a c1 /\ disjoint seed_e c1 /\ disjoint sp_matrix c1)
    (ensures fun h0 _ h1 -> modifies (loc_buffer c1) h0 h1 /\
      as_seq h1 c1 == S.crypto_kem_enc_ct_pack_c1 (as_seq h0 seed_a) (as_seq h0 seed_e) (as_matrix h0 sp_matrix))
let crypto_kem_enc_ct_pack_c1 seed_a seed_e sp_matrix c1 =
  push_frame();
  let bp_matrix = matrix_create params_nbar params_n in
  frodo_mul_add_sa_plus_e_main seed_a seed_e sp_matrix bp_matrix;
  assert (v params_n % 8 = 0);
  frodo_pack bp_matrix params_logq c1;
  pop_frame()

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq
  -Spec.Frodo.KEM.Encaps'"

inline_for_extraction noextract
val crypto_kem_enc_ct_pack_c2_inner:
    seed_e:lbytes crypto_bytes
  -> coins:lbytes (params_nbar *! params_nbar *! params_extracted_bits /. size 8)
  -> b:lbytes (params_logq *! params_n *! params_nbar /. size 8)
  -> sp_matrix:matrix_t params_nbar params_n
  -> c2:lbytes (params_logq *! params_nbar *! params_nbar /. size 8)
  -> v_matrix:matrix_t params_nbar params_nbar
  -> Stack unit
    (requires fun h ->
      live h seed_e /\ live h coins /\ live h b /\
      live h sp_matrix /\ live h c2 /\ live h v_matrix /\
      disjoint seed_e c2 /\ disjoint coins c2 /\ disjoint b c2 /\ disjoint sp_matrix c2 /\
      disjoint c2 v_matrix /\ disjoint seed_e v_matrix /\ disjoint coins v_matrix /\
      disjoint b v_matrix /\ disjoint sp_matrix v_matrix)
    (ensures fun h0 _ h1 -> modifies (loc_union (loc_buffer c2) (loc_buffer v_matrix)) h0 h1 /\
      as_matrix h1 v_matrix == S.frodo_mul_add_sb_plus_e_plus_mu (as_seq h0 b) (as_seq h0 seed_e) (as_seq h0 coins) (as_matrix h0 sp_matrix) /\
      as_seq h1 c2 == Spec.Frodo.Pack.frodo_pack (as_matrix h1 v_matrix) (v params_logq))
let crypto_kem_enc_ct_pack_c2_inner seed_e coins b sp_matrix c2 v_matrix =
  let n1 = params_nbar in
  let n2 = params_nbar in
  let d = params_logq in
  assert_norm (v d * v n1 < max_size_t /\ (v d * v n1) * v n2 < max_size_t /\ v d <= 16);
  frodo_mul_add_sb_plus_e_plus_mu b seed_e coins sp_matrix v_matrix;
  frodo_pack v_matrix params_logq c2

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

inline_for_extraction noextract
val crypto_kem_enc_ct_pack_c2:
    seed_e:lbytes crypto_bytes
  -> coins:lbytes (params_nbar *! params_nbar *! params_extracted_bits /. size 8)
  -> b:lbytes (params_logq *! params_n *! params_nbar /. size 8)
  -> sp_matrix:matrix_t params_nbar params_n
  -> c2:lbytes (params_logq *! params_nbar *! params_nbar /. size 8)
  -> Stack unit
    (requires fun h ->
      live h seed_e /\ live h coins /\ live h b /\ live h sp_matrix /\ live h c2 /\
      disjoint seed_e c2 /\ disjoint coins c2 /\ disjoint b c2 /\ disjoint sp_matrix c2)
    (ensures fun h0 _ h1 -> modifies (loc_buffer c2) h0 h1 /\
      as_seq h1 c2 == S.crypto_kem_enc_ct_pack_c2 (as_seq h0 seed_e) (as_seq h0 coins) (as_seq h0 b) (as_matrix h0 sp_matrix))
let crypto_kem_enc_ct_pack_c2 seed_e coins b sp_matrix c2 =
  assert (v params_nbar * v params_nbar % 2 == 0);
  push_frame();
  let v_matrix = matrix_create params_nbar params_nbar in
  crypto_kem_enc_ct_pack_c2_inner seed_e coins b sp_matrix c2 v_matrix;
  clear_matrix v_matrix;
  pop_frame()

inline_for_extraction noextract
val crypto_kem_enc_ct_inner:
    seed_a:lbytes bytes_seed_a
  -> seed_e:lbytes crypto_bytes
  -> b:lbytes (params_logq *! params_n *! params_nbar /. size 8)
  -> coins:lbytes (params_nbar *! params_nbar *! params_extracted_bits /. size 8)
  -> sp_matrix:matrix_t params_nbar params_n
  -> d:lbytes crypto_bytes
  -> ct:lbytes crypto_ciphertextbytes
  -> Stack unit
    (requires fun h ->
      live h seed_a /\ live h seed_e /\ live h b /\ live h coins /\
      live h sp_matrix /\ live h ct /\ live h d /\
      disjoint coins ct /\ disjoint b ct /\ disjoint d ct /\
      disjoint seed_a ct /\ disjoint seed_e ct /\ disjoint sp_matrix ct)
    (ensures fun h0 _ h1 -> modifies (loc_buffer ct) h0 h1 /\
       as_seq h1 ct == S.crypto_kem_enc_ct_inner (as_seq h0 seed_a) (as_seq h0 seed_e) (as_seq h0 b)
       (as_seq h0 coins) (as_matrix h0 sp_matrix) (as_seq h0 d))
let crypto_kem_enc_ct_inner seed_a seed_e b coins sp_matrix d ct =
  let h0 = ST.get () in
  Spec.Frodo.KEM.expand_crypto_ciphertextbytes ();
  let c1Len = params_logq *! params_nbar *! params_n /. size 8 in
  let c2Len = params_logq *! params_nbar *! params_nbar /. size 8 in
  let c12Len = c1Len +! c2Len in

  let c1 = sub #_ #(v crypto_ciphertextbytes) #(v c1Len) ct (size 0) c1Len in
  crypto_kem_enc_ct_pack_c1 seed_a seed_e sp_matrix c1;
  let h1 = ST.get () in
  assert (LSeq.sub #_ #(v crypto_ciphertextbytes) (as_seq h1 ct) 0 (v c1Len) == as_seq h1 c1);

  let c2 = sub #_ #(v crypto_ciphertextbytes) #(v c2Len) ct c1Len c2Len in
  crypto_kem_enc_ct_pack_c2 seed_e coins b sp_matrix c2;
  let h2 = ST.get () in
  assert (LSeq.sub #_ #(v crypto_ciphertextbytes) (as_seq h2 ct) (v c1Len) (v c2Len) == as_seq h2 c2);
  assert (LSeq.sub #_ #(v crypto_ciphertextbytes) (as_seq h2 ct) 0 (v c1Len) == as_seq h1 c1);

  update_sub ct c12Len crypto_bytes d;
  let h3 = ST.get () in
  LSeq.eq_intro (LSeq.sub #_ #(v crypto_ciphertextbytes) (as_seq h3 ct) (v c1Len) (v c2Len)) (as_seq h2 c2);
  LSeq.eq_intro (LSeq.sub #_ #(v crypto_ciphertextbytes) (as_seq h3 ct) 0 (v c1Len)) (as_seq h1 c1);
  S.lemma_update_ct (as_seq h3 c1) (as_seq h3 c2) (as_seq h0 d) (as_seq h3 ct)

val crypto_kem_enc_ct:
    pk:lbytes crypto_publickeybytes
  -> g:lbytes (size 3 *! crypto_bytes)
  -> coins:lbytes (params_nbar *! params_nbar *! params_extracted_bits /. size 8)
  -> ct:lbytes crypto_ciphertextbytes
  -> Stack unit
    (requires fun h ->
      live h pk /\ live h g /\ live h coins /\ live h ct /\
      disjoint g ct /\ disjoint ct pk /\ disjoint coins ct)
    (ensures fun h0 _ h1 -> modifies (loc_buffer ct) h0 h1 /\
      as_seq h1 ct == S.crypto_kem_enc_ct (as_seq h0 pk) (as_seq h0 g) (as_seq h0 coins))
[@"c_inline"]
let crypto_kem_enc_ct pk g coins ct =
  assert (v params_nbar * v params_n % 2 = 0);
  push_frame();
  let seed_a = sub #uint8 #_ #(v bytes_seed_a) pk (size 0) bytes_seed_a in
  let b = sub #uint8 #_ #(v (params_logq *! params_n *! params_nbar /. size 8)) pk bytes_seed_a (crypto_publickeybytes -! bytes_seed_a) in
  let seed_e = sub #uint8 #_ #(v crypto_bytes) g (size 0) crypto_bytes in
  let d = sub #uint8 #_ #(v crypto_bytes) g (size 2 *! crypto_bytes) crypto_bytes in

  let sp_matrix = matrix_create params_nbar params_n in
  frodo_sample_matrix params_nbar params_n crypto_bytes seed_e (u16 4) sp_matrix;
  crypto_kem_enc_ct_inner seed_a seed_e b coins sp_matrix d ct;

  clear_matrix sp_matrix;
  pop_frame()

val crypto_kem_enc_ss:
    g:lbytes (size 3 *! crypto_bytes)
  -> ct:lbytes crypto_ciphertextbytes
  -> ss:lbytes crypto_bytes
  -> Stack unit
    (requires fun h ->
      live h g /\ live h ct /\ live h ss /\
      disjoint ct ss /\ disjoint g ct /\ disjoint g ss)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer ss) h0 h1 /\
     (let c12 = LSeq.sub #_ #(v crypto_ciphertextbytes) (as_seq h0 ct) 0 (v crypto_ciphertextbytes - v crypto_bytes) in
      let kd = LSeq.sub #_ #(3 * v crypto_bytes) (as_seq h0 g) (v crypto_bytes) (2 * v crypto_bytes) in
      as_seq h1 ss == S.update_ss c12 kd))
[@"c_inline"]
let crypto_kem_enc_ss g ct ss =
  push_frame();
  let ss_init_len = crypto_ciphertextbytes +! crypto_bytes in
  let ss_init:lbytes ss_init_len = create ss_init_len (u8 0) in
  let c12 = sub ct (size 0) (crypto_ciphertextbytes -! crypto_bytes) in
  let kd = sub #uint8 #_ #(2 * v crypto_bytes) g crypto_bytes (size 2 *! crypto_bytes) in
  let h0 = ST.get () in
  update_sub ss_init (size 0) (crypto_ciphertextbytes -! crypto_bytes) c12;
  update_sub ss_init (crypto_ciphertextbytes -! crypto_bytes) (size 2 *! crypto_bytes) kd;
  let h2 = ST.get () in
  LSeq.eq_intro (LSeq.sub #_ #(v ss_init_len) (as_seq h2 ss_init) 0 (v crypto_ciphertextbytes - v crypto_bytes)) (as_seq h0 c12);
  //assert (as_seq h2 ss_init == S.update_ss_init (as_seq h0 c12) (as_seq h0 kd) (as_seq h0 ss_init));
  cshake_frodo ss_init_len ss_init (u16 7) crypto_bytes ss;
  pop_frame()

inline_for_extraction noextract
val crypto_kem_enc_0:
    coins:lbytes (params_nbar *! params_nbar *! params_extracted_bits /. size 8)
  -> pk:lbytes crypto_publickeybytes
  -> g:lbytes (size 3 *! crypto_bytes)
  -> Stack unit
    (requires fun h ->
      live h coins /\ live h pk /\ live h g)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer g) h0 h1 /\
      as_seq h1 g == S.crypto_kem_enc_0 (as_seq h0 coins) (as_seq h0 pk))
let crypto_kem_enc_0 coins pk g =
  let bytes_mu = params_nbar *! params_nbar *! params_extracted_bits /. size 8 in
  push_frame();
  let pk_coins:lbytes (crypto_publickeybytes +! bytes_mu) = create (crypto_publickeybytes +! bytes_mu) (u8 0) in
  let h0 = ST.get () in
  update_sub pk_coins (size 0) crypto_publickeybytes pk;
  update_sub pk_coins crypto_publickeybytes bytes_mu coins;
  let h2 = ST.get () in
  LSeq.eq_intro (LSeq.sub #_ #(v crypto_publickeybytes + v bytes_mu) (as_seq h2 pk_coins) 0 (v crypto_publickeybytes)) (as_seq h0 pk);

  cshake_frodo (crypto_publickeybytes +! bytes_mu) pk_coins (u16 3) (size 3 *! crypto_bytes) g;
  pop_frame()

inline_for_extraction noextract
val crypto_kem_enc_1:
     g:lbytes (size 3 *! crypto_bytes)
  -> coins:lbytes (params_nbar *! params_nbar *! params_extracted_bits /. size 8)
  -> ct:lbytes crypto_ciphertextbytes
  -> ss:lbytes crypto_bytes
  -> pk:lbytes crypto_publickeybytes
  -> Stack unit
    (requires fun h ->
      live h g /\ live h ct /\ live h ss /\ live h pk /\ live h coins /\
      disjoint ct ss /\ disjoint ct pk /\ disjoint ss pk /\
      disjoint coins ss /\ disjoint coins ct /\ disjoint g ct /\
      disjoint g ss /\ disjoint g coins /\ disjoint g pk)
    (ensures  fun h0 _ h1 ->
      modifies (loc_union (loc_union (loc_buffer ct) (loc_buffer ss)) (loc_buffer g)) h0 h1 /\
      (let ct_s, ss_s = S.crypto_kem_enc_1 (as_seq h0 g) (as_seq h0 coins) (as_seq h0 pk) in
      as_seq h1 ct == ct_s /\ as_seq h1 ss == ss_s))
let crypto_kem_enc_1 g coins ct ss pk =
  assert_norm (2 * v crypto_bytes % 4 = 0);
  crypto_kem_enc_ct pk g coins ct;
  crypto_kem_enc_ss g ct ss;
  clear_words_u8 (size 2 *! crypto_bytes) (sub #_ #_ #(2 * v crypto_bytes) g (size 0) (size 2 *! crypto_bytes))

inline_for_extraction noextract
val crypto_kem_enc_:
    coins:lbytes (params_nbar *! params_nbar *! params_extracted_bits /. size 8)
  -> ct:lbytes crypto_ciphertextbytes
  -> ss:lbytes crypto_bytes
  -> pk:lbytes crypto_publickeybytes
  -> Stack unit
    (requires fun h ->
      live h ct /\ live h ss /\ live h pk /\ live h coins /\
      disjoint ct ss /\ disjoint ct pk /\ disjoint ss pk /\
      disjoint coins ss /\ disjoint coins ct /\ disjoint coins pk)
    (ensures  fun h0 _ h1 -> modifies (loc_union (loc_buffer ct) (loc_buffer ss)) h0 h1 /\
      (let ct_s, ss_s = S.crypto_kem_enc (as_seq h0 coins) (as_seq h0 pk) in
      as_seq h1 ct == ct_s /\ as_seq h1 ss == ss_s))
let crypto_kem_enc_ coins ct ss pk =
  push_frame();
  let bytes_mu = params_nbar *! params_nbar *! params_extracted_bits /. size 8 in
  let g:lbytes (size 3 *! crypto_bytes) = create (size 3 *! crypto_bytes) (u8 0) in
  
  crypto_kem_enc_0 coins pk g;
  crypto_kem_enc_1 g coins ct ss pk;
  pop_frame()

inline_for_extraction noextract
val crypto_kem_enc:
    ct:lbytes crypto_ciphertextbytes
  -> ss:lbytes crypto_bytes
  -> pk:lbytes crypto_publickeybytes
  -> Stack uint32
    (requires fun h ->
      live h ct /\ live h ss /\ live h pk /\
      disjoint ct ss /\ disjoint ct pk /\ disjoint ss pk)
    (ensures  fun h0 _ h1 -> modifies (loc_union (loc_buffer ct) (loc_buffer ss)) h0 h1)
let crypto_kem_enc ct ss pk =
  push_frame();
  let bytes_mu = params_nbar *! params_nbar *! params_extracted_bits /. size 8 in
  let coins = create (params_nbar *! params_nbar *! params_extracted_bits /. size 8) (u8 0) in
  randombytes_ bytes_mu coins;
  crypto_kem_enc_ coins ct ss pk;
  pop_frame();
  u32 0
