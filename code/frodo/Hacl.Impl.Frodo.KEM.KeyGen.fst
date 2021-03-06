module Hacl.Impl.Frodo.KEM.KeyGen

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Matrix
open Hacl.Impl.Frodo.Params
open Hacl.Impl.Frodo.KEM
open Hacl.Impl.Frodo.Pack
open Hacl.Impl.Frodo.Sample
open Hacl.Frodo.Random

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module M = Spec.Matrix

module FP = Spec.Frodo.Params
module S = Spec.Frodo.KEM.KeyGen

#set-options "--z3rlimit 100 --fuel 0 --ifuel 0"

inline_for_extraction noextract
val frodo_shake_r:
    a:FP.frodo_alg
  -> c:uint8
  -> seed_se:lbytes (crypto_bytes a)
  -> output_len:size_t
  -> r:lbytes output_len
  -> Stack unit
    (requires fun h ->
      live h seed_se /\ live h r /\ disjoint seed_se r)
    (ensures  fun h0 _ h1 -> modifies (loc r) h0 h1 /\
      as_seq h1 r == S.frodo_shake_r a c (as_seq h0 seed_se) (v output_len))

let frodo_shake_r a c seed_se output_len r =
  push_frame ();
  let h0 = ST.get () in
  let shake_input_seed_se = create (1ul +! crypto_bytes a) (u8 0) in
  shake_input_seed_se.(0ul) <- c;
  update_sub shake_input_seed_se 1ul (crypto_bytes a) seed_se;
  let h2 = ST.get () in
  LSeq.eq_intro (LSeq.sub (as_seq h2 shake_input_seed_se) 0 1) (LSeq.create 1 c);
  LSeq.eq_intro (LSeq.sub (as_seq h2 shake_input_seed_se) 1 (v (crypto_bytes a))) (as_seq h0 seed_se);
  LSeq.eq_intro (LSeq.concat (LSeq.create 1 c) (as_seq h0 seed_se)) (as_seq h2 shake_input_seed_se);
  frodo_shake a (1ul +! crypto_bytes a) shake_input_seed_se output_len r;
  clear_words_u8 shake_input_seed_se;
  pop_frame ()


inline_for_extraction noextract
val frodo_mul_add_as_plus_e:
    a:FP.frodo_alg
  -> gen_a:FP.frodo_gen_a{is_supported gen_a}
  -> seed_a:lbytes bytes_seed_a
  -> s_matrix:matrix_t (params_n a) params_nbar
  -> e_matrix:matrix_t (params_n a) params_nbar
  -> b_matrix:matrix_t (params_n a) params_nbar
  -> Stack unit
    (requires fun h ->
      live h seed_a /\ live h s_matrix /\ live h e_matrix /\ live h b_matrix /\
      disjoint b_matrix seed_a /\ disjoint b_matrix e_matrix /\
      disjoint b_matrix s_matrix /\ disjoint s_matrix e_matrix)
    (ensures  fun h0 _ h1 -> modifies (loc b_matrix) h0 h1 /\
      as_matrix h1 b_matrix == S.frodo_mul_add_as_plus_e a gen_a (as_seq h0 seed_a)
        (as_matrix h0 s_matrix) (as_matrix h0 e_matrix))

let frodo_mul_add_as_plus_e a gen_a seed_a s_matrix e_matrix b_matrix =
  FP.params_n_sqr a;
  push_frame();
  let a_matrix = matrix_create (params_n a) (params_n a) in
  frodo_gen_matrix gen_a (params_n a) seed_a a_matrix;
  matrix_mul_s a_matrix s_matrix b_matrix;
  matrix_add b_matrix e_matrix;
  pop_frame()


inline_for_extraction noextract
val frodo_mul_add_as_plus_e_pack:
    a:FP.frodo_alg
  -> gen_a:FP.frodo_gen_a{is_supported gen_a}
  -> seed_a:lbytes bytes_seed_a
  -> s_matrix:matrix_t (params_n a) params_nbar
  -> e_matrix:matrix_t (params_n a) params_nbar
  -> b:lbytes (publicmatrixbytes_len a)
  -> Stack unit
    (requires fun h ->
      live h seed_a /\ live h b /\
      live h s_matrix /\ live h e_matrix /\
      disjoint seed_a b /\ disjoint b s_matrix /\
      disjoint b e_matrix /\ disjoint s_matrix e_matrix)
    (ensures  fun h0 _ h1 -> modifies (loc b) h0 h1 /\
      as_seq h1 b == S.frodo_mul_add_as_plus_e_pack a gen_a (as_seq h0 seed_a)
        (as_matrix h0 s_matrix) (as_matrix h0 e_matrix))

let frodo_mul_add_as_plus_e_pack a gen_a seed_a s_matrix e_matrix b =
  push_frame ();
  let b_matrix = matrix_create (params_n a) params_nbar in
  frodo_mul_add_as_plus_e a gen_a seed_a s_matrix e_matrix b_matrix;
  frodo_pack (params_logq a) b_matrix b;
  pop_frame ()


inline_for_extraction noextract
val get_s_e_matrices:
    a:FP.frodo_alg
  -> seed_se:lbytes (crypto_bytes a)
  -> s_matrix:matrix_t (params_n a) params_nbar
  -> e_matrix:matrix_t (params_n a) params_nbar
  -> Stack unit
    (requires fun h ->
      live h seed_se /\ live h s_matrix /\ live h e_matrix /\
      disjoint seed_se s_matrix /\ disjoint seed_se e_matrix /\
      disjoint s_matrix e_matrix)
    (ensures  fun h0 _ h1 -> modifies (loc s_matrix |+| loc e_matrix) h0 h1 /\
      (as_matrix h1 s_matrix, as_matrix h1 e_matrix) == S.get_s_e_matrices a (as_seq h0 seed_se))

let get_s_e_matrices a seed_se s_matrix e_matrix =
  push_frame ();
  [@inline_let] let s_bytes_len = secretmatrixbytes_len a in
  let r = create (2ul *! s_bytes_len) (u8 0) in
  frodo_shake_r a (u8 0x5f) seed_se (2ul *! s_bytes_len) r;
  frodo_sample_matrix a (params_n a) params_nbar (sub r 0ul s_bytes_len) s_matrix;
  frodo_sample_matrix a (params_n a) params_nbar (sub r s_bytes_len s_bytes_len) e_matrix;
  pop_frame ()


inline_for_extraction noextract
val clear_matrix2:
    a:FP.frodo_alg
  -> s_matrix:matrix_t (params_n a) params_nbar
  -> e_matrix:matrix_t (params_n a) params_nbar
  -> Stack unit
    (requires fun h ->
      live h s_matrix /\ live h e_matrix /\
      disjoint s_matrix e_matrix)
    (ensures  fun h0 _ h1 ->
      modifies (loc s_matrix |+| loc e_matrix) h0 h1)

let clear_matrix2 a s_matrix e_matrix =
  clear_matrix s_matrix;
  clear_matrix e_matrix


inline_for_extraction noextract
val frodo_mul_add_as_plus_e_pack_shake:
    a:FP.frodo_alg
  -> gen_a:FP.frodo_gen_a{is_supported gen_a}
  -> seed_a:lbytes bytes_seed_a
  -> seed_se:lbytes (crypto_bytes a)
  -> b:lbytes (publicmatrixbytes_len a)
  -> s:lbytes (secretmatrixbytes_len a)
  -> Stack unit
    (requires fun h ->
      live h seed_a /\ live h seed_se /\ live h s /\ live h b /\
      disjoint b s /\ disjoint seed_a b /\ disjoint seed_a s /\
      disjoint seed_se b /\ disjoint seed_se s)
    (ensures  fun h0 _ h1 -> modifies (loc s |+| loc b) h0 h1 /\
      (as_seq h1 b, as_seq h1 s) ==
      S.frodo_mul_add_as_plus_e_pack_shake a gen_a (as_seq h0 seed_a) (as_seq h0 seed_se))

let frodo_mul_add_as_plus_e_pack_shake a gen_a seed_a seed_se b s =
  push_frame ();
  let s_matrix = matrix_create (params_n a) params_nbar in
  let e_matrix = matrix_create (params_n a) params_nbar in
  get_s_e_matrices a seed_se s_matrix e_matrix;

  frodo_mul_add_as_plus_e_pack a gen_a seed_a s_matrix e_matrix b;
  matrix_to_lbytes s_matrix s;

  clear_matrix2 a s_matrix e_matrix;
  pop_frame ()


inline_for_extraction noextract
val crypto_kem_sk1:
    a:FP.frodo_alg
  -> s:lbytes (crypto_bytes a)
  -> pk:lbytes (crypto_publickeybytes a)
  -> sk:lbytes (crypto_secretkeybytes a -! bytes_pkhash a)
  -> Stack unit
    (requires fun h ->
      live h pk /\ live h sk /\ live h s /\
      disjoint pk sk /\ disjoint sk s)
    (ensures  fun h0 _ h1 -> modifies (loc sk) h0 h1 /\
     (let s_bytes = LSeq.sub (as_seq h0 sk) (v (crypto_bytes a) + v (crypto_publickeybytes a)) (v (secretmatrixbytes_len a)) in
      as_seq h1 sk == LSeq.concat (LSeq.concat (as_seq h0 s) (as_seq h0 pk)) s_bytes))

let crypto_kem_sk1 a s pk sk =
  let h1 = ST.get () in
  FP.expand_crypto_secretkeybytes a;
  let s_pk_len = crypto_bytes a +! crypto_publickeybytes a in
  [@inline_let] let sm_len = secretmatrixbytes_len a in
  let slen1 = crypto_secretkeybytes a -! bytes_pkhash a in
  let s_bytes = sub sk s_pk_len sm_len in

  update_sub sk 0ul (crypto_bytes a) s;
  let h2 = ST.get () in
  LSeq.eq_intro (LSeq.sub (as_seq h2 sk) (v s_pk_len) (v sm_len)) (as_seq h1 s_bytes);

  update_sub sk (crypto_bytes a) (crypto_publickeybytes a) pk;
  let h3 = ST.get () in
  LSeq.eq_intro (LSeq.sub (as_seq h3 sk) 0 (v (crypto_bytes a))) (as_seq h1 s);
  LSeq.eq_intro (LSeq.sub (as_seq h3 sk) (v (crypto_bytes a)) (v (crypto_publickeybytes a))) (as_seq h1 pk);
  LSeq.eq_intro (LSeq.sub (as_seq h3 sk) (v s_pk_len) (v sm_len)) (as_seq h1 s_bytes);
  LSeq.lemma_concat3
    (v (crypto_bytes a)) (as_seq h1 s)
    (v (crypto_publickeybytes a)) (as_seq h1 pk)
    (v sm_len) (as_seq h1 s_bytes)
    (as_seq h3 sk)


inline_for_extraction noextract
val crypto_kem_sk:
    a:FP.frodo_alg
  -> s:lbytes (crypto_bytes a)
  -> pk:lbytes (crypto_publickeybytes a)
  -> sk:lbytes (crypto_secretkeybytes a)
  -> Stack unit
    (requires fun h ->
      live h pk /\ live h sk /\ live h s /\
      disjoint pk sk /\ disjoint sk s)
    (ensures  fun h0 _ h1 -> modifies (loc sk) h0 h1 /\
     (let s_bytes = LSeq.sub (as_seq h0 sk) (v (crypto_bytes a) + v (crypto_publickeybytes a)) (v (secretmatrixbytes_len a)) in
      as_seq h1 sk == S.crypto_kem_sk a (as_seq h0 s) (as_seq h0 pk) s_bytes))

let crypto_kem_sk a s pk sk =
  FP.expand_crypto_secretkeybytes a;
  let slen1 = crypto_secretkeybytes a -! bytes_pkhash a in
  let sk_p = sub sk 0ul slen1 in
  crypto_kem_sk1 a s pk sk_p;

  let h0 = ST.get () in
  update_sub_f h0 sk slen1 (bytes_pkhash a)
  (fun h -> FP.frodo_shake a (v (crypto_publickeybytes a)) (as_seq h0 pk) (v (bytes_pkhash a)))
  (fun _ -> frodo_shake a (crypto_publickeybytes a) pk (bytes_pkhash a) (sub sk slen1 (bytes_pkhash a)));
  let h1 = ST.get () in
  LSeq.eq_intro (LSeq.sub (as_seq h0 sk) 0 (v slen1)) (LSeq.sub (as_seq h1 sk) 0 (v slen1));
  LSeq.lemma_concat2
    (v slen1) (LSeq.sub (as_seq h0 sk) 0 (v slen1))
    (v (bytes_pkhash a)) (LSeq.sub (as_seq h1 sk) (v slen1) (v (bytes_pkhash a))) (as_seq h1 sk)


inline_for_extraction noextract
val crypto_kem_keypair_:
    a:FP.frodo_alg
  -> gen_a:FP.frodo_gen_a{is_supported gen_a}
  -> coins:lbytes (size 2 *! crypto_bytes a +! bytes_seed_a)
  -> pk:lbytes (crypto_publickeybytes a)
  -> sk:lbytes (crypto_secretkeybytes a)
  -> Stack unit
    (requires fun h ->
      live h pk /\ live h sk /\ live h coins /\
      disjoint pk sk /\ disjoint coins sk /\ disjoint coins pk)
    (ensures  fun h0 _ h1 -> modifies (loc pk |+| loc sk) h0 h1 /\
      (as_seq h1 pk, as_seq h1 sk) == S.crypto_kem_keypair_ a gen_a (as_seq h0 coins))

let crypto_kem_keypair_ a gen_a coins pk sk =
  FP.expand_crypto_secretkeybytes a;
  FP.expand_crypto_secretkeybytes a;
  let h0 = ST.get () in
  let s = sub coins 0ul (crypto_bytes a) in
  let seed_se = sub coins (crypto_bytes a) (crypto_bytes a) in
  let z = sub coins (2ul *! crypto_bytes a) bytes_seed_a in

  let seed_a = sub pk 0ul bytes_seed_a in
  frodo_shake a bytes_seed_a z bytes_seed_a seed_a;

  let b_bytes = sub pk bytes_seed_a (publicmatrixbytes_len a) in
  let s_bytes = sub sk (crypto_bytes a +! crypto_publickeybytes a) (secretmatrixbytes_len a) in
  frodo_mul_add_as_plus_e_pack_shake a gen_a seed_a seed_se b_bytes s_bytes;
  let h1 = ST.get () in
  LSeq.lemma_concat2 (v bytes_seed_a) (as_seq h1 seed_a) (v (publicmatrixbytes_len a)) (as_seq h1 b_bytes) (as_seq h1 pk);

  crypto_kem_sk a s pk sk


inline_for_extraction noextract
val crypto_kem_keypair:
    a:FP.frodo_alg
  -> gen_a:FP.frodo_gen_a{is_supported gen_a}
  -> pk:lbytes (crypto_publickeybytes a)
  -> sk:lbytes (crypto_secretkeybytes a)
  -> Stack uint32
    (requires fun h ->
      live h pk /\ live h sk /\
      disjoint state pk /\ disjoint state sk /\ disjoint pk sk)
    (ensures  fun h0 r h1 -> modifies (loc state |+| (loc pk |+| loc sk)) h0 h1 /\
      (as_seq h1 pk, as_seq h1 sk) == S.crypto_kem_keypair a gen_a (as_seq h0 state))

let crypto_kem_keypair a gen_a pk sk =
  recall state;
  push_frame();
  let coins = create (size 2 *! crypto_bytes a +! bytes_seed_a) (u8 0) in
  randombytes_ (size 2 *! crypto_bytes a +! bytes_seed_a) coins;
  crypto_kem_keypair_ a gen_a coins pk sk;
  clear_words_u8 coins;
  pop_frame();
  u32 0
