module Hacl.Impl.Frodo.KEM.KeyGen

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
module S = Spec.Frodo.KEM.KeyGen
module M = Spec.Matrix
module LSeq = Lib.Sequence

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val frodo_mul_add_as_plus_e:
    seed_a:lbytes bytes_seed_a
  -> s_matrix:matrix_t params_n params_nbar
  -> e_matrix:matrix_t params_n params_nbar
  -> b_matrix:matrix_t params_n params_nbar
  -> Stack unit
    (requires fun h ->
      live h seed_a /\ live h s_matrix /\ live h e_matrix /\ live h b_matrix /\
      disjoint b_matrix seed_a /\ disjoint s_matrix b_matrix /\ disjoint b_matrix e_matrix)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer b_matrix) h0 h1 /\
      (let a_matrix = Spec.Frodo.Params.frodo_gen_matrix (v params_n) (v bytes_seed_a) (as_seq h0 seed_a) in
      as_matrix h1 b_matrix == M.add (M.mul_s a_matrix (as_matrix h0 s_matrix)) (as_matrix h0 e_matrix)))
[@"c_inline"]
let frodo_mul_add_as_plus_e seed_a s_matrix e_matrix b_matrix =
  assert_norm (0 < v params_n /\ 2 * v params_n < max_size_t /\ 256 + v params_n < maxint U16 /\ v params_n * v params_n < max_size_t);
  push_frame();
  let a_matrix = matrix_create params_n params_n in
  frodo_gen_matrix params_n bytes_seed_a seed_a a_matrix;
  matrix_mul_s a_matrix s_matrix b_matrix;
  matrix_add b_matrix e_matrix;
  pop_frame()

inline_for_extraction noextract
val frodo_mul_add_as_plus_e_pack_inner:
    seed_a:lbytes bytes_seed_a
  -> s_matrix:matrix_t params_n params_nbar
  -> e_matrix:matrix_t params_n params_nbar
  -> b:lbytes (params_logq *! params_n *! params_nbar /. size 8)
  -> Stack unit
    (requires fun h ->
      live h seed_a /\ live h s_matrix /\ live h e_matrix /\
      live h b /\ disjoint seed_a b)
    (ensures fun h0 r h1 -> modifies (loc_buffer b) h0 h1 /\
      (let a_matrix = Spec.Frodo.Params.frodo_gen_matrix (v params_n) (v bytes_seed_a) (as_seq h0 seed_a) in
      let b_matrix = M.add (M.mul_s a_matrix (as_matrix h0 s_matrix)) (as_matrix h0 e_matrix) in
      as_seq h1 b == Spec.Frodo.Pack.frodo_pack b_matrix (v params_logq)))
let frodo_mul_add_as_plus_e_pack_inner seed_a s_matrix e_matrix b =
  push_frame();
  let b_matrix = matrix_create params_n params_nbar in
  frodo_mul_add_as_plus_e seed_a s_matrix e_matrix b_matrix;
  assert (v params_nbar % 8 = 0);
  frodo_pack b_matrix params_logq b;
  pop_frame()

inline_for_extraction noextract
val clear_matrix_se:
    s:matrix_t params_n params_nbar
  -> e:matrix_t params_n params_nbar
  -> Stack unit
    (requires fun h -> live h s /\ live h e /\ disjoint s e)
    (ensures  fun h0 _ h1 -> modifies (loc_union (loc_buffer s) (loc_buffer e)) h0 h1)
let clear_matrix_se s e =
  assert_norm (v params_n * v params_nbar % 2 = 0);
  clear_matrix s;
  clear_matrix e

val frodo_mul_add_as_plus_e_pack:
    seed_a:lbytes bytes_seed_a
  -> seed_e:lbytes crypto_bytes
  -> b:lbytes (params_logq *! params_n *! params_nbar /. size 8)
  -> s:lbytes (size 2 *! params_n *! params_nbar)
  -> Stack unit
    (requires fun h ->
      live h seed_a /\ live h seed_e /\ live h s /\ live h b /\
      disjoint b s /\ disjoint seed_a b /\ disjoint seed_e b /\
      disjoint seed_a s /\ disjoint seed_e s)
    (ensures  fun h0 _ h1 ->
      modifies (loc_union (loc_buffer s) (loc_buffer b)) h0 h1 /\
      (let b_sp, s_bytes_sp = S.frodo_mul_add_as_plus_e_pack (as_seq h0 seed_a) (as_seq h0 seed_e) in
      as_seq h1 b == b_sp /\
      as_seq h1 s == s_bytes_sp))
[@"c_inline"]
let frodo_mul_add_as_plus_e_pack seed_a seed_e b s =
  push_frame();
  let s_matrix = matrix_create params_n params_nbar in
  let e_matrix = matrix_create params_n params_nbar in
  frodo_sample_matrix params_n params_nbar crypto_bytes seed_e (u16 1) s_matrix;
  frodo_sample_matrix params_n params_nbar crypto_bytes seed_e (u16 2) e_matrix;
  frodo_mul_add_as_plus_e_pack_inner seed_a s_matrix e_matrix b;
  matrix_to_lbytes s_matrix s;
  clear_matrix_se s_matrix e_matrix;
  pop_frame()

inline_for_extraction noextract
val crypto_kem_keypair_:
    coins:lbytes (size 2 *! crypto_bytes +! bytes_seed_a)
  -> pk:lbytes crypto_publickeybytes
  -> sk:lbytes crypto_secretkeybytes
  -> Stack unit
    (requires fun h ->
      live h pk /\ live h sk /\ live h coins /\
      disjoint pk sk /\ disjoint coins sk /\ disjoint coins pk)
    (ensures  fun h0 _ h1 ->
      modifies (loc_union (loc_buffer pk) (loc_buffer sk)) h0 h1 /\
      (let pk_s, sk_s = S.crypto_kem_keypair (as_seq h0 coins) in
      as_seq h1 pk == pk_s /\ as_seq h1 sk == sk_s))
let crypto_kem_keypair_ coins pk sk =
  let h0 = ST.get () in
  let s:lbytes crypto_bytes = sub coins (size 0) crypto_bytes in
  let seed_e = sub coins crypto_bytes crypto_bytes in
  let z = sub coins (size 2 *! crypto_bytes) bytes_seed_a in

  let seed_a = sub pk (size 0) bytes_seed_a in
  cshake_frodo bytes_seed_a z (u16 0) bytes_seed_a seed_a;

  let b:lbytes (params_logq *! params_n *! params_nbar /. size 8) = sub pk bytes_seed_a (crypto_publickeybytes -! bytes_seed_a) in
  let s_bytes = sub sk (crypto_bytes +! crypto_publickeybytes) (size 2 *! params_n *! params_nbar) in
  frodo_mul_add_as_plus_e_pack seed_a seed_e b s_bytes;
  let h1 = ST.get () in
  S.lemma_updade_pk (as_seq h1 seed_a) (as_seq h1 b) (as_seq h1 pk);

  assert (LSeq.sub #_ #(v crypto_secretkeybytes) (as_seq h1 sk)
    (v crypto_bytes + v crypto_publickeybytes) (2 * v params_n * v params_nbar) == as_seq h1 s_bytes);
  update_sub sk (size 0) crypto_bytes s;
  let h2 = ST.get () in
  LSeq.eq_intro (LSeq.sub #_ #(v crypto_secretkeybytes) (as_seq h2 sk) (v crypto_bytes + v crypto_publickeybytes) (2 * v params_n * v params_nbar)) (as_seq h1 s_bytes);
  update_sub sk crypto_bytes crypto_publickeybytes pk;
  let h3 = ST.get () in
  LSeq.eq_intro (LSeq.sub #_ #(v crypto_secretkeybytes) (as_seq h3 sk) 0 (v crypto_bytes)) (as_seq h1 s);
  LSeq.eq_intro (LSeq.sub #_ #(v crypto_secretkeybytes) (as_seq h3 sk) (v crypto_bytes + v crypto_publickeybytes) (2 * v params_n * v params_nbar)) (as_seq h1 s_bytes);
  S.lemma_updade_sk (as_seq h1 s) (as_seq h1 pk) (as_seq h1 s_bytes) (as_seq h3 sk)

inline_for_extraction noextract
val crypto_kem_keypair:
    pk:lbytes crypto_publickeybytes
  -> sk:lbytes crypto_secretkeybytes
  -> Stack uint32
    (requires fun h -> live h pk /\ live h sk /\ disjoint pk sk)
    (ensures  fun h0 r h1 -> live h1 pk /\ live h1 sk /\
      modifies (loc_union (loc_buffer pk) (loc_buffer sk)) h0 h1)
let crypto_kem_keypair pk sk =
  push_frame();
  let coins = create (size 2 *! crypto_bytes +! bytes_seed_a) (u8 0) in
  randombytes_ (size 2 *! crypto_bytes +! bytes_seed_a) coins;
  crypto_kem_keypair_ coins pk sk;
  pop_frame();
  u32 0
