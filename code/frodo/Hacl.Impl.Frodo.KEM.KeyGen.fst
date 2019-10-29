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
module S = Spec.Frodo.KEM.KeyGen
module M = Spec.Matrix
module LSeq = Lib.Sequence

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

inline_for_extraction noextract
val frodo_mul_add_as_plus_e:
    seed_a:lbytes bytes_seed_a
  -> seed_e:lbytes crypto_bytes
  -> s_matrix:matrix_t params_n params_nbar
  -> b_matrix:matrix_t params_n params_nbar
  -> Stack unit
    (requires fun h ->
      live h seed_a /\ live h seed_e /\ live h s_matrix /\ live h b_matrix /\
      disjoint b_matrix seed_a /\ disjoint b_matrix seed_e /\ disjoint b_matrix s_matrix)
    (ensures  fun h0 _ h1 -> modifies1 b_matrix h0 h1 /\
     (let a_matrix = Spec.Frodo.Params.frodo_gen_matrix (v params_n) (v bytes_seed_a) (as_seq h0 seed_a) in
      let e_matrix = Spec.Frodo.Sample.frodo_sample_matrix (v params_n) (v params_nbar)
	(v crypto_bytes) (as_seq h0 seed_e) (u16 2) in
      as_matrix h1 b_matrix == M.add (M.mul_s a_matrix (as_matrix h0 s_matrix)) e_matrix))
let frodo_mul_add_as_plus_e seed_a seed_e s_matrix b_matrix =
  assert_norm (v params_n * v params_nbar % 2 = 0);
  push_frame();
  let a_matrix = matrix_create params_n params_n in
  let e_matrix = matrix_create params_n params_nbar in
  frodo_gen_matrix params_n bytes_seed_a seed_a a_matrix;
  frodo_sample_matrix params_n params_nbar crypto_bytes seed_e (u16 2) e_matrix;
  matrix_mul_s a_matrix s_matrix b_matrix;
  matrix_add b_matrix e_matrix;
  clear_matrix e_matrix;
  pop_frame()

inline_for_extraction noextract
val frodo_mul_add_as_plus_e_pack0:
    seed_a:lbytes bytes_seed_a
  -> seed_e:lbytes crypto_bytes
  -> s_matrix:matrix_t params_n params_nbar
  -> b:lbytes (params_logq *! params_n *! params_nbar /. size 8)
  -> Stack unit
    (requires fun h ->
      live h seed_a /\ live h seed_e /\ live h s_matrix /\
      live h b /\ disjoint seed_a b)
    (ensures fun h0 r h1 -> modifies1 b h0 h1 /\
     (let a_matrix = Spec.Frodo.Params.frodo_gen_matrix (v params_n) (v bytes_seed_a) (as_seq h0 seed_a) in
      let e_matrix = Spec.Frodo.Sample.frodo_sample_matrix (v params_n) (v params_nbar)
	(v crypto_bytes) (as_seq h0 seed_e) (u16 2) in
      let b_matrix = M.add (M.mul_s a_matrix (as_matrix h0 s_matrix)) e_matrix in
      as_seq h1 b == Spec.Frodo.Pack.frodo_pack (v params_logq) b_matrix))
let frodo_mul_add_as_plus_e_pack0 seed_a seed_e s_matrix b =
  push_frame();
  let b_matrix = matrix_create params_n params_nbar in
  frodo_mul_add_as_plus_e seed_a seed_e s_matrix b_matrix;
  frodo_pack params_logq b_matrix b;
  pop_frame()

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
      modifies2 s b h0 h1 /\
      (as_seq h1 b, as_seq h1 s) == S.frodo_mul_add_as_plus_e_pack (as_seq h0 seed_a) (as_seq h0 seed_e))
[@"c_inline"]
let frodo_mul_add_as_plus_e_pack seed_a seed_e b s =
  assert_norm (v params_n * v params_nbar % 2 = 0);
  push_frame();
  let s_matrix = matrix_create params_n params_nbar in
  frodo_sample_matrix params_n params_nbar crypto_bytes seed_e (u16 1) s_matrix;
  matrix_to_lbytes s_matrix s;
  frodo_mul_add_as_plus_e_pack0 seed_a seed_e s_matrix b;
  clear_matrix s_matrix;
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
      modifies2 pk sk h0 h1 /\
      (as_seq h1 pk, as_seq h1 sk) == S.crypto_kem_keypair_ (as_seq h0 coins))
let crypto_kem_keypair_ coins pk sk =
  let h0 = ST.get () in
  let s = sub coins (size 0) crypto_bytes in
  let seed_e = sub coins crypto_bytes crypto_bytes in
  let z = sub coins (size 2 *! crypto_bytes) bytes_seed_a in
  let seed_a = sub pk (size 0) bytes_seed_a in
  cshake_frodo bytes_seed_a z (u16 0) bytes_seed_a seed_a;
  let b = sub pk bytes_seed_a (crypto_publickeybytes -! bytes_seed_a) in
  let s_bytes = sub sk (crypto_bytes +! crypto_publickeybytes) (size 2 *! params_n *! params_nbar) in
  frodo_mul_add_as_plus_e_pack seed_a seed_e b s_bytes;
  let h1 = ST.get () in
  LSeq.lemma_concat2 (v bytes_seed_a) (as_seq h1 seed_a) (v params_logq * v params_n * v params_nbar / 8) (as_seq h1 b) (as_seq h1 pk);

  assert (LSeq.sub #_ #(v crypto_secretkeybytes) (as_seq h1 sk)
    (v crypto_bytes + v crypto_publickeybytes) (2 * v params_n * v params_nbar) == as_seq h1 s_bytes);
  update_sub sk (size 0) crypto_bytes s;
  let h2 = ST.get () in
  LSeq.eq_intro (LSeq.sub (as_seq h2 sk) (v crypto_bytes + v crypto_publickeybytes) (2 * v params_n * v params_nbar)) (as_seq h1 s_bytes);
  update_sub sk crypto_bytes crypto_publickeybytes pk;
  let h3 = ST.get () in
  LSeq.eq_intro (LSeq.sub (as_seq h3 sk) 0 (v crypto_bytes)) (as_seq h1 s);
  LSeq.eq_intro (LSeq.sub (as_seq h3 sk) (v crypto_bytes + v crypto_publickeybytes) (2 * v params_n * v params_nbar)) (as_seq h1 s_bytes);
  LSeq.lemma_concat3 (v crypto_bytes) (as_seq h1 s) (v crypto_publickeybytes) (as_seq h1 pk) (2 * v params_n * v params_nbar) (as_seq h1 s_bytes) (as_seq h3 sk)

inline_for_extraction noextract
val crypto_kem_keypair:
    pk:lbytes crypto_publickeybytes
  -> sk:lbytes crypto_secretkeybytes
  -> Stack uint32
    (requires fun h ->
      disjoint state pk /\ disjoint state sk /\ disjoint pk sk /\
      live h pk /\ live h sk)
    (ensures  fun h0 r h1 ->
      modifies (loc state |+| (loc pk |+| loc sk)) h0 h1 /\
      (as_seq h1 pk, as_seq h1 sk) == S.crypto_kem_keypair (as_seq h0 state))
let crypto_kem_keypair pk sk =
  recall state;
  push_frame();
  let coins = create (size 2 *! crypto_bytes +! bytes_seed_a) (u8 0) in
  randombytes_ (size 2 *! crypto_bytes +! bytes_seed_a) coins;
  crypto_kem_keypair_ coins pk sk;
  pop_frame();
  u32 0
