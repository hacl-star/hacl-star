module Hacl.Spec.SHA2.Equiv

open FStar.Mul
open Lib.IntTypes
open Lib.NTuple
open Lib.Sequence
open Lib.IntVector
open Lib.LoopCombinators

open Hacl.Spec.SHA2.Vec
open Spec.Hash.Definitions
module Constants = Spec.SHA2.Constants
module Spec = Hacl.Spec.SHA2
module LSeq = Lib.Sequence

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

val _Ch_lemma: #a:sha2_alg -> #m:m_spec -> x:element_t a m -> y:element_t a m -> z:element_t a m ->
  Lemma (forall (l:nat{l < lanes a m}).{:pattern (vec_v (_Ch x y z)).[l]}
    (vec_v (_Ch #a #m x y z)).[l] == Spec._Ch a (vec_v x).[l] (vec_v y).[l] (vec_v z).[l])
  [SMTPat (_Ch x y z)]

let _Ch_lemma #a #m x y z = ()


val _Maj_lemma: #a:sha2_alg -> #m:m_spec -> x:element_t a m -> y:element_t a m -> z:element_t a m ->
  Lemma (forall (l:nat{l < lanes a m}).{:pattern (vec_v (_Maj x y z)).[l]}
    (vec_v (_Maj #a #m x y z)).[l] == Spec._Maj a (vec_v x).[l] (vec_v y).[l] (vec_v z).[l])
  [SMTPat (_Maj x y z)]

let _Maj_lemma #a #m x y z = ()


val _Sigma0_lemma: #a:sha2_alg -> #m:m_spec -> x:element_t a m ->
  Lemma (forall (l:nat{l < lanes a m}).{:pattern (vec_v (_Sigma0 x)).[l]}
    (vec_v (_Sigma0 #a #m x)).[l] == Spec._Sigma0 a (vec_v x).[l])
  [SMTPat (_Sigma0 x)]

let _Sigma0_lemma #a #m x = ()


val _Sigma1_lemma: #a:sha2_alg -> #m:m_spec -> x:element_t a m ->
  Lemma (forall (l:nat{l < lanes a m}).{:pattern (vec_v (_Sigma1 x)).[l]}
    (vec_v (_Sigma1 #a #m x)).[l] == Spec._Sigma1 a (vec_v x).[l])
  [SMTPat (_Sigma1 x)]

let _Sigma1_lemma #a #m x = ()


val _sigma0_lemma: #a:sha2_alg -> #m:m_spec -> x:element_t a m ->
  Lemma (forall (l:nat{l < lanes a m}).{:pattern (vec_v (_sigma0 x)).[l]}
    (vec_v (_sigma0 #a #m x)).[l] == Spec._sigma0 a (vec_v x).[l])
  [SMTPat (_sigma0 x)]

let _sigma0_lemma #a #m x = ()


val _sigma1_lemma: #a:sha2_alg -> #m:m_spec -> x:element_t a m ->
  Lemma (forall (l:nat{l < lanes a m}).{:pattern (vec_v (_sigma1 x)).[l]}
    (vec_v (_sigma1 #a #m x)).[l] == Spec._sigma1 a (vec_v x).[l])
  [SMTPat (_sigma1 x)]

let _sigma1_lemma #a #m x = ()


val seq_of_list_is_create8: #a:Type -> x0:a -> x1:a -> x2:a -> x3:a -> x4:a -> x5:a -> x6:a -> x7:a ->
  Lemma (create8 x0 x1 x2 x3 x4 x5 x6 x7 == Seq.seq_of_list [x0; x1; x2; x3; x4; x5; x6; x7])

let seq_of_list_is_create8 #a x0 x1 x2 x3 x4 x5 x6 x7 =
  let rp = Seq.seq_of_list [x0; x1; x2; x3; x4; x5; x6; x7] in
  assert_norm (length rp == 8);
  let lp = create8 x0 x1 x2 x3 x4 x5 x6 x7 in

  let aux (i:nat{i < 8}) : Lemma (Seq.index lp i == Seq.index rp i) =
    assert_norm (Seq.index lp i == Seq.index rp i) in

  Classical.forall_intro aux;
  eq_intro rp lp


val shuffle_core_pre_create8: a:sha2_alg -> k_t:word a -> ws_t:word a -> hash:words_state a -> words_state a
let shuffle_core_pre_create8 a k_t ws_t hash =
  let a0 = Seq.index hash 0 in
  let b0 = Seq.index hash 1 in
  let c0 = Seq.index hash 2 in
  let d0 = Seq.index hash 3 in
  let e0 = Seq.index hash 4 in
  let f0 = Seq.index hash 5 in
  let g0 = Seq.index hash 6 in
  let h0 = Seq.index hash 7 in

  let t1 = h0 +. (Spec._Sigma1 a e0) +. (Spec._Ch a e0 f0 g0) +. k_t +. ws_t in
  let t2 = (Spec._Sigma0 a a0) +. (Spec._Maj a a0 b0 c0) in
  create8 (t1 +. t2) a0 b0 c0 (d0 +. t1) e0 f0 g0


val shuffle_core_pre_create8_lemma: a:sha2_alg -> k_t:word a -> ws_t:word a -> hash:words_state a ->
  Lemma (Spec.shuffle_core_pre a k_t ws_t hash == shuffle_core_pre_create8 a k_t ws_t hash)
let shuffle_core_pre_create8_lemma a k_t ws_t hash =
  let a0 = Seq.index hash 0 in
  let b0 = Seq.index hash 1 in
  let c0 = Seq.index hash 2 in
  let d0 = Seq.index hash 3 in
  let e0 = Seq.index hash 4 in
  let f0 = Seq.index hash 5 in
  let g0 = Seq.index hash 6 in
  let h0 = Seq.index hash 7 in

  let t1 = h0 +. (Spec._Sigma1 a e0) +. (Spec._Ch a e0 f0 g0) +. k_t +. ws_t in
  let t2 = (Spec._Sigma0 a a0) +. (Spec._Maj a a0 b0 c0) in
  seq_of_list_is_create8 (t1 +. t2) a0 b0 c0 (d0 +. t1) e0 f0 g0



noextract
let state_spec_v_l (#a:sha2_alg) (#m:m_spec) (st:state_spec a m) (l:nat{l < lanes a m}) : words_state a =
  create8
    (vec_v st.[0]).[l] (vec_v st.[1]).[l] (vec_v st.[2]).[l] (vec_v st.[3]).[l]
    (vec_v st.[4]).[l] (vec_v st.[5]).[l] (vec_v st.[6]).[l] (vec_v st.[7]).[l]

noextract
let ws_spec_v_l (#a:sha2_alg) (#m:m_spec) (st:ws_spec a m) (l:nat{l < lanes a m}) : lseq (word a) 16 =
  create16
    (vec_v st.[0]).[l] (vec_v st.[1]).[l] (vec_v st.[2]).[l] (vec_v st.[3]).[l]
    (vec_v st.[4]).[l] (vec_v st.[5]).[l] (vec_v st.[6]).[l] (vec_v st.[7]).[l]
    (vec_v st.[8]).[l] (vec_v st.[9]).[l] (vec_v st.[10]).[l] (vec_v st.[11]).[l]
    (vec_v st.[12]).[l] (vec_v st.[13]).[l] (vec_v st.[14]).[l] (vec_v st.[15]).[l]


val shuffle_core_spec_lemma_l:
    #a:sha2_alg
  -> #m:m_spec
  -> k_t:word a
  -> ws_t:element_t a m
  -> st:state_spec a m
  -> l:nat{l < lanes a m} ->
  Lemma
   (state_spec_v_l (shuffle_core_spec k_t ws_t st) l ==
    Spec.shuffle_core_pre a k_t (vec_v ws_t).[l] (state_spec_v_l st l))

let shuffle_core_spec_lemma_l #a #m k_t ws_t st l =
  eq_intro #(word a) #(state_word_length a)
    (state_spec_v_l (shuffle_core_spec k_t ws_t st) l)
    (shuffle_core_pre_create8 a k_t (vec_v ws_t).[l] (state_spec_v_l st l));
  shuffle_core_pre_create8_lemma a k_t (vec_v ws_t).[l] (state_spec_v_l st l)


val ws_next_inner_lemma_l:
    #a:sha2_alg
  -> #m:m_spec
  -> i:size_nat{i < 16}
  -> ws:ws_spec a m
  -> l:nat{l < lanes a m} ->
  Lemma ((ws_spec_v (ws_next_inner i ws)).[l] == Spec.ws_next_inner a i (ws_spec_v ws).[l])

let ws_next_inner_lemma_l #a #m i ws = admit()


val ws_next_lemma_l:
    #a:sha2_alg
  -> #m:m_spec
  -> ws:ws_spec a m
  -> l:nat{l < lanes a m} ->
  Lemma ((ws_spec_v (ws_next #a #m ws)).[l] == Spec.ws_next a (ws_spec_v ws).[l])

let ws_next_lemma_l #a #m ws l = admit()


val shuffle_inner_lemma_l:
    #a:sha2_alg
  -> #m:m_spec
  -> ws:ws_spec a m
  -> i:size_nat{i < Spec.num_rounds16 a}
  -> j:size_nat{j < 16}
  -> st:state_spec a m
  -> l:nat{l < lanes a m} ->
  Lemma ((state_spec_v (shuffle_inner ws i j st)).[l] == Spec.shuffle_inner a (ws_spec_v ws).[l] i j (state_spec_v st).[l])

let shuffle_inner_lemma_l #a #m ws i j st l = admit()


val shuffle_inner_loop_lemma_l:
    #a:sha2_alg
  -> #m:m_spec
  -> i:size_nat{i < Spec.num_rounds16 a}
  -> ws_st:tuple2 (ws_spec a m) (state_spec a m)
  -> l:nat{l < lanes a m} ->
  Lemma
  (let (ws1, st1) = shuffle_inner_loop i ws_st in
   let (ws0, st0) = ws_st in
   let (ws, st) = Spec.shuffle_inner_loop a i ((ws_spec_v ws0).[l], (state_spec_v st0).[l]) in
   (ws_spec_v ws1).[l] == ws /\ (state_spec_v st1).[l] == st)

let shuffle_inner_loop_lemma_l #a #m i (ws0, st0) = admit()


val shuffle_lemma_l:
    #a:sha2_alg
  -> #m:m_spec
  -> ws:ws_spec a m
  -> st:state_spec a m
  -> l:nat{l < lanes a m} ->
  Lemma ((state_spec_v (shuffle ws st)).[l] == Spec.shuffle a (ws_spec_v ws).[l] (state_spec_v st).[l])

let shuffle_lemma_l #a #m ws st l = admit()


val init_lemma_l: a:sha2_alg -> m:m_spec -> l:nat{l < lanes a m} ->
  Lemma ((state_spec_v (init a m)).[l] == Spec.init a)

let init_lemma_l a m l = admit()


val update_lemma_l:
    #a:sha2_alg
  -> #m:m_spec
  -> b:multiblock_spec a m
  -> st:state_spec a m
  -> l:nat{l < lanes a m} ->
  Lemma ((state_spec_v (update b st)).[l] == Spec.update a b.(|l|) (state_spec_v st).[l])

let update_lemma_l #a #m b st l = admit()


val update_last_lemma_l:
    #a:sha2_alg
  -> #m:m_spec
  -> totlen:len_t a
  -> len:size_nat{len < block_length a}
  -> b:multiseq (lanes a m) len
  -> st:state_spec a m
  -> l:nat{l < lanes a m} ->
  Lemma ((state_spec_v (update_last totlen len b st)).[l] ==
    Spec.update_last a totlen len b.(|l|) (state_spec_v st).[l])

let update_last_lemma_l #a #m totlen len b st l = admit()


val hash_lemma_l:
    #a:sha2_alg
  -> #m:m_spec
  -> len:size_nat
  -> b:multiseq (lanes a m) len
  -> l:nat{l < lanes a m} ->
  Lemma ((hash #a #m len b).(|l|) == Spec.hash len b.(|l|))

let hash_lemma_l #a #m len b l = admit()
