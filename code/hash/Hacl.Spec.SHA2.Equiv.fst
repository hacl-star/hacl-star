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

let _Ch_lemma #a #m x y z :
  Lemma (vec_v (_Ch #a #m x y z) ==
    LSeq.createi (lanes a m) (fun i -> Spec._Ch a (vec_v x).[i] (vec_v y).[i] (vec_v z).[i]))
 =
  LSeq.eq_intro (vec_v (_Ch #a #m x y z))
    (LSeq.createi (lanes a m) (fun i -> Spec._Ch a (vec_v x).[i] (vec_v y).[i] (vec_v z).[i]))


let _Maj_lemma #a #m x y z :
  Lemma (vec_v (_Maj #a #m x y z) ==
    LSeq.createi (lanes a m) (fun i -> Spec._Maj a (vec_v x).[i] (vec_v y).[i] (vec_v z).[i]))
 =
  LSeq.eq_intro (vec_v (_Maj #a #m x y z))
    (LSeq.createi (lanes a m) (fun i -> Spec._Maj a (vec_v x).[i] (vec_v y).[i] (vec_v z).[i]))


let _Sigma0_lemma #a #m x : Lemma (vec_v (_Sigma0 #a #m x) == LSeq.map (Spec._Sigma0 a) (vec_v x)) =
  LSeq.eq_intro (vec_v (_Sigma0 #a #m x)) (LSeq.map (Spec._Sigma0 a) (vec_v x))

let _Sigma1_lemma #a #m x : Lemma (vec_v (_Sigma1 #a #m x) == LSeq.map (Spec._Sigma1 a) (vec_v x)) =
  LSeq.eq_intro (vec_v (_Sigma1 #a #m x)) (LSeq.map (Spec._Sigma1 a) (vec_v x))

let _sigma0_lemma #a #m x : Lemma (vec_v (_sigma0 #a #m x) == LSeq.map (Spec._sigma0 a) (vec_v x)) =
  LSeq.eq_intro (vec_v (_sigma0 #a #m x)) (LSeq.map (Spec._sigma0 a) (vec_v x))

let _sigma1_lemma #a #m x : Lemma (vec_v (_sigma1 #a #m x) == LSeq.map (Spec._sigma1 a) (vec_v x)) =
  LSeq.eq_intro (vec_v (_sigma1 #a #m x)) (LSeq.map (Spec._sigma1 a) (vec_v x))


val shuffle_core_spec_lemma_l:
    #a:sha2_alg
  -> #m:m_spec
  -> k_t:word a
  -> ws_t:element_t a m
  -> st:state_spec a m
  -> l:nat{l < lanes a m} ->
  Lemma
   ((state_spec_v (shuffle_core_spec k_t ws_t st)).[l] ==
     Spec.shuffle_core_pre a k_t (vec_v ws_t).[l] (state_spec_v st).[l])

let shuffle_core_spec_lemma_l #a #m k_t ws_t st l = admit()


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
