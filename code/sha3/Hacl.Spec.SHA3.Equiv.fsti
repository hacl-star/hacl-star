module Hacl.Spec.SHA3.Equiv

open FStar.Mul
open Lib.IntTypes
open Lib.NTuple
open Lib.Sequence
open Lib.IntVector
open Lib.LoopCombinators

open Spec.Hash.Definitions
open Hacl.Spec.SHA3.Vec
open Hacl.Spec.SHA3.Vec.Common
module Spec = Spec.SHA3
module BSeq = Lib.ByteSequence

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(* state_theta0 *)

val state_theta_inner_C_lemma_l:
  m:m_spec
  -> s:state_spec m
  -> i:size_nat{i < 5}
  -> _C:lseq (element_t m) 5
  -> l:nat{l < lanes m} ->
  Lemma
   ((_C_v (state_theta_inner_C m s i _C)).[l] ==
    Spec.state_theta_inner_C (state_spec_v s).[l] i (_C_v _C).[l])

val state_theta0_loop:
  m:m_spec
  -> s:state_spec m
  -> _C:lseq (element_t m) 5
  -> l:nat{l < lanes m}
  -> n:nat{n <= 5} ->
  Lemma
   ((_C_v (repeati n (state_theta_inner_C m s) _C)).[l] ==
    repeati n (Spec.state_theta_inner_C (state_spec_v s).[l]) (_C_v _C).[l])

val state_theta0_lemma_l:
  m:m_spec
  -> s:state_spec m
  -> _C:lseq (element_t m) 5
  -> l:nat{l < lanes m} ->
  Lemma ((_C_v (state_theta0 m s _C)).[l] == Spec.state_theta0 (state_spec_v s).[l] (_C_v _C).[l])

(* state_theta1 *)

val state_theta_inner_s_inner_lemma_l:
  m:m_spec
  -> x:index
  -> _D:element_t m
  -> y:index
  -> s:state_spec m
  -> l:nat{l < lanes m} ->
  Lemma
   ((state_spec_v (state_theta_inner_s_inner m x _D y s)).[l] ==
    Spec.state_theta_inner_s_inner x (vec_v _D).[l] y (state_spec_v s).[l])

val state_theta_inner_s_loop:
  m:m_spec
  -> _C:lseq (element_t m) 5
  -> x:index
  -> s:state_spec m
  -> l:nat{l < lanes m}
  -> n:nat{n <= 5} ->
  Lemma
   (let _D_u64 = ((_C_v _C).[l]).[(x + 4) % 5] ^. (Spec.rotl ((_C_v _C).[l]).[(x + 1) % 5] (size 1)) in
    let _D_elem = _C.[(x + 4) % 5] ^| (_C.[(x + 1) % 5] <<<| (size 1)) in
    (state_spec_v (repeati n (state_theta_inner_s_inner m x _D_elem) s)).[l] ==
    repeati n (Spec.state_theta_inner_s_inner x _D_u64) (state_spec_v s).[l])

val state_theta_inner_s_lemma_l:
  m:m_spec
  -> _C:lseq (element_t m) 5
  -> x:index
  -> s:state_spec m
  -> l:nat{l < lanes m} ->
  Lemma ((state_spec_v (state_theta_inner_s m _C x s)).[l] ==
         Spec.state_theta_inner_s (_C_v _C).[l] x (state_spec_v s).[l])

val state_theta1_loop:
  m:m_spec
  -> _C:lseq (element_t m) 5
  -> s:state_spec m
  -> l:nat{l < lanes m}
  -> n:nat{n <= 5} ->
  Lemma
   ((state_spec_v (repeati n (state_theta_inner_s m _C) s)).[l] ==
    repeati n (Spec.state_theta_inner_s (_C_v _C).[l]) (state_spec_v s).[l])

val state_theta1_lemma_l:
  m:m_spec
  -> _C:lseq (element_t m) 5
  -> s:state_spec m
  -> l:nat{l < lanes m} ->
  Lemma ((state_spec_v (state_theta1 m _C s)).[l] ==
         Spec.state_theta1 (_C_v _C).[l] (state_spec_v s).[l])

(* state_theta *)

val state_theta_lemma_l:
  m:m_spec
  -> s:state_spec m
  -> l:nat{l < lanes m} ->
  Lemma ((state_spec_v (state_theta m s)).[l] ==
         Spec.state_theta (state_spec_v s).[l])

(* state_pi_rho *)

val state_pi_rho_inner_lemma_l:
  m:m_spec
  -> i:size_nat{i < 24}
  -> current:element_t m
  -> s:state_spec m
  -> l:nat{l < lanes m} ->
  Lemma
   (let c', s' = state_pi_rho_inner m i (current, s) in
    (((vec_v c').[l] <: uint64), (state_spec_v s').[l]) ==
    Spec.state_pi_rho_inner i ((vec_v current).[l], (state_spec_v s).[l]))

val state_pi_rho_loop:
  m:m_spec
  -> s:state_spec m
  -> l:nat{l < lanes m}
  -> n:nat{n <= 24} ->
  Lemma
    (let c_elem = get m s 1 0 in
     let c_u64 = Spec.get (state_spec_v s).[l] 1 0 in
     let c', s' = repeat_gen n (state_pi_rho_s m)
       (state_pi_rho_inner m) (c_elem, s) in
     let c'_s, s'_s = repeat_gen n Spec.state_pi_rho_s
       Spec.state_pi_rho_inner (c_u64, (state_spec_v s).[l]) in
     (vec_v c').[l] == c'_s /\ (state_spec_v s').[l] == s'_s)

val state_pi_rho_lemma_l:
  m:m_spec
  -> s:state_spec m
  -> l:nat{l < lanes m} ->
  Lemma ((state_spec_v (state_pi_rho m s)).[l] ==
           Spec.state_pi_rho (state_spec_v s).[l])

(* state_chi *)

val state_chi_inner0_lemma_l:
  m:m_spec
  -> s_pi_rho:state_spec m
  -> y:index
  -> x:index
  -> s:state_spec m
  -> l:nat{l < lanes m} ->
  Lemma
   ((state_spec_v (state_chi_inner0 m s_pi_rho y x s)).[l] ==
      Spec.state_chi_inner0 (state_spec_v s_pi_rho).[l] y x (state_spec_v s).[l])

val state_chi_inner1_loop:
  m:m_spec
  -> s_pi_rho:state_spec m
  -> y:index
  -> s:state_spec m
  -> l:nat{l < lanes m}
  -> n:nat{n <= 5} ->
  Lemma
   ((state_spec_v (repeati n (state_chi_inner0 m s_pi_rho y) s)).[l] ==
      repeati n (Spec.state_chi_inner0 (state_spec_v s_pi_rho).[l] y) (state_spec_v s).[l])

val state_chi_inner1_lemma_l:
  m:m_spec
  -> s_pi_rho:state_spec m
  -> y:index
  -> s:state_spec m
  -> l:nat{l < lanes m} ->
  Lemma ((state_spec_v (state_chi_inner1 m s_pi_rho y s)).[l] ==
         Spec.state_chi_inner1 (state_spec_v s_pi_rho).[l] y (state_spec_v s).[l])

val state_chi_loop:
  m:m_spec
  -> s_pi_rho:state_spec m
  -> s:state_spec m
  -> l:nat{l < lanes m}
  -> n:nat{n <= 5} ->
  Lemma
   ((state_spec_v (repeati n (state_chi_inner1 m s_pi_rho) s)).[l] ==
      repeati n (Spec.state_chi_inner1 (state_spec_v s_pi_rho).[l]) (state_spec_v s).[l])

val state_chi_lemma_l:
  m:m_spec
  -> s_pi_rho:state_spec m
  -> l:nat{l < lanes m} ->
  Lemma ((state_spec_v (state_chi m s_pi_rho)).[l] ==
           Spec.state_chi (state_spec_v s_pi_rho).[l])

(* state_iota *)

val state_iota_lemma_l:
  m:m_spec
  -> s:state_spec m
  -> round:size_nat{round < 24}
  -> l:nat{l < lanes m} ->
  Lemma
   ((state_spec_v (state_iota m s round)).[l] ==
      Spec.state_iota (state_spec_v s).[l] round)

(* state_permute *)

val state_permute1_lemma_l:
  m:m_spec
  -> round:size_nat{round < 24}
  -> s:state_spec m
  -> l:nat{l < lanes m} ->
  Lemma ((state_spec_v (state_permute1 m round s)).[l] ==
         Spec.state_permute1 round (state_spec_v s).[l])

val state_permute_loop:
  m:m_spec
  -> s:state_spec m
  -> l:nat{l < lanes m}
  -> n:nat{n <= 24} ->
  Lemma
   ((state_spec_v (repeati n (state_permute1 m) s)).[l] ==
      repeati n Spec.state_permute1 (state_spec_v s).[l])

val state_permute_lemma_l:
  m:m_spec
  -> s:state_spec m
  -> l:nat{l < lanes m} ->
  Lemma ((state_spec_v (state_permute m s)).[l] ==
           Spec.state_permute (state_spec_v s).[l])

(* loadState *)

val load_blocks_lemma_ij:
    #a:keccak_alg
  -> #m:m_spec
  -> b:multiblock_spec a m
  -> j:nat{j < lanes m}
  -> i:nat{i < 32} ->
  Lemma (let l = lanes m in
    let ind = (i / l * l + j) * word_length a in
    (vec_v (load_blocks b).[i]).[j] ==
    BSeq.uint_from_bytes_le
      (Seq.slice b.(|i % l|) ind (ind + word_length a)))

val load_blocks_lemma_ij_subst:
    #a:keccak_alg
  -> #m:m_spec
  -> b:multiblock_spec a m
  -> j:nat{j < lanes m}
  -> i:nat{i < 32} ->
  Lemma (let l = lanes m in
    (vec_v (load_blocks b).[i / l * l + j]).[i % l] ==
    BSeq.uint_from_bytes_le
      (Seq.slice b.(|j|) (i * word_length a) (i * word_length a + word_length a)))

val load_ws_lemma_l:
    #a:keccak_alg
  -> #m:m_spec{is_supported m}
  -> b:multiblock_spec a m
  -> l:nat{l < lanes m}
  -> i:nat{i < 25} ->
  Lemma ((ws_spec_v (load_ws b)).[l].[i] == BSeq.uint_from_bytes_le
      (Seq.slice (Seq.slice b.(|l|) 0 200) (i * word_length a) (i * word_length a + word_length a)))

val loadState_inner_lemma_l:
    #a:keccak_alg
  -> #m:m_spec{is_supported m}
  -> b:multiblock_spec a m
  -> s:state_spec m
  -> l:nat{l < lanes m}
  -> i:nat{i < 25} ->
  Lemma ((state_spec_v (loadState_inner m (load_ws b) i s)).[l] ==
    Spec.loadState_inner (Seq.slice b.(|l|) 0 200) i (state_spec_v s).[l])

val loadState_loop_full:
  #a:keccak_alg
  -> #m:m_spec{is_supported m}
  -> r:size_nat{r > 0 /\ r <= 200}
  -> b:multiblock_spec a m
  -> s:state_spec m
  -> l:nat{l < lanes m}
  -> n:nat{n <= 25} ->
  Lemma
  ((state_spec_v (repeati n (loadState_inner m (load_ws b)) s)).[l] ==
    repeati n (Spec.loadState_inner (Seq.slice b.(|l|) 0 200))
      (state_spec_v s).[l])

val update_sub_b_lemma:
    #a:keccak_alg
  -> #m:m_spec{is_supported m}
  -> r:size_nat{r > 0 /\ r <= 200}
  -> b:multiblock_spec a m
  -> l:nat{l < lanes m} ->
  Lemma
  (requires
    forall l. l < lanes m ==> (forall j. (j >= r /\ j < 256) ==> Seq.index b.(|l|) j == u8 0))
  (ensures
    Seq.slice b.(|l|) 0 200 == update_sub (create 200 (u8 0)) 0 r (Seq.slice b.(|l|) 0 r))

val loadState_loop:
    #a:keccak_alg
  -> #m:m_spec{is_supported m}
  -> r:size_nat{r > 0 /\ r <= 200}
  -> b:multiblock_spec a m
  -> s:state_spec m
  -> l:nat{l < lanes m}
  -> n:nat{n <= 25} ->
  Lemma
  (requires
    forall l. l < lanes m ==> (forall j. (j >= r /\ j < 256) ==> Seq.index b.(|l|) j == u8 0))
  (ensures (let bs = update_sub (create 200 (u8 0)) 0 r (Seq.slice b.(|l|) 0 r) in
    (state_spec_v (repeati n (loadState_inner m (load_ws b)) s)).[l] ==
      repeati n (Spec.loadState_inner bs) (state_spec_v s).[l]))

val loadState_lemma_l:
  #a:keccak_alg
  -> #m:m_spec{is_supported m}
  -> r:size_nat{r > 0 /\ r <= 200}
  -> b:multiblock_spec a m
  -> s:state_spec m
  -> l:nat{l < lanes m} ->
  Lemma
  (requires
    forall l. l < lanes m ==> (forall j. (j >= r /\ j < 256) ==> Seq.index b.(|l|) j == u8 0))
  (ensures 
    (state_spec_v (loadState #a #m r b s)).[l] ==
      Spec.loadState r (Seq.slice b.(|l|) 0 r) (state_spec_v s).[l])

(* storeState *)

val storeState_lemma_ij:
    #a:keccak_alg
  -> #m:m_spec{is_supported m}
  -> s:state_spec m
  -> j:nat{j < lanes m}
  -> i:nat{i < 25 * word_length a} ->
  Lemma
   ((storeState #a #m s).[j * (32 * word_length a) + i] ==
      (BSeq.uint_to_bytes_le (Seq.index (state_spec_v s).[j] (i / word_length a))).[i % word_length a])

val storeState_lemma_ij_sub:
    #a:keccak_alg
  -> #m:m_spec{is_supported m}
  -> s:state_spec m
  -> j:nat{j < lanes m}
  -> i:nat{i < 25} ->
  Lemma
   (sub (sub (storeState #a #m s) (j * (32 * word_length a)) (25 * word_length a)) (i * word_length a) (word_length a) ==
      BSeq.uint_to_bytes_le (Seq.index (state_spec_v s).[j] i))

let storeState_inner_unroll (s:Spec.state) : Tot (BSeq.lbytes 200) =
  let block = Spec.storeState_inner s 0 (create 200 (u8 0)) in
  let block = Spec.storeState_inner s 1 block in
  let block = Spec.storeState_inner s 2 block in
  let block = Spec.storeState_inner s 3 block in
  let block = Spec.storeState_inner s 4 block in
  let block = Spec.storeState_inner s 5 block in
  let block = Spec.storeState_inner s 6 block in
  let block = Spec.storeState_inner s 7 block in
  let block = Spec.storeState_inner s 8 block in
  let block = Spec.storeState_inner s 9 block in
  let block = Spec.storeState_inner s 10 block in
  let block = Spec.storeState_inner s 11 block in
  let block = Spec.storeState_inner s 12 block in
  let block = Spec.storeState_inner s 13 block in
  let block = Spec.storeState_inner s 14 block in
  let block = Spec.storeState_inner s 15 block in
  let block = Spec.storeState_inner s 16 block in
  let block = Spec.storeState_inner s 17 block in
  let block = Spec.storeState_inner s 18 block in
  let block = Spec.storeState_inner s 19 block in
  let block = Spec.storeState_inner s 20 block in
  let block = Spec.storeState_inner s 21 block in
  let block = Spec.storeState_inner s 22 block in
  let block = Spec.storeState_inner s 23 block in
  let block = Spec.storeState_inner s 24 block in
  block

val storeState_inner_loop:
  s:Spec.state  ->
  Lemma
   (storeState_inner_unroll s ==
      repeati 25 (Spec.storeState_inner s) (create 200 (u8 0)))

val storeState_inner_unroll_sub_0_6:
    #a:keccak_alg
  -> #m:m_spec{is_supported m}
  -> s:Spec.state
  -> i:nat{i < 6} ->
  Lemma
   (sub (storeState_inner_unroll s) (i * 8) 8 ==
      BSeq.uint_to_bytes_le #U64 s.[i])

val storeState_inner_unroll_sub_6_12:
    #a:keccak_alg
  -> #m:m_spec{is_supported m}
  -> s:Spec.state
  -> i:nat{i >= 6 /\ i < 12} ->
  Lemma
   (sub (storeState_inner_unroll s) (i * 8) 8 ==
      BSeq.uint_to_bytes_le #U64 s.[i])

val storeState_inner_unroll_sub_12_18:
    #a:keccak_alg
  -> #m:m_spec{is_supported m}
  -> s:Spec.state
  -> i:nat{i >= 12 /\ i < 18} ->
  Lemma
   (sub (storeState_inner_unroll s) (i * 8) 8 ==
      BSeq.uint_to_bytes_le #U64 s.[i])

val storeState_inner_unroll_sub_18_25:
    #a:keccak_alg
  -> #m:m_spec{is_supported m}
  -> s:Spec.state
  -> i:nat{i >= 18 /\ i < 25} ->
  Lemma
   (sub (storeState_inner_unroll s) (i * 8) 8 ==
      BSeq.uint_to_bytes_le #U64 s.[i])

val storeState_inner_unroll_sub:
    #a:keccak_alg
  -> #m:m_spec{is_supported m}
  -> s:Spec.state
  -> i:nat{i < 25} ->
  Lemma
   (sub (storeState_inner_unroll s) (i * 8) 8 ==
      BSeq.uint_to_bytes_le #U64 s.[i])

val sub_word_length_lemma:
    #a:keccak_alg
  -> l0:lseq uint8 (25 * word_length a)
  -> l1:lseq uint8 (25 * word_length a) ->
  Lemma
  (requires
    forall (i:nat{0 <= i /\ i < 25}).
    (forall (j:nat{0 <= j /\ j < word_length a}).
      Seq.index (sub l0 (i*word_length a) (word_length a)) j ==
        Seq.index (sub l1 (i*word_length a) (word_length a)) j))
  (ensures l0 == l1)

val storeState_lemma_l:
  #a:keccak_alg
  -> #m:m_spec{is_supported m}
  -> r:size_nat{r <= 200}
  -> s:state_spec m
  -> l:nat{l < lanes m} ->
  Lemma
   (sub (storeState #a #m s) (l * (32 * word_length a)) r ==
     Spec.storeState r (state_spec_v s).[l])

val storeState_update_b_lemma_l:
  #a:keccak_alg
  -> #m:m_spec{is_supported m}
  -> r:size_nat{r > 0 /\ r <= 200}
  -> outputByteLen:size_nat
  -> i:size_nat{i < outputByteLen / r}
  -> b:multiseq (lanes m) outputByteLen
  -> s:state_spec m
  -> l:nat{l < lanes m} ->
  Lemma
   (let block = storeState #a #m s in
    let b' = update_b #m block r outputByteLen i b in
    i * r + r <= outputByteLen /\
    sub #uint8 #outputByteLen b'.(|l|) (i * r) r ==
     Spec.storeState r (state_spec_v s).[l] /\
    (forall j. (j < i * r /\ j >= i * r + r) ==>
      Seq.index b'.(|l|) j == Seq.index b.(|l|) j))

val storeState_update_b_last_lemma_l:
  #a:keccak_alg
  -> #m:m_spec{is_supported m}
  -> r:size_nat{r > 0 /\ r <= 200}
  -> outputByteLen:size_nat
  -> outRem:size_nat{outRem == outputByteLen % r}
  -> b:multiseq (lanes m) outputByteLen
  -> s:state_spec m
  -> l:nat{l < lanes m} ->
  Lemma
   (let block = storeState #a #m s in
    let b' = update_b_last #m block r outputByteLen outRem b in
    outRem <= outputByteLen /\
    sub #uint8 #outputByteLen b'.(|l|) (outputByteLen - outRem) outRem ==
     Spec.storeState outRem (state_spec_v s).[l] /\
    (forall i. (i < outputByteLen - outRem) ==>
      Seq.index b'.(|l|) i == Seq.index b.(|l|) i))

(* absorb_inner *)

val absorb_inner_lemma_l:
  #a:keccak_alg
  -> #m:m_spec{is_supported m}
  -> r:size_nat{r > 0 /\ r <= 200}
  -> input:multiseq (lanes m) 256{forall l. l < lanes m ==> 
     (forall i. (i >= r /\ i < 256) ==> Seq.index input.(|l|) i == u8 0)}
  -> s:state_spec m
  -> l:nat{l < lanes m} ->
  Lemma
   ((state_spec_v (absorb_inner #a #m r input s)).[l] ==
    Spec.absorb_inner r (sub #uint8 #256 input.(|l|) 0 r) (state_spec_v s).[l])

(* absorb_inner_block *)

val absorb_inner_block_lemma_l:
  #a:keccak_alg
  -> #m:m_spec{is_supported m}
  -> r:size_nat{r > 0 /\ r <= 200}
  -> inputByteLen:nat
  -> input:multiseq (lanes m) inputByteLen
  -> i:nat{i < inputByteLen / r}
  -> s:state_spec m
  -> l:nat{l < lanes m} ->
  Lemma
   ((state_spec_v (absorb_inner_block #a #m r inputByteLen input i s)).[l] ==
    repeat_blocks_f r input.(|l|) (Spec.absorb_inner r) (inputByteLen / r) i (state_spec_v s).[l])

(* absorb_inner_nblocks *)

val absorb_inner_loop:
  #a:keccak_alg
  -> #m:m_spec{is_supported m}
  -> r:size_nat{r > 0 /\ r <= 200}
  -> inputByteLen:nat
  -> input:multiseq (lanes m) inputByteLen
  -> s:state_spec m
  -> l:nat{l < lanes m}
  -> n:nat{n <= inputByteLen / r} ->
  Lemma
   ((state_spec_v (repeati n (absorb_inner_block #a #m r inputByteLen input) s)).[l] ==
    repeati n (repeat_blocks_f r input.(|l|) (Spec.absorb_inner r) (inputByteLen / r)) (state_spec_v s).[l])

val absorb_inner_nblocks_lemma_l:
  #a:keccak_alg
  -> #m:m_spec{is_supported m}
  -> r:size_nat{r > 0 /\ r <= 200}
  -> inputByteLen:nat
  -> input:multiseq (lanes m) inputByteLen
  -> s:state_spec m
  -> l:nat{l < lanes m} ->
  Lemma
   ((state_spec_v (absorb_inner_nblocks #a #m r inputByteLen input s)).[l] ==
    repeati (inputByteLen / r) (repeat_blocks_f r input.(|l|) (Spec.absorb_inner r) (inputByteLen / r)) (state_spec_v s).[l])

(* absorb_next *)

val next_block_lemma_l:
  #m:m_spec{is_supported m}
  -> r:size_nat{r > 0 /\ r <= 200}
  -> l:nat{l < lanes m} ->
  Lemma
   (sub #uint8 #256 ((next_block #m r (next_block_seq_zero m)).(|l|)) 0 r ==
    ((create r (u8 0)).[r - 1] <- u8 0x80))

val absorb_next_lemma_l:
  #a:keccak_alg
  -> #m:m_spec{is_supported m}
  -> r:size_nat{r > 0 /\ r <= 200}
  -> s:state_spec m
  -> l:nat{l < lanes m} ->
  Lemma
   ((state_spec_v (absorb_next #a #m r s)).[l] ==
    Spec.absorb_next (state_spec_v s).[l] r)

(* absorb_last *)

val load_last_block_lemma_helper:
  #m:m_spec{is_supported m}
  -> delimitedSuffix:byte_t
  -> r:size_nat{r > 0 /\ r <= 200}
  -> rem:size_nat{rem < r}
  -> input:BSeq.lbytes rem ->
  Lemma(let b_0 = update_sub (create r (u8 0)) 0 rem input in
        let b = b_0.[rem] <- byte_to_uint8 delimitedSuffix in
        (forall i. (i >= 0 /\ i < rem) ==> Seq.index b i == Seq.index input i) /\
        Seq.index b rem == byte_to_uint8 delimitedSuffix /\
        (forall i. (i >= (rem + 1) /\ i < r) ==> Seq.index b i == u8 0))

val load_last_block_lemma_l:
  #m:m_spec{is_supported m}
  -> delimitedSuffix:byte_t
  -> r:size_nat{r > 0 /\ r <= 200}
  -> rem:size_nat{rem < r}
  -> input:multiseq (lanes m) 256{forall l. l < lanes m ==> 
       (forall i. (i >= rem /\ i < 256) ==> Seq.index input.(|l|) i == u8 0)}
  -> l:nat{l < lanes m} ->
  Lemma
   (let b = update_sub (create r (u8 0)) 0 rem (sub #uint8 #256 input.(|l|) 0 rem) in
    sub #uint8 #256 ((load_last_block #m r rem delimitedSuffix input).(|l|)) 0 r ==
      (b.[rem] <- byte_to_uint8 delimitedSuffix))

val absorb_last_lemma_l:
  #a:keccak_alg
  -> #m:m_spec{is_supported m}
  -> delimitedSuffix:byte_t
  -> r:size_nat{r > 0 /\ r <= 200}
  -> rem:size_nat{rem < r}
  -> input:multiseq (lanes m) 256{forall l. l < lanes m ==> 
       (forall i. (i >= rem /\ i < 256) ==> Seq.index input.(|l|) i == u8 0)}
  -> s:state_spec m
  -> l:nat{l < lanes m} ->
  Lemma
   ((state_spec_v (absorb_last #a #m delimitedSuffix r rem input s)).[l] ==
    Spec.absorb_last delimitedSuffix r rem (sub #uint8 #256 input.(|l|) 0 rem) (state_spec_v s).[l])

(* absorb_final *)

val absorb_final_lemma_l:
  #a:keccak_alg
  -> #m:m_spec{is_supported m}
  -> delimitedSuffix:byte_t
  -> r:size_nat{r > 0 /\ r <= 200}
  -> inputByteLen:nat
  -> input:multiseq (lanes m) inputByteLen
  -> s:state_spec m
  -> l:nat{l < lanes m} ->
  Lemma
   (inputByteLen - (inputByteLen / r) * r <= inputByteLen /\
   (inputByteLen / r) * r == inputByteLen - (inputByteLen % r) /\
    (state_spec_v (absorb_final #a #m s r inputByteLen input delimitedSuffix)).[l] ==
      Spec.absorb_last delimitedSuffix r (inputByteLen % r)
        (Seq.slice input.(|l|) ((inputByteLen / r) * r) inputByteLen) (state_spec_v s).[l])

(* absorb *)

val absorb_lemma_l:
  #a:keccak_alg
  -> #m:m_spec{is_supported m}
  -> s:state_spec m
  -> r:size_nat{r > 0 /\ r <= 200}
  -> inputByteLen:nat
  -> input:multiseq (lanes m) inputByteLen
  -> delimitedSuffix:byte_t
  -> l:nat{l < lanes m} ->
  Lemma
   ((state_spec_v (absorb #a #m s r inputByteLen input delimitedSuffix)).[l] ==
    Spec.absorb (state_spec_v s).[l] r inputByteLen input.(|l|) delimitedSuffix)

(* squeeze_inner *)

val squeeze_inner_lemma_l:
  #a:keccak_alg
  -> #m:m_spec{is_supported m}
  -> r:size_nat{r > 0 /\ r <= 200}
  -> outputByteLen:size_nat
  -> i:size_nat{i < outputByteLen / r}
  -> s:state_spec m
  -> b:multiseq (lanes m) outputByteLen
  -> s_pre:lseq uint8 (i * r)
  -> l:nat{l < lanes m} ->
  Lemma
  (requires
    s_pre == sub #uint8 #outputByteLen b.(|l|) 0 (i * r))
  (ensures
    (let s', b' = squeeze_inner #a #m r outputByteLen i (s, b) in
    let s'_s, b'_s = Spec.squeeze_inner r outputByteLen i (state_spec_v s).[l] in
    (state_spec_v s').[l] == s'_s /\ i * r + r <= outputByteLen /\
    sub #uint8 #outputByteLen b'.(|l|) 0 (i * r + r) == Seq.append s_pre b'_s))

(* squeeze_nblocks *)

val lemma_generate_squeeze_inner_loop:
    #a:keccak_alg
  -> #m:m_spec{is_supported m}
  -> r:size_nat{r > 0 /\ r <= 200}
  -> outputByteLen:size_nat
  -> n:nat{n <= outputByteLen}
  -> s:state_spec m
  -> b:multiseq (lanes m) outputByteLen
  -> l:nat{l < lanes m} -> Lemma
  (n / r <= outputByteLen / r /\
   (let c (i:nat{i <= outputByteLen / r}) = Spec.state in
   let (s1, out1) = generate_blocks r (outputByteLen / r) (n / r) c (Spec.squeeze_inner r outputByteLen) (state_spec_v s).[l] in
   let (s2, out2) = repeat_gen (n / r) (squeeze_s m r outputByteLen) (squeeze_inner #a #m r outputByteLen) (s, b) in
   (state_spec_v s2).[l] == (s1 <: Spec.state) /\ (n / r) * r <= outputByteLen /\
   sub #uint8 #outputByteLen out2.(|l|) 0 ((n / r) * r) == out1))

val squeeze_nblocks_lemma_l:
    #a:keccak_alg
  -> #m:m_spec{is_supported m}
  -> r:size_nat{r > 0 /\ r <= 200}
  -> outputByteLen:size_nat
  -> s:state_spec m
  -> b:multiseq (lanes m) outputByteLen
  -> l:nat{l < lanes m} -> Lemma
  (let c (i:nat{i <= outputByteLen / r}) = Spec.state in
   let (s1, out1) = generate_blocks r (outputByteLen / r) (outputByteLen / r) c (Spec.squeeze_inner r outputByteLen) (state_spec_v s).[l] in
   let (s2, out2) = repeat_gen (outputByteLen / r) (squeeze_s m r outputByteLen) (squeeze_inner #a #m r outputByteLen) (s, b) in
   (state_spec_v s2).[l] == (s1 <: Spec.state) /\ (outputByteLen / r) * r <= outputByteLen /\
   sub #uint8 #outputByteLen out2.(|l|) 0 ((outputByteLen / r) * r) == out1)

(* squeeze_last *)

val squeeze_last_lemma_l:
  #a:keccak_alg
  -> #m:m_spec{is_supported m}
  -> r:size_nat{r > 0 /\ r <= 200}
  -> outputByteLen:size_nat
  -> s:state_spec m
  -> b:multiseq (lanes m) outputByteLen
  -> l:nat{l < lanes m} ->
  Lemma
   (let outRem = outputByteLen % r in
    let b' = squeeze_last #a #m s r outputByteLen b in
    let b'_s = Spec.storeState outRem (state_spec_v s).[l] in
    outRem <= outputByteLen /\
    sub #uint8 #outputByteLen b'.(|l|) (outputByteLen - outRem) outRem == b'_s /\
    (forall i. (i < outputByteLen - outRem) ==>
      Seq.index b'.(|l|) i == Seq.index b.(|l|) i))

(* squeeze *)

val squeeze_lemma_l:
  #a:keccak_alg
  -> #m:m_spec{is_supported m}
  -> s:state_spec m
  -> r:size_nat{r > 0 /\ r <= 200}
  -> outputByteLen:size_nat
  -> b:multiseq (lanes m) outputByteLen
  -> l:nat{l < lanes m} ->
  Lemma
   ((squeeze #a #m s r outputByteLen b).(|l|) ==
      Spec.squeeze (state_spec_v s).[l] r outputByteLen)

(* keccak *)

val keccak_lemma_l:
  #a:keccak_alg
  -> #m:m_spec{is_supported m}
  -> rate:size_nat{rate % 8 == 0 /\ rate / 8 > 0 /\ rate <= 1600}
  -> inputByteLen:nat
  -> input:multiseq (lanes m) inputByteLen
  -> delimitedSuffix:byte_t
  -> outputByteLen:size_nat
  -> b:multiseq (lanes m) outputByteLen
  -> l:nat{l < lanes m} ->
  Lemma
   ((keccak #a #m rate inputByteLen input delimitedSuffix outputByteLen b).(|l|) ==
      Spec.keccak rate (1600 - rate) inputByteLen input.(|l|) delimitedSuffix outputByteLen)

(* shake128 *)

val shake128_lemma_l:
  m:m_spec{is_supported m}
  -> inputByteLen:nat
  -> input:multiseq (lanes m) inputByteLen
  -> outputByteLen:size_nat
  -> output:multiseq (lanes m) outputByteLen
  -> l:nat{l < lanes m} ->
  Lemma
   ((shake128 m inputByteLen input outputByteLen output).(|l|) ==
      Spec.shake128 inputByteLen input.(|l|) outputByteLen)

(* shake256 *)

val shake256_lemma_l:
  m:m_spec{is_supported m}
  -> inputByteLen:nat
  -> input:multiseq (lanes m) inputByteLen
  -> outputByteLen:size_nat
  -> output:multiseq (lanes m) outputByteLen
  -> l:nat{l < lanes m} ->
  Lemma
   ((shake256 m inputByteLen input outputByteLen output).(|l|) ==
      Spec.shake256 inputByteLen input.(|l|) outputByteLen)

(* sha3_224 *)

val sha3_224_lemma_l:
  m:m_spec{is_supported m}
  -> inputByteLen:nat
  -> input:multiseq (lanes m) inputByteLen
  -> output:multiseq (lanes m) 28
  -> l:nat{l < lanes m} ->
  Lemma
   ((sha3_224 m inputByteLen input output).(|l|) ==
      Spec.sha3_224 inputByteLen input.(|l|))

(* sha3_256 *)

val sha3_256_lemma_l:
  m:m_spec{is_supported m}
  -> inputByteLen:nat
  -> input:multiseq (lanes m) inputByteLen
  -> output:multiseq (lanes m) 32
  -> l:nat{l < lanes m} ->
  Lemma
   ((sha3_256 m inputByteLen input output).(|l|) ==
      Spec.sha3_256 inputByteLen input.(|l|))

(* sha3_384 *)

val sha3_384_lemma_l:
  m:m_spec{is_supported m}
  -> inputByteLen:nat
  -> input:multiseq (lanes m) inputByteLen
  -> output:multiseq (lanes m) 48
  -> l:nat{l < lanes m} ->
  Lemma
   ((sha3_384 m inputByteLen input output).(|l|) ==
      Spec.sha3_384 inputByteLen input.(|l|))

(* sha3_512 *)

val sha3_512_lemma_l:
  m:m_spec{is_supported m}
  -> inputByteLen:nat
  -> input:multiseq (lanes m) inputByteLen
  -> output:multiseq (lanes m) 64
  -> l:nat{l < lanes m} ->
  Lemma
   ((sha3_512 m inputByteLen input output).(|l|) ==
      Spec.sha3_512 inputByteLen input.(|l|))
