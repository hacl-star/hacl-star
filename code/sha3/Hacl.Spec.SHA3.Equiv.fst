module Hacl.Spec.SHA3.Equiv

open FStar.Mul
open Lib.IntTypes
open Lib.NTuple
open Lib.Sequence
open Lib.IntVector
open Lib.IntVector.Serialize
open Lib.LoopCombinators

open Spec.Hash.Definitions
open Hacl.Spec.SHA3.Vec
open Hacl.Spec.SHA3.Vec.Common
module Spec = Spec.SHA3
module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence
module Lemmas = Hacl.Spec.SHA3.Lemmas

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

let state_theta_inner_C_lemma_l m s i _C l =
  eq_intro (_C_v (state_theta_inner_C m s i _C)).[l]
    (Spec.state_theta_inner_C (state_spec_v s).[l] i (_C_v _C).[l])

val state_theta0_loop:
  m:m_spec
  -> s:state_spec m
  -> _C:lseq (element_t m) 5
  -> l:nat{l < lanes m}
  -> n:nat{n <= 5} ->
  Lemma
   ((_C_v (repeati n (state_theta_inner_C m s) _C)).[l] ==
    repeati n (Spec.state_theta_inner_C (state_spec_v s).[l]) (_C_v _C).[l])

let rec state_theta0_loop m s _C l n =
  if n = 0 then begin
    eq_repeati0 n (state_theta_inner_C m s) _C;
    eq_repeati0 n (Spec.state_theta_inner_C (state_spec_v s).[l]) (_C_v _C).[l];
    () end
  else begin
    let lp0 = repeati (n - 1) (state_theta_inner_C m s) _C in
    state_theta0_loop m s _C l (n - 1);
    unfold_repeati n (state_theta_inner_C m s) _C (n - 1);
    unfold_repeati n (Spec.state_theta_inner_C (state_spec_v s).[l]) (_C_v _C).[l] (n - 1);
    state_theta_inner_C_lemma_l m s (n - 1) lp0 l;
    () end

val state_theta0_lemma_l:
  m:m_spec
  -> s:state_spec m
  -> _C:lseq (element_t m) 5
  -> l:nat{l < lanes m} ->
  Lemma ((_C_v (state_theta0 m s _C)).[l] == Spec.state_theta0 (state_spec_v s).[l] (_C_v _C).[l])

let state_theta0_lemma_l m s _C l = state_theta0_loop m s _C l 5

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

let state_theta_inner_s_inner_lemma_l m x _D y s l =
  eq_intro (state_spec_v (state_theta_inner_s_inner m x _D y s)).[l]
    (Spec.state_theta_inner_s_inner x (vec_v _D).[l] y (state_spec_v s).[l])

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

let rec state_theta_inner_s_loop m _C x s l n =
  let _D_u64 = ((_C_v _C).[l]).[(x + 4) % 5] ^. (Spec.rotl ((_C_v _C).[l]).[(x + 1) % 5] (size 1)) in
  let _D_elem = _C.[(x + 4) % 5] ^| (_C.[(x + 1) % 5] <<<| (size 1)) in

  if n = 0 then begin
    eq_repeati0 n (state_theta_inner_s_inner m x _D_elem) s;
    eq_repeati0 n (Spec.state_theta_inner_s_inner x _D_u64) (state_spec_v s).[l] end
  else begin
    let lp0 = repeati (n - 1) (state_theta_inner_s_inner m x _D_elem) s in
    state_theta_inner_s_loop m _C x s l (n - 1);
    unfold_repeati n (state_theta_inner_s_inner m x _D_elem) s (n - 1);
    unfold_repeati n (Spec.state_theta_inner_s_inner x _D_u64) (state_spec_v s).[l] (n - 1);
    state_theta_inner_s_inner_lemma_l m x _D_elem (n - 1) lp0 l;
    () end

val state_theta_inner_s_lemma_l:
  m:m_spec
  -> _C:lseq (element_t m) 5
  -> x:index
  -> s:state_spec m
  -> l:nat{l < lanes m} ->
  Lemma ((state_spec_v (state_theta_inner_s m _C x s)).[l] ==
         Spec.state_theta_inner_s (_C_v _C).[l] x (state_spec_v s).[l])

let state_theta_inner_s_lemma_l m _C x s l = state_theta_inner_s_loop m _C x s l 5

val state_theta1_loop:
  m:m_spec
  -> _C:lseq (element_t m) 5
  -> s:state_spec m
  -> l:nat{l < lanes m}
  -> n:nat{n <= 5} ->
  Lemma
   ((state_spec_v (repeati n (state_theta_inner_s m _C) s)).[l] ==
    repeati n (Spec.state_theta_inner_s (_C_v _C).[l]) (state_spec_v s).[l])

let rec state_theta1_loop m _C s l n =
  if n = 0 then begin
    eq_repeati0 n (state_theta_inner_s m _C) s;
    eq_repeati0 n (Spec.state_theta_inner_s (_C_v _C).[l]) (state_spec_v s).[l] end
  else begin
    let lp0 = repeati (n - 1) (state_theta_inner_s m _C) s in
    state_theta1_loop m _C s l (n - 1);
    unfold_repeati n (state_theta_inner_s m _C) s (n - 1);
    unfold_repeati n (Spec.state_theta_inner_s (_C_v _C).[l]) (state_spec_v s).[l] (n - 1);
    state_theta_inner_s_lemma_l m _C (n - 1) lp0 l;
    () end

val state_theta1_lemma_l:
  m:m_spec
  -> _C:lseq (element_t m) 5
  -> s:state_spec m
  -> l:nat{l < lanes m} ->
  Lemma ((state_spec_v (state_theta1 m _C s)).[l] ==
         Spec.state_theta1 (_C_v _C).[l] (state_spec_v s).[l])

let state_theta1_lemma_l m _C s l = state_theta1_loop m _C s l 5

(* state_theta *)

val state_theta_lemma_l:
  m:m_spec
  -> s:state_spec m
  -> l:nat{l < lanes m} ->
  Lemma ((state_spec_v (state_theta m s)).[l] ==
         Spec.state_theta (state_spec_v s).[l])

let state_theta_lemma_l m s l =
  eq_intro (_C_v (create 5 (zero_element m))).[l] (create 5 (u64 0));
  let _C = create 5 (zero_element m) in
  state_theta0_lemma_l m s _C l;
  let _C = state_theta0 m s _C in
  state_theta1_lemma_l m _C s l

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

let state_pi_rho_inner_lemma_l m i current s l =
  let _, s' = state_pi_rho_inner m i (current, s) in
  let _, s'_s = Spec.state_pi_rho_inner i ((vec_v current).[l], (state_spec_v s).[l]) in
  eq_intro (state_spec_v s').[l] s'_s

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

let rec state_pi_rho_loop m s l n =
  let c_elem = get m s 1 0 in
  let c_u64 = Spec.get (state_spec_v s).[l] 1 0 in

  if n = 0 then begin
    eq_repeat_gen0 n (state_pi_rho_s m)
      (state_pi_rho_inner m) (c_elem, s);
    eq_repeat_gen0 n Spec.state_pi_rho_s
      Spec.state_pi_rho_inner (c_u64, (state_spec_v s).[l]);
    () end
  else begin
    let c_lp0, lp0 = repeat_gen (n - 1) (state_pi_rho_s m)
      (state_pi_rho_inner m) (c_elem, s) in
    state_pi_rho_loop m s l (n - 1);
    unfold_repeat_gen n (state_pi_rho_s m)
      (state_pi_rho_inner m) (c_elem, s) (n - 1);
    unfold_repeat_gen n Spec.state_pi_rho_s
      Spec.state_pi_rho_inner (c_u64, (state_spec_v s).[l]) (n - 1);
    state_pi_rho_inner_lemma_l m (n - 1) c_lp0 lp0 l;
    () end

val state_pi_rho_lemma_l:
  m:m_spec
  -> s:state_spec m
  -> l:nat{l < lanes m} ->
  Lemma ((state_spec_v (state_pi_rho m s)).[l] ==
           Spec.state_pi_rho (state_spec_v s).[l])

let state_pi_rho_lemma_l m s l = state_pi_rho_loop m s l 24

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

let state_chi_inner0_lemma_l m s_pi_rho y x s l =
  eq_intro (state_spec_v (state_chi_inner0 m s_pi_rho y x s)).[l]
    (Spec.state_chi_inner0 (state_spec_v s_pi_rho).[l] y x (state_spec_v s).[l])

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

let rec state_chi_inner1_loop m s_pi_rho y s l n =
  if n = 0 then begin
    eq_repeati0 n (state_chi_inner0 m s_pi_rho y) s;
    eq_repeati0 n (Spec.state_chi_inner0 (state_spec_v s_pi_rho).[l] y) (state_spec_v s).[l] end
  else begin
    let lp0 = repeati (n - 1) (state_chi_inner0 m s_pi_rho y) s in
    state_chi_inner1_loop m s_pi_rho y s l (n - 1);
    unfold_repeati n (state_chi_inner0 m s_pi_rho y) s (n - 1);
    unfold_repeati n (Spec.state_chi_inner0 (state_spec_v s_pi_rho).[l] y) (state_spec_v s).[l] (n - 1);
    state_chi_inner0_lemma_l m s_pi_rho y (n - 1) lp0 l;
    () end

val state_chi_inner1_lemma_l:
  m:m_spec
  -> s_pi_rho:state_spec m
  -> y:index
  -> s:state_spec m
  -> l:nat{l < lanes m} ->
  Lemma ((state_spec_v (state_chi_inner1 m s_pi_rho y s)).[l] ==
         Spec.state_chi_inner1 (state_spec_v s_pi_rho).[l] y (state_spec_v s).[l])

let state_chi_inner1_lemma_l m s_pi_rho y s l = state_chi_inner1_loop m s_pi_rho y s l 5

val state_chi_loop:
  m:m_spec
  -> s_pi_rho:state_spec m
  -> s:state_spec m
  -> l:nat{l < lanes m}
  -> n:nat{n <= 5} ->
  Lemma
   ((state_spec_v (repeati n (state_chi_inner1 m s_pi_rho) s)).[l] ==
      repeati n (Spec.state_chi_inner1 (state_spec_v s_pi_rho).[l]) (state_spec_v s).[l])

let rec state_chi_loop m s_pi_rho s l n =
  if n = 0 then begin
    eq_repeati0 n (state_chi_inner1 m s_pi_rho) s;
    eq_repeati0 n (Spec.state_chi_inner1 (state_spec_v s_pi_rho).[l]) (state_spec_v s).[l] end
  else begin
    let lp0 = repeati (n - 1) (state_chi_inner1 m s_pi_rho) s in
    state_chi_loop m s_pi_rho s l (n - 1);
    unfold_repeati n (state_chi_inner1 m s_pi_rho) s (n - 1);
    unfold_repeati n (Spec.state_chi_inner1 (state_spec_v s_pi_rho).[l]) (state_spec_v s).[l] (n - 1);
    state_chi_inner1_lemma_l m s_pi_rho (n - 1) lp0 l;
    () end

val state_chi_lemma_l:
  m:m_spec
  -> s_pi_rho:state_spec m
  -> l:nat{l < lanes m} ->
  Lemma ((state_spec_v (state_chi m s_pi_rho)).[l] ==
           Spec.state_chi (state_spec_v s_pi_rho).[l])

let state_chi_lemma_l m s_pi_rho l = state_chi_loop m s_pi_rho s_pi_rho l 5

val state_iota_lemma_l:
  m:m_spec
  -> s:state_spec m
  -> round:size_nat{round < 24}
  -> l:nat{l < lanes m} ->
  Lemma
   ((state_spec_v (state_iota m s round)).[l] ==
      Spec.state_iota (state_spec_v s).[l] round)

let state_iota_lemma_l m s round l =
  eq_intro (state_spec_v (state_iota m s round)).[l]
    (Spec.state_iota (state_spec_v s).[l] round)

(* state_permute *)

val state_permute1_lemma_l:
  m:m_spec
  -> round:size_nat{round < 24}
  -> s:state_spec m
  -> l:nat{l < lanes m} ->
  Lemma ((state_spec_v (state_permute1 m round s)).[l] ==
         Spec.state_permute1 round (state_spec_v s).[l])

let state_permute1_lemma_l m round s l =
  state_theta_lemma_l m s l;
  let s_theta = state_theta m s in
  state_pi_rho_lemma_l m s_theta l;
  let s_pi_rho = state_pi_rho m s_theta in
  state_chi_lemma_l m s_pi_rho l;
  let s_chi = state_chi m s_pi_rho in
  state_iota_lemma_l m s_chi round l

val state_permute_loop:
  m:m_spec
  -> s:state_spec m
  -> l:nat{l < lanes m}
  -> n:nat{n <= 24} ->
  Lemma
   ((state_spec_v (repeati n (state_permute1 m) s)).[l] ==
      repeati n Spec.state_permute1 (state_spec_v s).[l])

let rec state_permute_loop m s l n =
  if n = 0 then begin
    eq_repeati0 n (state_permute1 m) s;
    eq_repeati0 n Spec.state_permute1 (state_spec_v s).[l] end
  else begin
    let lp0 = repeati (n - 1) (state_permute1 m) s in
    state_permute_loop m s l (n - 1);
    unfold_repeati n (state_permute1 m) s (n - 1);
    unfold_repeati n Spec.state_permute1 (state_spec_v s).[l] (n - 1);
    state_permute1_lemma_l m (n - 1) lp0 l;
    () end

val state_permute_lemma_l:
  m:m_spec
  -> s:state_spec m
  -> l:nat{l < lanes m} ->
  Lemma ((state_spec_v (state_permute m s)).[l] ==
           Spec.state_permute (state_spec_v s).[l])

let state_permute_lemma_l m s l = state_permute_loop m s l 24

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

let load_blocks_lemma_ij #a #m b j i =
  let l = lanes m in
  let idx_i = i % l in
  let idx_j = i / l in

  let blocksize = word_length a in
  let blocksize_l = l * blocksize in
  let b_j = Seq.slice b.(|idx_i|) (idx_j * blocksize_l) (idx_j * blocksize_l + blocksize_l) in

  assert (vec_v ((load_blocks #a #m b).[i]) == BSeq.uints_from_bytes_le b_j);
  BSeq.index_uints_from_bytes_le #(word_t a) #SEC #(lanes m) b_j j;
  assert ((vec_v ((load_blocks #a #m b).[i])).[j] ==
    BSeq.uint_from_bytes_le (Seq.slice b_j (j * blocksize) (j * blocksize + blocksize)));

  calc (==) {
    idx_j * blocksize_l + j * blocksize;
    (==) { Math.Lemmas.paren_mul_right idx_j l blocksize;
      Math.Lemmas.distributivity_add_left (idx_j * l) j blocksize }
    (idx_j * l + j) * blocksize;
  };

  Seq.Properties.slice_slice b.(|idx_i|)
    (idx_j * blocksize_l) (idx_j * blocksize_l + blocksize_l)
    (j * blocksize) (j * blocksize + blocksize);

  assert ((vec_v ((load_blocks #a #m b).[i])).[j] ==
    BSeq.uint_from_bytes_le
      (Seq.slice b.(|idx_i|) ((idx_j * l + j) * blocksize)
        ((idx_j * l + j) * blocksize + blocksize)))

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

let load_blocks_lemma_ij_subst #a #m b j i =
  let l = lanes m in
  let i_new = i / l * l + j in
  let j_new = i % l in
  load_blocks_lemma_ij #a #m b j_new i_new;

  calc (==) {
    i_new % l;
    (==) { }
    (i / l * l + j) % l;
    (==) { Math.Lemmas.modulo_addition_lemma j l (i / l) }
    j % l;
    (==) { Math.Lemmas.small_mod j l }
    j;
    };

  calc (==) {
    i_new / l * l + j_new;
    (==) { }
    (i / l * l + j) / l * l + i % l;
    (==) { Math.Lemmas.division_addition_lemma j l (i / l) }
    (i / l + j / l) * l + i % l;
    (==) { Math.Lemmas.distributivity_add_left (i / l) (j / l) l }
    i / l * l + j / l * l + i % l;
    (==) { Math.Lemmas.euclidean_division_definition i l }
    i + j / l * l;
    (==) { Math.Lemmas.small_div j l }
    i;
    }

val load_ws_lemma_l:
    #a:keccak_alg
  -> #m:m_spec{is_supported m}
  -> b:multiblock_spec a m
  -> l:nat{l < lanes m}
  -> i:nat{i < 25} ->
  Lemma ((ws_spec_v (load_ws b)).[l].[i] == BSeq.uint_from_bytes_le
      (Seq.slice (Seq.slice b.(|l|) 0 200) (i * word_length a) (i * word_length a + word_length a)))

let load_ws_lemma_l #a #m b l i =
  assert (Seq.slice (Seq.slice b.(|l|) 0 200) (i * word_length a) (i * word_length a + word_length a) ==
    Seq.slice b.(|l|) (i * word_length a) (i * word_length a + word_length a));
  Lemmas.transpose_ws_lemma_ij (load_blocks #a #m b) l i;
  load_blocks_lemma_ij_subst #a #m b l i

val loadState_inner_lemma_l:
    #a:keccak_alg
  -> #m:m_spec{is_supported m}
  -> b:multiblock_spec a m
  -> s:state_spec m
  -> l:nat{l < lanes m}
  -> i:nat{i < 25} ->
  Lemma ((state_spec_v (loadState_inner m (load_ws b) i s)).[l] ==
    Spec.loadState_inner (Seq.slice b.(|l|) 0 200) i (state_spec_v s).[l])

let loadState_inner_lemma_l #a #m b s l i =
  load_ws_lemma_l #a #m b l i;
  eq_intro (state_spec_v (loadState_inner m (load_ws #a #m b) i s)).[l]
    (Spec.loadState_inner (Seq.slice b.(|l|) 0 200) i (state_spec_v s).[l])

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

let rec loadState_loop_full #a #m r b s l n =
  if n = 0 then begin
    eq_repeati0 n (loadState_inner m (load_ws b)) s;
    eq_repeati0 n (Spec.loadState_inner (Seq.slice b.(|l|) 0 200))
      (state_spec_v s).[l];
    () end
  else begin
    let lp0 = repeati (n - 1) (loadState_inner m (load_ws b)) s in
    loadState_loop_full #a #m r b s l (n - 1);
    unfold_repeati n (loadState_inner m (load_ws b)) s (n - 1);
    unfold_repeati n (Spec.loadState_inner (Seq.slice b.(|l|) 0 200))
      (state_spec_v s).[l] (n - 1);
    loadState_inner_lemma_l #a #m b lp0 l (n - 1);
    () end

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

let update_sub_b_lemma #a #m r b l =
  assert (forall j. (j >= 0 /\ j < r) ==>
    Seq.index (Seq.slice b.(|l|) 0 200) j == Seq.index (Seq.slice b.(|l|) 0 r) j);
  eq_intro (Seq.slice b.(|l|) 0 200) (update_sub (create 200 (u8 0)) 0 r (Seq.slice b.(|l|) 0 r))

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

let loadState_loop #a #m r b s l n =
  loadState_loop_full #a #m r b s l n;
  update_sub_b_lemma #a #m r b l

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

let loadState_lemma_l  #a #m r b s l = loadState_loop #a #m r b s l 25

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

let storeState_lemma_ij #a #m s j i =
  let ws = create 32 (zero_element m) in
  let ws = update_sub ws 0 25 s in
  let ws1 = transpose_s_ws ws in
  let j_v = j * (32 * word_length a) + i in
  let blocksize_v = word_length a * lanes m in

  calc (==) { // j_v % blocksize_v / word_length a
    (j * (32 * word_length a) + i) % blocksize_v / word_length a;
    (==) { Math.Lemmas.modulo_division_lemma (j * (32 * word_length a) + i) (word_length a) (lanes m) }
    (j * (32 * word_length a) + i) / word_length a % lanes m;
    (==) { Math.Lemmas.paren_mul_right j 32 (word_length a);
           Math.Lemmas.division_addition_lemma i (word_length a) (32 * j) }
    (32 * j + i / word_length a) % lanes m;
    };

  calc (==) { // j_v / blocksize_v
    (j * (32 * word_length a) + i) / (word_length a * lanes m);
    (==) { Math.Lemmas.division_multiplication_lemma (j * (32 * word_length a) + i) (word_length a) (lanes m) }
    (j * (32 * word_length a) + i) / word_length a / lanes m;
    (==) { Math.Lemmas.paren_mul_right j 32 (word_length a);
           Math.Lemmas.division_addition_lemma i (word_length a) (32 * j) }
    (32 * j + i / word_length a) / lanes m;
    };

  calc (==) {
    Seq.index (storeState #a #m s) j_v;
    (==) { index_vecs_to_bytes_le #(word_t a) #(lanes m) #32 ws1 j_v }
    (BSeq.uints_to_bytes_le (vec_v ws1.[j_v / blocksize_v])).[j_v % blocksize_v];
    (==) { BSeq.index_uints_to_bytes_le (vec_v ws1.[j_v / blocksize_v]) (j_v % blocksize_v) }
    (BSeq.uint_to_bytes_le
      (Seq.index (vec_v ws1.[j_v / blocksize_v]) (j_v % blocksize_v / word_length a))).[(j_v % blocksize_v) % word_length a];
    (==) { Math.Lemmas.modulo_modulo_lemma j_v (word_length a) (lanes m) }
    (BSeq.uint_to_bytes_le
      (Seq.index (vec_v ws1.[j_v / blocksize_v]) (j_v % blocksize_v / word_length a))).[j_v % word_length a];
    (==) { Lemmas.transpose_s_lemma_ij #a #m ws j i }
    (BSeq.uint_to_bytes_le (Seq.index (ws_spec_v ws).[j] (i / word_length a))).[j_v % word_length a];
    (==) { Math.Lemmas.paren_mul_right j 32 (word_length a);
           Math.Lemmas.modulo_addition_lemma i (word_length a) (j * 32) }
    (BSeq.uint_to_bytes_le (Seq.index (ws_spec_v ws).[j] (i / word_length a))).[i % word_length a];
    (==) { }
    (BSeq.uint_to_bytes_le (Seq.index (state_spec_v s).[j] (i / word_length a))).[i % word_length a];
    }

val storeState_lemma_ij_sub:
    #a:keccak_alg
  -> #m:m_spec{is_supported m}
  -> s:state_spec m
  -> block:Lib.ByteSequence.lbytes 200
  -> j:nat{j < lanes m}
  -> i:nat{i < 25} ->
  Lemma
   (sub (sub (storeState #a #m s) (j * (32 * word_length a)) (25 * word_length a)) (i * word_length a) (word_length a) ==
      sub (Spec.storeState_inner (state_spec_v s).[j] i block) (i * word_length a) (word_length a))

let storeState_lemma_ij_sub #a #m s block j i =
  let aux (k:nat{k < word_length a}) : Lemma (
      (sub (storeState #a #m s) (j * (32 * word_length a)) (25 * word_length a)).[i * word_length a + k] ==
        (Spec.storeState_inner (state_spec_v s).[j] i block).[i * word_length a + k]) =
    storeState_lemma_ij #a #m s j (i * word_length a + k) in

  Classical.forall_intro aux;
  eq_intro
    (sub (sub (storeState #a #m s) (j * (32 * word_length a)) (25 * word_length a)) (i * word_length a) (word_length a))
    (sub (Spec.storeState_inner (state_spec_v s).[j] i block) (i * word_length a) (word_length a))

val storeState_loop:
    #a:keccak_alg
  -> #m:m_spec{is_supported m}
  -> s:state_spec m
  -> l:nat{l < lanes m}
  -> n:nat{n <= 25} ->
  Lemma
   (sub (storeState #a #m s) (l * (32 * word_length a)) (25 * word_length a) ==
     repeati n (Spec.storeState_inner (state_spec_v s).[l]) (create 200 (u8 0)))

let rec storeState_loop #a #m s l n =
  let lp = repeati n (Spec.storeState_inner (state_spec_v s).[l]) (create 200 (u8 0)) in
  
  if n = 0 then begin
    eq_repeati0 n (Spec.storeState_inner (state_spec_v s).[l])
      (create 200 (u8 0));
    () end
  else begin
    let lp0 = repeati (n - 1) (Spec.storeState_inner (state_spec_v s).[l]) (create 200 (u8 0)) in
    storeState_loop #a #m s l (n - 1);
    unfold_repeati n (Spec.storeState_inner (state_spec_v s).[l])
      (create 200 (u8 0)) (n - 1);
    storeState_lemma_ij_sub #a #m s lp0 l (n - 1);
    assert (lp == (Spec.storeState_inner (state_spec_v s).[l]) (n - 1) lp0);
    () end; admit()

val storeState_lemma_l:
  #a:keccak_alg
  -> #m:m_spec{is_supported m}
  -> r:size_nat{r > 0 /\ r <= 200}
  -> s:state_spec m
  -> l:nat{l < lanes m} ->
  Lemma
   (sub (storeState #a #m s) (l * (32 * word_length a)) r ==
     Spec.storeState r (state_spec_v s).[l])

let storeState_lemma_l  #a #m r s l =
  storeState_loop #a #m s l 25

(* absorb_next *)

val next_block_lemma_l:
  #m:m_spec{is_supported m}
  -> r:size_nat{r > 0 /\ r <= 200}
  -> l:nat{l < lanes m} ->
  Lemma
   (sub #uint8 #256 ((next_block #m r (next_block_seq_zero m)).(|l|)) 0 r ==
    ((create r (u8 0)).[r - 1] <- u8 0x80))

let next_block_lemma_l #m r l =
  eq_intro (sub #uint8 #256 ((next_block #m r (next_block_seq_zero m)).(|l|)) 0 r)
    ((create r (u8 0)).[r - 1] <- u8 0x80)

val absorb_next_lemma_l:
  #a:keccak_alg
  -> #m:m_spec{is_supported m}
  -> r:size_nat{r > 0 /\ r <= 200}
  -> s:state_spec m
  -> l:nat{l < lanes m} ->
  Lemma
   ((state_spec_v (absorb_next #a #m r s)).[l] ==
    Spec.absorb_next (state_spec_v s).[l] r)

let absorb_next_lemma_l  #a #m r s l =
  next_block_lemma_l #m r l;
  let b = next_block #m r (next_block_seq_zero m) in
  loadState_lemma_l #a #m r b s l;
  let s = loadState #a #m r b s in
  state_permute_lemma_l m s l

(* absorb_last *)

val load_last_block_lemma_helper:
  #m:m_spec{is_supported m}
  -> delimitedSuffix:byte_t
  -> r:size_nat{r > 0 /\ r <= 200}
  -> rem:size_nat{rem < r}
  -> input:Lib.ByteSequence.lbytes rem ->
  Lemma(let b_0 = update_sub (create r (u8 0)) 0 rem input in
        let b = b_0.[rem] <- byte_to_uint8 delimitedSuffix in
        (forall i. (i >= 0 /\ i < rem) ==> Seq.index b i == Seq.index input i) /\
        Seq.index b rem == byte_to_uint8 delimitedSuffix /\
        (forall i. (i >= (rem + 1) /\ i < r) ==> Seq.index b i == u8 0))

let load_last_block_lemma_helper #m delimitedSuffix r rem input = 
  let b_0 = update_sub (create r (u8 0)) 0 rem input in
  let b = b_0.[rem] <- byte_to_uint8 delimitedSuffix in
  eq_intro (slice #uint8 #r b_0 (rem + 1) r)
        (create (r - (rem + 1)) (u8 0));
  assert (forall j. (j >= 0 /\ j < (r - (rem + 1))) ==> 
        Seq.index (slice #uint8 #r b (rem + 1) r) j ==
          Seq.index b ((rem + 1) + j));
  assert (forall j. (j >= (rem + 1) /\ j < r) ==> (j - (rem + 1) >= 0))

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

let load_last_block_lemma_l #m delimitedSuffix r rem input l =
  let b = update_sub (create r (u8 0)) 0 rem (sub #uint8 #256 input.(|l|) 0 rem) in
  load_last_block_lemma_helper #m delimitedSuffix r rem (sub #uint8 #256 input.(|l|) 0 rem);
  eq_intro (sub #uint8 #256 ((load_last_block #m r rem delimitedSuffix input).(|l|)) 0 r)
    (b.[rem] <- byte_to_uint8 delimitedSuffix)

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

let absorb_last_lemma_l #a #m delimitedSuffix r rem input s l =
  load_last_block_lemma_l #m delimitedSuffix r rem input l;
  let lastBlock = load_last_block #m r rem delimitedSuffix input in
  loadState_lemma_l #a #m r lastBlock s l;
  let s = loadState #a #m r lastBlock s in
  let s =
    if not ((delimitedSuffix &. byte 0x80) =. byte 0) &&
       (rem = r - 1)
    then (state_permute_lemma_l m s l; state_permute m s) else s in
  absorb_next_lemma_l #a #m r s l

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

let absorb_inner_lemma_l #a #m r input s l =
  loadState_lemma_l #a #m r input s l;
  let s = loadState #a #m r input s in
  state_permute_lemma_l m s l
