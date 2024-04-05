module Hacl.Spec.SHA3.Equiv

open FStar.Mul
open Lib.Sequence
open Lib.IntVector.Serialize
open Lib.LoopCombinators

open Spec.Hash.Definitions
open Hacl.Spec.SHA3.Vec
module Spec = Spec.SHA3
module BSeq = Lib.ByteSequence
module Lemmas = Hacl.Spec.SHA3.Lemmas

friend Hacl.Impl.SHA3.Vec

#set-options "--z3rlimit 120 --fuel 0 --ifuel 0"

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

#push-options "--max_ifuel 1"
let state_chi_inner0_lemma_l m s_pi_rho y x s l =
  eq_intro (state_spec_v (state_chi_inner0 m s_pi_rho y x s)).[l]
    (Spec.state_chi_inner0 (state_spec_v s_pi_rho).[l] y x (state_spec_v s).[l])
#pop-options

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
    #m:m_spec
  -> b:multiblock_spec m
  -> j:nat{j < lanes m}
  -> i:nat{i < 32} ->
  Lemma (let l = lanes m in
    let ind = (i / l * l + j) * 8 in
    (vec_v (load_blocks b).[i]).[j] ==
    BSeq.uint_from_bytes_le
      (Seq.slice b.(|i % l|) ind (ind + 8)))

let load_blocks_lemma_ij #m b j i =
  let l = lanes m in
  let idx_i = i % l in
  let idx_j = i / l in

  let blocksize = 8 in
  let blocksize_l = l * blocksize in
  let b_j = Seq.slice b.(|idx_i|) (idx_j * blocksize_l) (idx_j * blocksize_l + blocksize_l) in

  assert (vec_v ((load_blocks #m b).[i]) == BSeq.uints_from_bytes_le b_j);
  BSeq.index_uints_from_bytes_le #U64 #SEC #(lanes m) b_j j;
  assert ((vec_v ((load_blocks #m b).[i])).[j] ==
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

  assert ((vec_v ((load_blocks #m b).[i])).[j] ==
    BSeq.uint_from_bytes_le
      (Seq.slice b.(|idx_i|) ((idx_j * l + j) * blocksize)
        ((idx_j * l + j) * blocksize + blocksize)))

val load_blocks_lemma_ij_subst:
    #m:m_spec
  -> b:multiblock_spec m
  -> j:nat{j < lanes m}
  -> i:nat{i < 32} ->
  Lemma (let l = lanes m in
    (vec_v (load_blocks b).[i / l * l + j]).[i % l] ==
    BSeq.uint_from_bytes_le
      (Seq.slice b.(|j|) (i * 8) (i * 8 + 8)))

let load_blocks_lemma_ij_subst #m b j i =
  let l = lanes m in
  let i_new = i / l * l + j in
  let j_new = i % l in
  load_blocks_lemma_ij #m b j_new i_new;

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
    #m:m_spec{is_supported m}
  -> b:multiblock_spec m
  -> l:nat{l < lanes m}
  -> i:nat{i < 25} ->
  Lemma ((ws_spec_v (load_ws b)).[l].[i] == BSeq.uint_from_bytes_le
      (Seq.slice (Seq.slice b.(|l|) 0 200) (i * 8) (i * 8 + 8)))

let load_ws_lemma_l #m b l i =
  assert (Seq.slice (Seq.slice b.(|l|) 0 200) (i * 8) (i * 8 + 8) ==
    Seq.slice b.(|l|) (i * 8) (i * 8 + 8));
  Lemmas.transpose_ws_lemma_ij (load_blocks #m b) l i;
  load_blocks_lemma_ij_subst #m b l i

val loadState_inner_lemma_l:
    #m:m_spec{is_supported m}
  -> b:multiblock_spec m
  -> s:state_spec m
  -> l:nat{l < lanes m}
  -> i:nat{i < 25} ->
  Lemma ((state_spec_v (loadState_inner m (load_ws b) i s)).[l] ==
    Spec.loadState_inner (Seq.slice b.(|l|) 0 200) i (state_spec_v s).[l])

let loadState_inner_lemma_l #m b s l i =
  load_ws_lemma_l #m b l i;
  eq_intro (state_spec_v (loadState_inner m (load_ws #m b) i s)).[l]
    (Spec.loadState_inner (Seq.slice b.(|l|) 0 200) i (state_spec_v s).[l])

val loadState_loop_full:
  #m:m_spec{is_supported m}
  -> r:size_nat{r > 0 /\ r <= 200}
  -> b:multiblock_spec m
  -> s:state_spec m
  -> l:nat{l < lanes m}
  -> n:nat{n <= 25} ->
  Lemma
  ((state_spec_v (repeati n (loadState_inner m (load_ws b)) s)).[l] ==
    repeati n (Spec.loadState_inner (Seq.slice b.(|l|) 0 200))
      (state_spec_v s).[l])

let rec loadState_loop_full #m r b s l n =
  if n = 0 then begin
    eq_repeati0 n (loadState_inner m (load_ws b)) s;
    eq_repeati0 n (Spec.loadState_inner (Seq.slice b.(|l|) 0 200))
      (state_spec_v s).[l];
    () end
  else begin
    let lp0 = repeati (n - 1) (loadState_inner m (load_ws b)) s in
    loadState_loop_full #m r b s l (n - 1);
    unfold_repeati n (loadState_inner m (load_ws b)) s (n - 1);
    unfold_repeati n (Spec.loadState_inner (Seq.slice b.(|l|) 0 200))
      (state_spec_v s).[l] (n - 1);
    loadState_inner_lemma_l #m b lp0 l (n - 1);
    () end

val update_sub_b_lemma:
    #m:m_spec{is_supported m}
  -> r:size_nat{r > 0 /\ r <= 200}
  -> b:multiblock_spec m
  -> l:nat{l < lanes m} ->
  Lemma
  (requires
    forall l. l < lanes m ==> (forall j. (j >= r /\ j < 256) ==> Seq.index b.(|l|) j == u8 0))
  (ensures
    Seq.slice b.(|l|) 0 200 == update_sub (create 200 (u8 0)) 0 r (Seq.slice b.(|l|) 0 r))

let update_sub_b_lemma #m r b l =
  assert (forall j. (j >= 0 /\ j < r) ==>
    Seq.index (Seq.slice b.(|l|) 0 200) j == Seq.index (Seq.slice b.(|l|) 0 r) j);
  eq_intro (Seq.slice b.(|l|) 0 200) (update_sub (create 200 (u8 0)) 0 r (Seq.slice b.(|l|) 0 r))

val loadState_loop:
    #m:m_spec{is_supported m}
  -> r:size_nat{r > 0 /\ r <= 200}
  -> b:multiblock_spec m
  -> s:state_spec m
  -> l:nat{l < lanes m}
  -> n:nat{n <= 25} ->
  Lemma
  (requires
    forall l. l < lanes m ==> (forall j. (j >= r /\ j < 256) ==> Seq.index b.(|l|) j == u8 0))
  (ensures (let bs = update_sub (create 200 (u8 0)) 0 r (Seq.slice b.(|l|) 0 r) in
    (state_spec_v (repeati n (loadState_inner m (load_ws b)) s)).[l] ==
      repeati n (Spec.loadState_inner bs) (state_spec_v s).[l]))

let loadState_loop #m r b s l n =
  loadState_loop_full #m r b s l n;
  update_sub_b_lemma #m r b l

val loadState_lemma_l:
  #m:m_spec{is_supported m}
  -> r:size_nat{r > 0 /\ r <= 200}
  -> b:multiblock_spec m
  -> s:state_spec m
  -> l:nat{l < lanes m} ->
  Lemma
  (requires
    forall l. l < lanes m ==> (forall j. (j >= r /\ j < 256) ==> Seq.index b.(|l|) j == u8 0))
  (ensures 
    (state_spec_v (loadState #m r b s)).[l] ==
      Spec.loadState r (Seq.slice b.(|l|) 0 r) (state_spec_v s).[l])

let loadState_lemma_l  #m r b s l = loadState_loop #m r b s l 25

(* storeState *)

val storeState_lemma_ij:
    #m:m_spec{is_supported m}
  -> s:state_spec m
  -> j:nat{j < lanes m}
  -> i:nat{i < 25 * 8} ->
  Lemma
   ((storeState #m s).[j * (32 * 8) + i] ==
      (BSeq.uint_to_bytes_le (Seq.index (state_spec_v s).[j] (i / 8))).[i % 8])

let storeState_lemma_ij #m s j i =
  let ws = create 32 (zero_element m) in
  let ws = update_sub ws 0 25 s in
  let ws1 = transpose_s_ws ws in
  let j_v = j * (32 * 8) + i in
  let blocksize_v = 8 * lanes m in

  calc (==) { // j_v % blocksize_v / 8
    (j * (32 * 8) + i) % blocksize_v / 8;
    (==) { Math.Lemmas.modulo_division_lemma (j * (32 * 8) + i) 8 (lanes m) }
    (j * (32 * 8) + i) / 8 % lanes m;
    (==) { Math.Lemmas.paren_mul_right j 32 8;
           Math.Lemmas.division_addition_lemma i 8 (32 * j) }
    (32 * j + i / 8) % lanes m;
    };

  calc (==) { // j_v / blocksize_v
    (j * (32 * 8) + i) / (8 * lanes m);
    (==) { Math.Lemmas.division_multiplication_lemma (j * (32 * 8) + i) 8 (lanes m) }
    (j * (32 * 8) + i) / 8 / lanes m;
    (==) { Math.Lemmas.paren_mul_right j 32 8;
           Math.Lemmas.division_addition_lemma i 8 (32 * j) }
    (32 * j + i / 8) / lanes m;
    };

  calc (==) {
    Seq.index (storeState #m s) j_v;
    (==) { index_vecs_to_bytes_le #U64 #(lanes m) #32 ws1 j_v }
    (BSeq.uints_to_bytes_le (vec_v ws1.[j_v / blocksize_v])).[j_v % blocksize_v];
    (==) { BSeq.index_uints_to_bytes_le (vec_v ws1.[j_v / blocksize_v]) (j_v % blocksize_v) }
    (BSeq.uint_to_bytes_le
      (Seq.index (vec_v ws1.[j_v / blocksize_v]) (j_v % blocksize_v / 8))).[(j_v % blocksize_v) % 8];
    (==) { Math.Lemmas.modulo_modulo_lemma j_v 8 (lanes m) }
    (BSeq.uint_to_bytes_le
      (Seq.index (vec_v ws1.[j_v / blocksize_v]) (j_v % blocksize_v / 8))).[j_v % 8];
    (==) { Lemmas.transpose_s_lemma_ij #m ws j i }
    (BSeq.uint_to_bytes_le (Seq.index (ws_spec_v ws).[j] (i / 8))).[j_v % 8];
    (==) { Math.Lemmas.paren_mul_right j 32 8;
           Math.Lemmas.modulo_addition_lemma i 8 (j * 32) }
    (BSeq.uint_to_bytes_le (Seq.index (ws_spec_v ws).[j] (i / 8))).[i % 8];
    (==) { }
    (BSeq.uint_to_bytes_le (Seq.index (state_spec_v s).[j] (i / 8))).[i % 8];
    }

val storeState_lemma_ij_sub:
    #m:m_spec{is_supported m}
  -> s:state_spec m
  -> j:nat{j < lanes m}
  -> i:nat{i < 25} ->
  Lemma
   (sub (sub (storeState #m s) (j * (32 * 8)) (25 * 8)) (i * 8) 8 ==
      BSeq.uint_to_bytes_le (Seq.index (state_spec_v s).[j] i))

let storeState_lemma_ij_sub #m s j i =
  let aux (k:nat{k < 8}) : Lemma (
      (sub (storeState #m s) (j * (32 * 8)) (25 * 8)).[i * 8 + k] ==
        (BSeq.uint_to_bytes_le (Seq.index (state_spec_v s).[j] i)).[k]) =
    storeState_lemma_ij #m s j (i * 8 + k) in

  Classical.forall_intro aux;
  eq_intro
    (sub (sub (storeState #m s) (j * (32 * 8)) (25 * 8)) (i * 8) 8)
    (BSeq.uint_to_bytes_le (Seq.index (state_spec_v s).[j] i))

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

let storeState_inner_loop s =
  let block = create 200 (u8 0) in
  eq_repeati0 25 (Spec.storeState_inner s) block;
  unfold_repeati 25 (Spec.storeState_inner s) block 0;
  unfold_repeati 25 (Spec.storeState_inner s) block 1;
  unfold_repeati 25 (Spec.storeState_inner s) block 2;
  unfold_repeati 25 (Spec.storeState_inner s) block 3;
  unfold_repeati 25 (Spec.storeState_inner s) block 4;
  unfold_repeati 25 (Spec.storeState_inner s) block 5;
  unfold_repeati 25 (Spec.storeState_inner s) block 6;
  unfold_repeati 25 (Spec.storeState_inner s) block 7;
  unfold_repeati 25 (Spec.storeState_inner s) block 8;
  unfold_repeati 25 (Spec.storeState_inner s) block 9;
  unfold_repeati 25 (Spec.storeState_inner s) block 10;
  unfold_repeati 25 (Spec.storeState_inner s) block 11;
  unfold_repeati 25 (Spec.storeState_inner s) block 12;
  unfold_repeati 25 (Spec.storeState_inner s) block 13;
  unfold_repeati 25 (Spec.storeState_inner s) block 14;
  unfold_repeati 25 (Spec.storeState_inner s) block 15;
  unfold_repeati 25 (Spec.storeState_inner s) block 16;
  unfold_repeati 25 (Spec.storeState_inner s) block 17;
  unfold_repeati 25 (Spec.storeState_inner s) block 18;
  unfold_repeati 25 (Spec.storeState_inner s) block 19;
  unfold_repeati 25 (Spec.storeState_inner s) block 20;
  unfold_repeati 25 (Spec.storeState_inner s) block 21;
  unfold_repeati 25 (Spec.storeState_inner s) block 22;
  unfold_repeati 25 (Spec.storeState_inner s) block 23;
  unfold_repeati 25 (Spec.storeState_inner s) block 24

val storeState_inner_unroll_sub_0_6:
    #m:m_spec{is_supported m}
  -> s:Spec.state
  -> i:nat{i < 6} ->
  Lemma
   (sub (storeState_inner_unroll s) (i * 8) 8 ==
      BSeq.uint_to_bytes_le #U64 s.[i])

let storeState_inner_unroll_sub_0_6 #m s i =
  let b0 = Spec.storeState_inner s 0 (create 200 (u8 0)) in
  let b1 = Spec.storeState_inner s 1 b0 in
  let b2 = Spec.storeState_inner s 2 b1 in
  let b3 = Spec.storeState_inner s 3 b2 in
  let b4 = Spec.storeState_inner s 4 b3 in
  let b5 = Spec.storeState_inner s 5 b4 in
  let b6 = Spec.storeState_inner s 6 b5 in
  let b7 = Spec.storeState_inner s 7 b6 in
  let b8 = Spec.storeState_inner s 8 b7 in
  let b9 = Spec.storeState_inner s 9 b8 in
  let b10 = Spec.storeState_inner s 10 b9 in
  let b11 = Spec.storeState_inner s 11 b10 in
  let b12 = Spec.storeState_inner s 12 b11 in
  let b13 = Spec.storeState_inner s 13 b12 in
  let b14 = Spec.storeState_inner s 14 b13 in
  let b15 = Spec.storeState_inner s 15 b14 in
  let b16 = Spec.storeState_inner s 16 b15 in
  let b17 = Spec.storeState_inner s 17 b16 in
  let b18 = Spec.storeState_inner s 18 b17 in
  let b19 = Spec.storeState_inner s 19 b18 in
  let b20 = Spec.storeState_inner s 20 b19 in
  let b21 = Spec.storeState_inner s 21 b20 in
  let b22 = Spec.storeState_inner s 22 b21 in
  let b23 = Spec.storeState_inner s 23 b22 in
  let b24 = Spec.storeState_inner s 24 b23 in
  let block = storeState_inner_unroll s in
  //s.[0]
  eq_intro (sub b10 0 8) (BSeq.uint_to_bytes_le #U64 s.[0]);
  eq_intro (sub b20 0 8) (BSeq.uint_to_bytes_le #U64 s.[0]);
  eq_intro (sub block 0 8) (BSeq.uint_to_bytes_le #U64 s.[0]);
  //s.[1]
  eq_intro (sub b11 8 8) (BSeq.uint_to_bytes_le #U64 s.[1]);
  eq_intro (sub b21 8 8) (BSeq.uint_to_bytes_le #U64 s.[1]);
  eq_intro (sub block 8 8) (BSeq.uint_to_bytes_le #U64 s.[1]);
  //s.[2]
  eq_intro (sub b12 16 8) (BSeq.uint_to_bytes_le #U64 s.[2]);
  eq_intro (sub b22 16 8) (BSeq.uint_to_bytes_le #U64 s.[2]);
  eq_intro (sub block 16 8) (BSeq.uint_to_bytes_le #U64 s.[2]);
  //s.[3]
  eq_intro (sub b13 24 8) (BSeq.uint_to_bytes_le #U64 s.[3]);
  eq_intro (sub b23 24 8) (BSeq.uint_to_bytes_le #U64 s.[3]);
  eq_intro (sub block 24 8) (BSeq.uint_to_bytes_le #U64 s.[3]);
  //s.[4]
  eq_intro (sub b14 32 8) (BSeq.uint_to_bytes_le #U64 s.[4]);
  eq_intro (sub b24 32 8) (BSeq.uint_to_bytes_le #U64 s.[4]);
  eq_intro (sub block 32 8) (BSeq.uint_to_bytes_le #U64 s.[4]);
  //s.[5]
  eq_intro (sub b15 40 8) (BSeq.uint_to_bytes_le #U64 s.[5]);
  eq_intro (sub block 40 8) (BSeq.uint_to_bytes_le #U64 s.[5])

val storeState_inner_unroll_sub_6_12:
    #m:m_spec{is_supported m}
  -> s:Spec.state
  -> i:nat{i >= 6 /\ i < 12} ->
  Lemma
   (sub (storeState_inner_unroll s) (i * 8) 8 ==
      BSeq.uint_to_bytes_le #U64 s.[i])

let storeState_inner_unroll_sub_6_12 #m s i =
  let b0 = Spec.storeState_inner s 0 (create 200 (u8 0)) in
  let b1 = Spec.storeState_inner s 1 b0 in
  let b2 = Spec.storeState_inner s 2 b1 in
  let b3 = Spec.storeState_inner s 3 b2 in
  let b4 = Spec.storeState_inner s 4 b3 in
  let b5 = Spec.storeState_inner s 5 b4 in
  let b6 = Spec.storeState_inner s 6 b5 in
  let b7 = Spec.storeState_inner s 7 b6 in
  let b8 = Spec.storeState_inner s 8 b7 in
  let b9 = Spec.storeState_inner s 9 b8 in
  let b10 = Spec.storeState_inner s 10 b9 in
  let b11 = Spec.storeState_inner s 11 b10 in
  let b12 = Spec.storeState_inner s 12 b11 in
  let b13 = Spec.storeState_inner s 13 b12 in
  let b14 = Spec.storeState_inner s 14 b13 in
  let b15 = Spec.storeState_inner s 15 b14 in
  let b16 = Spec.storeState_inner s 16 b15 in
  let b17 = Spec.storeState_inner s 17 b16 in
  let b18 = Spec.storeState_inner s 18 b17 in
  let b19 = Spec.storeState_inner s 19 b18 in
  let b20 = Spec.storeState_inner s 20 b19 in
  let b21 = Spec.storeState_inner s 21 b20 in
  let b22 = Spec.storeState_inner s 22 b21 in
  let b23 = Spec.storeState_inner s 23 b22 in
  let b24 = Spec.storeState_inner s 24 b23 in
  let block = storeState_inner_unroll s in
  //s.[6]
  eq_intro (sub b16 48 8) (BSeq.uint_to_bytes_le #U64 s.[6]);
  eq_intro (sub block 48 8) (BSeq.uint_to_bytes_le #U64 s.[6]);
  //s.[7]
  eq_intro (sub b17 56 8) (BSeq.uint_to_bytes_le #U64 s.[7]);
  eq_intro (sub block 56 8) (BSeq.uint_to_bytes_le #U64 s.[7]);
  //s.[8]
  eq_intro (sub b18 64 8) (BSeq.uint_to_bytes_le #U64 s.[8]);
  eq_intro (sub block 64 8) (BSeq.uint_to_bytes_le #U64 s.[8]);
  //s.[9]
  eq_intro (sub b19 72 8) (BSeq.uint_to_bytes_le #U64 s.[9]);
  eq_intro (sub block 72 8) (BSeq.uint_to_bytes_le #U64 s.[9]);
  //s.[10]
  eq_intro (sub b20 80 8) (BSeq.uint_to_bytes_le #U64 s.[10]);
  eq_intro (sub block 80 8) (BSeq.uint_to_bytes_le #U64 s.[10]);
  //s.[11]
  eq_intro (sub b21 88 8) (BSeq.uint_to_bytes_le #U64 s.[11]);
  eq_intro (sub block 88 8) (BSeq.uint_to_bytes_le #U64 s.[11])

val storeState_inner_unroll_sub_12_18:
    #m:m_spec{is_supported m}
  -> s:Spec.state
  -> i:nat{i >= 12 /\ i < 18} ->
  Lemma
   (sub (storeState_inner_unroll s) (i * 8) 8 ==
      BSeq.uint_to_bytes_le #U64 s.[i])

let storeState_inner_unroll_sub_12_18 #m s i =
  let b0 = Spec.storeState_inner s 0 (create 200 (u8 0)) in
  let b1 = Spec.storeState_inner s 1 b0 in
  let b2 = Spec.storeState_inner s 2 b1 in
  let b3 = Spec.storeState_inner s 3 b2 in
  let b4 = Spec.storeState_inner s 4 b3 in
  let b5 = Spec.storeState_inner s 5 b4 in
  let b6 = Spec.storeState_inner s 6 b5 in
  let b7 = Spec.storeState_inner s 7 b6 in
  let b8 = Spec.storeState_inner s 8 b7 in
  let b9 = Spec.storeState_inner s 9 b8 in
  let b10 = Spec.storeState_inner s 10 b9 in
  let b11 = Spec.storeState_inner s 11 b10 in
  let b12 = Spec.storeState_inner s 12 b11 in
  let b13 = Spec.storeState_inner s 13 b12 in
  let b14 = Spec.storeState_inner s 14 b13 in
  let b15 = Spec.storeState_inner s 15 b14 in
  let b16 = Spec.storeState_inner s 16 b15 in
  let b17 = Spec.storeState_inner s 17 b16 in
  let b18 = Spec.storeState_inner s 18 b17 in
  let b19 = Spec.storeState_inner s 19 b18 in
  let b20 = Spec.storeState_inner s 20 b19 in
  let b21 = Spec.storeState_inner s 21 b20 in
  let b22 = Spec.storeState_inner s 22 b21 in
  let b23 = Spec.storeState_inner s 23 b22 in
  let b24 = Spec.storeState_inner s 24 b23 in
  let block = storeState_inner_unroll s in
  //s.[12]
  eq_intro (sub b22 96 8) (BSeq.uint_to_bytes_le #U64 s.[12]);
  eq_intro (sub block 96 8) (BSeq.uint_to_bytes_le #U64 s.[12]);
  //s.[13]
  eq_intro (sub b23 104 8) (BSeq.uint_to_bytes_le #U64 s.[13]);
  eq_intro (sub block 104 8) (BSeq.uint_to_bytes_le #U64 s.[13]);
  //s.[14]
  eq_intro (sub b24 112 8) (BSeq.uint_to_bytes_le #U64 s.[14]);
  eq_intro (sub block 112 8) (BSeq.uint_to_bytes_le #U64 s.[14]);
  //s.[15]
  eq_intro (sub block 120 8) (BSeq.uint_to_bytes_le #U64 s.[15]);
  //s.[16]
  eq_intro (sub block 128 8) (BSeq.uint_to_bytes_le #U64 s.[16]);
  //s.[17]
  eq_intro (sub block 136 8) (BSeq.uint_to_bytes_le #U64 s.[17])

val storeState_inner_unroll_sub_18_25:
    #m:m_spec{is_supported m}
  -> s:Spec.state
  -> i:nat{i >= 18 /\ i < 25} ->
  Lemma
   (sub (storeState_inner_unroll s) (i * 8) 8 ==
      BSeq.uint_to_bytes_le #U64 s.[i])

let storeState_inner_unroll_sub_18_25 #m s i =
  let block = storeState_inner_unroll s in
  //s.[18]
  eq_intro (sub block 144 8) (BSeq.uint_to_bytes_le #U64 s.[18]);
  //s.[19]
  eq_intro (sub block 152 8) (BSeq.uint_to_bytes_le #U64 s.[19]);
  //s.[20]
  eq_intro (sub block 160 8) (BSeq.uint_to_bytes_le #U64 s.[20]);
  //s.[21]
  eq_intro (sub block 168 8) (BSeq.uint_to_bytes_le #U64 s.[21]);
  //s.[22]
  eq_intro (sub block 176 8) (BSeq.uint_to_bytes_le #U64 s.[22]);
  //s.[23]
  eq_intro (sub block 184 8) (BSeq.uint_to_bytes_le #U64 s.[23]);
  //s.[24]
  eq_intro (sub block 192 8) (BSeq.uint_to_bytes_le #U64 s.[24])

val storeState_inner_unroll_sub:
    #m:m_spec{is_supported m}
  -> s:Spec.state
  -> i:nat{i < 25} ->
  Lemma
   (sub (storeState_inner_unroll s) (i * 8) 8 ==
      BSeq.uint_to_bytes_le #U64 s.[i])

let storeState_inner_unroll_sub #m s i =
  let aux_0_6 (j:nat{j < 6}) : Lemma (sub (storeState_inner_unroll s) (j * 8) 8 ==
      BSeq.uint_to_bytes_le #U64 s.[j]) =
    storeState_inner_unroll_sub_0_6 #m s j in
  let aux_6_12 (j:nat{j >= 6 /\ j < 12}) : Lemma (sub (storeState_inner_unroll s) (j * 8) 8 ==
      BSeq.uint_to_bytes_le #U64 s.[j]) =
    storeState_inner_unroll_sub_6_12 #m s j in
  let aux_12_18 (j:nat{j >= 12 /\ j < 18}) : Lemma (sub (storeState_inner_unroll s) (j * 8) 8 ==
      BSeq.uint_to_bytes_le #U64 s.[j]) =
    storeState_inner_unroll_sub_12_18 #m s j in
  let aux_18_25 (j:nat{j >= 18 /\ j < 25}) : Lemma (sub (storeState_inner_unroll s) (j * 8) 8 ==
      BSeq.uint_to_bytes_le #U64 s.[j]) =
    storeState_inner_unroll_sub_18_25 #m s j in

  Classical.forall_intro aux_0_6;
  Classical.forall_intro aux_6_12;
  Classical.forall_intro aux_12_18;
  Classical.forall_intro aux_18_25

val sub_word_length_lemma:
    l0:lseq uint8 (25 * 8)
  -> l1:lseq uint8 (25 * 8) ->
  Lemma
  (requires
    forall (i:nat{0 <= i /\ i < 25}).
    (forall (j:nat{0 <= j /\ j < 8}).
      Seq.index (sub l0 (i*8) 8) j ==
        Seq.index (sub l1 (i*8) 8) j))
  (ensures
    l0 == l1)

let sub_word_length_lemma l0 l1 =
  assert (forall (i:nat{0 <= i /\ i < 25}).
    (forall (j:nat{0 <= j /\ j < 8}).
      Seq.index (sub l0 (i*8) 8) j ==
        Seq.index (sub l1 (i*8) 8) j));
  assert (forall (i:nat{0 <= i /\ i < 25}).
    (forall (j:nat{0 <= j /\ j < 8}).
      Seq.index l0 ((i*8) + j) == Seq.index l1 ((i*8) + j)));
  assert (forall (i:nat{0 <= i /\ i < 25 * 8}).
      i == (i / 8) * 8 + i % 8);
  assert (forall (i:nat{0 <= i /\ i < 25 * 8}).
      Seq.index l0 i == Seq.index l1 i);
  eq_intro l0 l1

val storeState_lemma_l:
  #m:m_spec{is_supported m}
  -> r:size_nat{r <= 200}
  -> s:state_spec m
  -> l:nat{l < lanes m} ->
  Lemma
   (sub (storeState #m s) (l * (32 * 8)) r ==
     Spec.storeState r (state_spec_v s).[l])

let storeState_lemma_l  #m r s l =
  let l0 = sub (storeState #m s) (l * (32 * 8)) (25 * 8) in
  let l1 = storeState_inner_unroll (state_spec_v s).[l] in
  let aux (i:nat{i < 25}) : Lemma (sub l0 (i * 8) 8 ==
      sub l1 (i * 8) 8) =
    storeState_lemma_ij_sub #m s l i;
    storeState_inner_unroll_sub #m (state_spec_v s).[l] i in

  Classical.forall_intro aux;
  sub_word_length_lemma l0 l1;
  storeState_inner_loop (state_spec_v s).[l]

val storeState_update_b_lemma_l:
  #m:m_spec{is_supported m}
  -> r:size_nat{r > 0 /\ r <= 200}
  -> outputByteLen:size_nat
  -> i:size_nat{i < outputByteLen / r}
  -> b:multiseq (lanes m) outputByteLen
  -> s:state_spec m
  -> l:nat{l < lanes m} ->
  Lemma
   (let block = storeState #m s in
    let b' = update_b #m block r outputByteLen i b in
    i * r + r <= outputByteLen /\
    sub #uint8 #outputByteLen b'.(|l|) (i * r) r ==
     Spec.storeState r (state_spec_v s).[l] /\
    (forall j. (j < i * r /\ j >= i * r + r) ==>
      Seq.index b'.(|l|) j == Seq.index b.(|l|) j))

let storeState_update_b_lemma_l #m r outputByteLen i b s l =
  assert (i + 1 <= outputByteLen / r);
  assert ((i + 1) * r <= outputByteLen);
  assert (i * r + r <= outputByteLen);
  storeState_lemma_l #m r s l

val storeState_update_b_last_lemma_l:
  #m:m_spec{is_supported m}
  -> r:size_nat{r > 0 /\ r <= 200}
  -> outputByteLen:size_nat
  -> outRem:size_nat{outRem == outputByteLen % r}
  -> b:multiseq (lanes m) outputByteLen
  -> s:state_spec m
  -> l:nat{l < lanes m} ->
  Lemma
   (let block = storeState #m s in
    let b' = update_b_last #m block r outputByteLen outRem b in
    outRem <= outputByteLen /\
    sub #uint8 #outputByteLen b'.(|l|) (outputByteLen - outRem) outRem ==
     Spec.storeState outRem (state_spec_v s).[l] /\
    (forall i. (i < outputByteLen - outRem) ==>
      Seq.index b'.(|l|) i == Seq.index b.(|l|) i))

let storeState_update_b_last_lemma_l #m r outputByteLen outRem b s l =
  let block = storeState #m s in
  let b' = update_b_last #m block r outputByteLen outRem b in
  assert (outputByteLen >= 0);
  FStar.Math.Lemmas.lemma_mod_lt outputByteLen r;
  assert (outRem <= outputByteLen);
  eq_intro (sub #uint8 #outputByteLen b.(|l|) 0 (outputByteLen - outRem))
    (sub #uint8 #outputByteLen b'.(|l|) 0 (outputByteLen - outRem));
  assert (forall (i:nat). (i < outputByteLen - outRem) ==>
    Seq.index b.(|l|) i == Seq.index (sub #uint8 #outputByteLen b.(|l|) 0 (outputByteLen - outRem)) i);
  assert (forall (i:nat). (i < outputByteLen - outRem) ==>
    Seq.index b'.(|l|) i == Seq.index (sub #uint8 #outputByteLen b'.(|l|) 0 (outputByteLen - outRem)) i);
  assert (forall (i:nat). (i < outputByteLen - outRem) ==>
    Seq.index b'.(|l|) i == Seq.index b.(|l|) i);
  storeState_lemma_l #m outRem s l

(* absorb_inner *)

val absorb_inner_lemma_l:
  #m:m_spec{is_supported m}
  -> r:size_nat{r > 0 /\ r <= 200}
  -> input:multiseq (lanes m) 256{forall l. l < lanes m ==> 
     (forall i. (i >= r /\ i < 256) ==> Seq.index input.(|l|) i == u8 0)}
  -> s:state_spec m
  -> l:nat{l < lanes m} ->
  Lemma
   ((state_spec_v (absorb_inner #m r input s)).[l] ==
    Spec.absorb_inner r (sub #uint8 #256 input.(|l|) 0 r) (state_spec_v s).[l])

let absorb_inner_lemma_l #m r input s l =
  loadState_lemma_l #m r input s l;
  let s = loadState #m r input s in
  state_permute_lemma_l m s l

(* absorb_inner_block *)

val absorb_inner_block_lemma_l:
  #m:m_spec{is_supported m}
  -> r:size_nat{r > 0 /\ r <= 200}
  -> inputByteLen:nat
  -> input:multiseq (lanes m) inputByteLen
  -> i:nat{i < inputByteLen / r}
  -> s:state_spec m
  -> l:nat{l < lanes m} ->
  Lemma
   ((state_spec_v (absorb_inner_block #m r inputByteLen input i s)).[l] ==
    repeat_blocks_f r input.(|l|) (Spec.absorb_inner r) (inputByteLen / r) i (state_spec_v s).[l])

let absorb_inner_block_lemma_l #m r inputByteLen input i s l =
  assert (i * r >= 0);
  assert ((i+1) * r <= inputByteLen);
  let mb = get_multiblock_spec #m r inputByteLen input i in
  eq_intro (sub #uint8 #256 mb.(|l|) 0 r)
    (Seq.slice input.(|l|) (i * r) (i * r + r));
  absorb_inner_lemma_l #m r mb s l

(* absorb_inner_nblocks *)

val absorb_inner_loop:
  #m:m_spec{is_supported m}
  -> r:size_nat{r > 0 /\ r <= 200}
  -> inputByteLen:nat
  -> input:multiseq (lanes m) inputByteLen
  -> s:state_spec m
  -> l:nat{l < lanes m}
  -> n:nat{n <= inputByteLen / r} ->
  Lemma
   ((state_spec_v (repeati n (absorb_inner_block #m r inputByteLen input) s)).[l] ==
    repeati n (repeat_blocks_f r input.(|l|) (Spec.absorb_inner r) (inputByteLen / r)) (state_spec_v s).[l])

let rec absorb_inner_loop #m r inputByteLen input s l n =
  if n = 0 then begin
    eq_repeati0 n (absorb_inner_block #m r inputByteLen input) s;
    eq_repeati0 n (repeat_blocks_f r input.(|l|) (Spec.absorb_inner r) (inputByteLen / r)) (state_spec_v s).[l];
    () end
  else begin
    let lp0 = repeati (n - 1) (absorb_inner_block #m r inputByteLen input) s in
    absorb_inner_loop #m r inputByteLen input s l (n - 1);
    unfold_repeati n (absorb_inner_block #m r inputByteLen input) s (n - 1);
    unfold_repeati n (repeat_blocks_f r input.(|l|) (Spec.absorb_inner r) (inputByteLen / r)) (state_spec_v s).[l] (n - 1);
    absorb_inner_block_lemma_l #m r inputByteLen input (n - 1) lp0 l;
    () end

val absorb_inner_nblocks_lemma_l:
  #m:m_spec{is_supported m}
  -> r:size_nat{r > 0 /\ r <= 200}
  -> inputByteLen:nat
  -> input:multiseq (lanes m) inputByteLen
  -> s:state_spec m
  -> l:nat{l < lanes m} ->
  Lemma
   ((state_spec_v (absorb_inner_nblocks #m r inputByteLen input s)).[l] ==
    repeati (inputByteLen / r) (repeat_blocks_f r input.(|l|) (Spec.absorb_inner r) (inputByteLen / r)) (state_spec_v s).[l])

let absorb_inner_nblocks_lemma_l #m r inputByteLen input s l =
  absorb_inner_loop #m r inputByteLen input s l (inputByteLen / r)

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
  #m:m_spec{is_supported m}
  -> r:size_nat{r > 0 /\ r <= 200}
  -> s:state_spec m
  -> l:nat{l < lanes m} ->
  Lemma
   ((state_spec_v (absorb_next #m r s)).[l] ==
    Spec.absorb_next (state_spec_v s).[l] r)

let absorb_next_lemma_l  #m r s l =
  next_block_lemma_l #m r l;
  let b = next_block #m r (next_block_seq_zero m) in
  loadState_lemma_l #m r b s l;
  let s = loadState #m r b s in
  state_permute_lemma_l m s l

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
  #m:m_spec{is_supported m}
  -> delimitedSuffix:byte_t
  -> r:size_nat{r > 0 /\ r <= 200}
  -> rem:size_nat{rem < r}
  -> input:multiseq (lanes m) 256{forall l. l < lanes m ==> 
       (forall i. (i >= rem /\ i < 256) ==> Seq.index input.(|l|) i == u8 0)}
  -> s:state_spec m
  -> l:nat{l < lanes m} ->
  Lemma
   ((state_spec_v (absorb_last #m delimitedSuffix r rem input s)).[l] ==
    Spec.absorb_last delimitedSuffix r rem (sub #uint8 #256 input.(|l|) 0 rem) (state_spec_v s).[l])

let absorb_last_lemma_l #m delimitedSuffix r rem input s l =
  eq_lemma (delimitedSuffix &. byte 0x80) (byte 0);
  assert (((delimitedSuffix &. byte 0x80) =. byte 0) == (v (delimitedSuffix &. byte 0x80) = 0));
  logand_spec delimitedSuffix (byte 0x80);
  assert (v (delimitedSuffix &. byte 0x80) == UInt.logand #8 (v delimitedSuffix) 0x80);
  load_last_block_lemma_l #m delimitedSuffix r rem input l;
  let lastBlock = load_last_block #m r rem delimitedSuffix input in
  loadState_lemma_l #m r lastBlock s l;
  let s' = loadState #m r lastBlock s in
  let s' =
    if not ((delimitedSuffix &. byte 0x80) =. byte 0) &&
       (rem = r - 1)
    then (state_permute_lemma_l m s' l; state_permute m s') else s' in
  absorb_next_lemma_l #m r s' l;
  eq_intro (state_spec_v (absorb_last #m delimitedSuffix r rem input s)).[l]
    (Spec.absorb_last delimitedSuffix r rem (sub #uint8 #256 input.(|l|) 0 rem) (state_spec_v s).[l])

(* absorb_final *)

val absorb_final_lemma_l:
  #m:m_spec{is_supported m}
  -> delimitedSuffix:byte_t
  -> r:size_nat{r > 0 /\ r <= 200}
  -> inputByteLen:nat
  -> input:multiseq (lanes m) inputByteLen
  -> s:state_spec m
  -> l:nat{l < lanes m} ->
  Lemma
   (inputByteLen - (inputByteLen / r) * r <= inputByteLen /\
   (inputByteLen / r) * r == inputByteLen - (inputByteLen % r) /\
    (state_spec_v (absorb_final #m s r inputByteLen input delimitedSuffix)).[l] ==
      Spec.absorb_last delimitedSuffix r (inputByteLen % r)
        (Seq.slice input.(|l|) ((inputByteLen / r) * r) inputByteLen) (state_spec_v s).[l])

let absorb_final_lemma_l #m delimitedSuffix r inputByteLen input s l =
  let rem = inputByteLen % r in
  assert (inputByteLen - (inputByteLen / r) * r <= inputByteLen);
  assert ((inputByteLen / r) * r == inputByteLen - rem);
  let mb = get_multilast_spec #m r inputByteLen input in
  eq_intro (sub #uint8 #256 mb.(|l|) 0 rem)
    (Seq.slice input.(|l|) ((inputByteLen / r) * r) inputByteLen);
  absorb_last_lemma_l #m delimitedSuffix r rem mb s l

(* absorb *)

val absorb_lemma_l:
  #m:m_spec{is_supported m}
  -> s:state_spec m
  -> r:size_nat{r > 0 /\ r <= 200}
  -> inputByteLen:nat
  -> input:multiseq (lanes m) inputByteLen
  -> delimitedSuffix:byte_t
  -> l:nat{l < lanes m} ->
  Lemma
   ((state_spec_v (absorb #m s r inputByteLen input delimitedSuffix)).[l] ==
    Spec.absorb (state_spec_v s).[l] r inputByteLen input.(|l|) delimitedSuffix)

let absorb_lemma_l #m s r inputByteLen input delimitedSuffix l =
  lemma_repeat_blocks r input.(|l|) (Spec.absorb_inner r)
    (Spec.absorb_last delimitedSuffix r) (state_spec_v s).[l];
  absorb_inner_nblocks_lemma_l #m r inputByteLen input s l;
  let s' = absorb_inner_nblocks #m r inputByteLen input s in
  absorb_final_lemma_l #m delimitedSuffix r inputByteLen input s' l

(* squeeze_inner *)

val squeeze_inner_lemma_l:
  #m:m_spec{is_supported m}
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
    (let s', b' = squeeze_inner #m r outputByteLen i (s, b) in
    let s'_s, b'_s = Spec.squeeze_inner r outputByteLen i (state_spec_v s).[l] in
    (state_spec_v s').[l] == s'_s /\ i * r + r <= outputByteLen /\
    sub #uint8 #outputByteLen b'.(|l|) 0 (i * r + r) == Seq.append s_pre b'_s))

let squeeze_inner_lemma_l #m r outputByteLen i s b s_pre l =
  let s', b' = squeeze_inner #m r outputByteLen i (s, b) in
  let s'_s, b'_s = Spec.squeeze_inner r outputByteLen i (state_spec_v s).[l] in
  storeState_update_b_lemma_l #m r outputByteLen i b s l;
  state_permute_lemma_l m s l;
  eq_intro (sub #uint8 #outputByteLen b'.(|l|) 0 (i * r + r)) (Seq.append s_pre b'_s)

(* squeeze_nblocks *)

val lemma_generate_squeeze_inner_loop:
    #m:m_spec{is_supported m}
  -> r:size_nat{r > 0 /\ r <= 200}
  -> outputByteLen:size_nat
  -> n:nat{n <= outputByteLen}
  -> s:state_spec m
  -> b:multiseq (lanes m) outputByteLen
  -> l:nat{l < lanes m} -> Lemma
  (n / r <= outputByteLen / r /\
   (let c (i:nat{i <= outputByteLen / r}) = Spec.state in
   let (s1, out1) = generate_blocks r (outputByteLen / r) (n / r) c (Spec.squeeze_inner r outputByteLen) (state_spec_v s).[l] in
   let (s2, out2) = repeat_gen (n / r) (squeeze_s m r outputByteLen) (squeeze_inner #m r outputByteLen) (s, b) in
   (state_spec_v s2).[l] == (s1 <: Spec.state) /\ (n / r) * r <= outputByteLen /\
   sub #uint8 #outputByteLen out2.(|l|) 0 ((n / r) * r) == out1))

let rec lemma_generate_squeeze_inner_loop #m r outputByteLen n s b l =
  let k = n / r in
  let c (i:nat{i <= outputByteLen / r}) = Spec.state in
  let (s1, out1) = generate_blocks r (outputByteLen / r) k c (Spec.squeeze_inner r outputByteLen) (state_spec_v s).[l] in
  assert (length out1 == k * r);
  assert ((n / r) * r <= outputByteLen);

  if k = 0 then begin
    eq_generate_blocks0 r (outputByteLen / r) c (Spec.squeeze_inner r outputByteLen) (state_spec_v s).[l];
    eq_repeat_gen0 k (squeeze_s m r outputByteLen) (squeeze_inner #m r outputByteLen) (s, b) end
  else begin
    assert ((n - r) / r == (n - 1 * r) / r);
    Math.Lemmas.division_sub_lemma n r 1;
    assert ((n - r) / r == k - 1);
    Math.Lemmas.distributivity_sub_left k 1 r;
    assert ((k - 1) * r == k * r - r);
    assert ((k - 1) * r + r == k * r);
    assert (n - r <= outputByteLen);
    assert (k * r - r <= outputByteLen);
    lemma_generate_squeeze_inner_loop #m r outputByteLen (n - r) s b l;
    let (_, out3) = generate_blocks r (outputByteLen / r) (k - 1) c (Spec.squeeze_inner r outputByteLen) (state_spec_v s).[l] in
    let (s4, out4) = repeat_gen (k - 1) (squeeze_s m r outputByteLen) (squeeze_inner #m r outputByteLen) (s, b) in
    unfold_generate_blocks r (outputByteLen / r) c (Spec.squeeze_inner r outputByteLen) (state_spec_v s).[l] (k - 1);
    unfold_repeat_gen k (squeeze_s m r outputByteLen) (squeeze_inner #m r outputByteLen) (s, b) (k - 1);
    squeeze_inner_lemma_l #m r outputByteLen (k - 1) s4 out4 out3 l;
    () end

val squeeze_nblocks_lemma_l:
    #m:m_spec{is_supported m}
  -> r:size_nat{r > 0 /\ r <= 200}
  -> outputByteLen:size_nat
  -> s:state_spec m
  -> b:multiseq (lanes m) outputByteLen
  -> l:nat{l < lanes m} -> Lemma
  (let c (i:nat{i <= outputByteLen / r}) = Spec.state in
   let (s1, out1) = generate_blocks r (outputByteLen / r) (outputByteLen / r) c (Spec.squeeze_inner r outputByteLen) (state_spec_v s).[l] in
   let (s2, out2) = repeat_gen (outputByteLen / r) (squeeze_s m r outputByteLen) (squeeze_inner #m r outputByteLen) (s, b) in
   (state_spec_v s2).[l] == (s1 <: Spec.state) /\ (outputByteLen / r) * r <= outputByteLen /\
   sub #uint8 #outputByteLen out2.(|l|) 0 ((outputByteLen / r) * r) == out1)

let squeeze_nblocks_lemma_l #m r outputByteLen s b l =
  lemma_generate_squeeze_inner_loop #m r outputByteLen outputByteLen s b l

(* squeeze_last *)

val squeeze_last_lemma_l:
  #m:m_spec{is_supported m}
  -> r:size_nat{r > 0 /\ r <= 200}
  -> outputByteLen:size_nat
  -> s:state_spec m
  -> b:multiseq (lanes m) outputByteLen
  -> l:nat{l < lanes m} ->
  Lemma
   (let outRem = outputByteLen % r in
    let b' = squeeze_last #m s r outputByteLen b in
    let b'_s = Spec.storeState outRem (state_spec_v s).[l] in
    outRem <= outputByteLen /\
    sub #uint8 #outputByteLen b'.(|l|) (outputByteLen - outRem) outRem == b'_s /\
    (forall i. (i < outputByteLen - outRem) ==>
      Seq.index b'.(|l|) i == Seq.index b.(|l|) i))

let squeeze_last_lemma_l #m r outputByteLen s b l =
  storeState_update_b_last_lemma_l #m r outputByteLen (outputByteLen % r) b s l

(* squeeze *)

val squeeze_lemma_l:
  #m:m_spec{is_supported m}
  -> s:state_spec m
  -> r:size_nat{r > 0 /\ r <= 200}
  -> outputByteLen:size_nat
  -> b:multiseq (lanes m) outputByteLen
  -> l:nat{l < lanes m} ->
  Lemma
   ((squeeze #m s r outputByteLen b).(|l|) ==
      Spec.squeeze (state_spec_v s).[l] r outputByteLen)

let squeeze_lemma_l #m s r outputByteLen b l =
  assert ((outputByteLen / r) * r == outputByteLen - (outputByteLen % r));
  squeeze_nblocks_lemma_l #m r outputByteLen s b l;
  let s', b' = squeeze_nblocks #m r outputByteLen (s, b) in
  squeeze_last_lemma_l #m r outputByteLen s' b' l;
  eq_intro ((squeeze #m s r outputByteLen b).(|l|))
    (Spec.squeeze (state_spec_v s).[l] r outputByteLen)

(* keccak *)

val keccak_lemma_l:
  #m:m_spec{is_supported m}
  -> rate:size_nat{rate % 8 == 0 /\ rate / 8 > 0 /\ rate <= 1600}
  -> inputByteLen:nat
  -> input:multiseq (lanes m) inputByteLen
  -> delimitedSuffix:byte_t
  -> outputByteLen:size_nat
  -> b:multiseq (lanes m) outputByteLen
  -> l:nat{l < lanes m} ->
  Lemma
   ((keccak #m rate inputByteLen input delimitedSuffix outputByteLen b).(|l|) ==
      Spec.keccak rate (1600 - rate) inputByteLen input.(|l|) delimitedSuffix outputByteLen)

let keccak_lemma_l #m rate inputByteLen input delimitedSuffix outputByteLen b l =
  let r = rate / 8 in
  eq_intro (state_spec_v (create 25 (zero_element m))).[l] (create 25 (u64 0));
  let s = create 25 (zero_element m) in
  absorb_lemma_l #m s r inputByteLen input delimitedSuffix l;
  let s = absorb #m s r inputByteLen input delimitedSuffix in
  squeeze_lemma_l #m s r outputByteLen b l

(* shake128 *)

let shake128_lemma_l m inputByteLen input outputByteLen output l =
  keccak_lemma_l #m 1344 inputByteLen input (byte 0x1F) outputByteLen output l

(* shake256 *)

let shake256_lemma_l m inputByteLen input outputByteLen output l =
  keccak_lemma_l #m 1088 inputByteLen input (byte 0x1F) outputByteLen output l

(* sha3_224 *)

let sha3_224_lemma_l m inputByteLen input output l =
  keccak_lemma_l #m 1152 inputByteLen input (byte 0x06) 28 output l

(* sha3_256 *)

let sha3_256_lemma_l m inputByteLen input output l =
  keccak_lemma_l #m 1088 inputByteLen input (byte 0x06) 32 output l

(* sha3_384 *)

let sha3_384_lemma_l m inputByteLen input output l =
  keccak_lemma_l #m 832 inputByteLen input (byte 0x06) 48 output l

(* sha3_512 *)

let sha3_512_lemma_l m inputByteLen input output l =
  keccak_lemma_l #m 576 inputByteLen input (byte 0x06) 64 output l

(* Lemmas to prove functions in Hacl.Hash.SHA3 module *)

let absorb_inner_repeat_blocks_multi_lemma r inputByteLen input s =
  reveal_vec_1 U64;
  let aux_s (i:nat{i < 25}) : Lemma (s.[i] == (vec_v #U64 #1 s.[i]).[0]) =
    reveal_vec_v_1 #U64 s.[i] in
  let aux_n (i:nat{i < 25}) : Lemma ((absorb_inner_nblocks #M32 r inputByteLen input s).[i] == 
    ((vec_v (absorb_inner_nblocks #M32 r inputByteLen input s).[i]).[0] <: vec_t U64 1)) =
    reveal_vec_v_1 (absorb_inner_nblocks #M32 r inputByteLen input s).[i] in

  Classical.forall_intro aux_s;
  Classical.forall_intro aux_n;
  eq_intro ((state_spec_v #M32 s).[0]) s;
  eq_intro ((state_spec_v (absorb_inner_nblocks #M32 r inputByteLen input s)).[0])
    (absorb_inner_nblocks #M32 r inputByteLen input s);
  absorb_inner_nblocks_lemma_l #M32 r inputByteLen input s 0;
  lemma_repeat_blocks_multi r input.(|0|) (Spec.absorb_inner r) s

let absorb_inner_block_r_lemma r input s =
  reveal_vec_1 U64;
  let aux_s (i:nat{i < 25}) : Lemma (s.[i] == (vec_v #U64 #1 s.[i]).[0]) =
    reveal_vec_v_1 #U64 s.[i] in
  let aux_n (i:nat{i < 25}) : Lemma ((absorb_inner_block #M32 r r input 0 s).[i] == 
    ((vec_v (absorb_inner_block #M32 r r input 0 s).[i]).[0] <: vec_t U64 1)) =
    reveal_vec_v_1 (absorb_inner_block #M32 r r input 0 s).[i] in

  Classical.forall_intro aux_s;
  Classical.forall_intro aux_n;
  eq_intro ((state_spec_v #M32 s).[0]) s;
  eq_intro ((state_spec_v (absorb_inner_block #M32 r r input 0 s)).[0])
    (absorb_inner_block #M32 r r input 0 s);
  absorb_inner_block_lemma_l #M32 r r input 0 s 0

let absorb_last_r_lemma delimitedSuffix r inputByteLen input s =
  assert (inputByteLen / r == 0);
  assert (inputByteLen % r == inputByteLen);
  reveal_vec_1 U64;
  let aux_s (i:nat{i < 25}) : Lemma (s.[i] == (vec_v #U64 #1 s.[i]).[0]) =
    reveal_vec_v_1 #U64 s.[i] in
  let aux_n (i:nat{i < 25}) : Lemma
    ((absorb_final #M32 s r inputByteLen input delimitedSuffix).[i] == 
      ((vec_v (absorb_final #M32 s r inputByteLen input
      delimitedSuffix).[i]).[0] <: vec_t U64 1)) =
    reveal_vec_v_1 (absorb_final #M32 s r inputByteLen input delimitedSuffix).[i] in

  Classical.forall_intro aux_s;
  Classical.forall_intro aux_n;
  eq_intro ((state_spec_v #M32 s).[0]) s;
  eq_intro ((state_spec_v (absorb_final #M32 s r inputByteLen input delimitedSuffix)).[0])
    (absorb_final #M32 s r inputByteLen input delimitedSuffix);
  absorb_final_lemma_l #M32 delimitedSuffix r inputByteLen input s 0

let squeeze_s_lemma s r outputByteLen b =
  reveal_vec_1 U64;
  let aux_s (i:nat{i < 25}) : Lemma (s.[i] == (vec_v #U64 #1 s.[i]).[0]) =
    reveal_vec_v_1 #U64 s.[i] in

  Classical.forall_intro aux_s;
  eq_intro ((state_spec_v #M32 s).[0]) s;
  squeeze_lemma_l #M32 s r outputByteLen b 0
