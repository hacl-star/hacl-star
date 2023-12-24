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
