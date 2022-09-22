module Hacl.Spec.K256.PrecompTable

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.K256.Field52.Definitions
open Hacl.Impl.K256.Point

module Loops = Lib.LoopCombinators
module S = Spec.K256
module SL = Spec.K256.Lemmas

module LE = Lib.Exponentiation
module SE = Spec.Exponentiation

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let precomp_basepoint_table_list: x:list uint64{List.Tot.length x = 240} =
  let open FStar.Tactics in
  _ by (exact (Meta.K256.PrecompTable.mk_list ()))

let precomp_basepoint_table_lseq: lseq uint64 240 =
  let open FStar.Tactics in
  _ by (exact (Meta.K256.PrecompTable.mk_lseq ()))

let pow_base_point (k:nat) =
  LE.pow S.mk_k256_comm_monoid (S.to_aff_point S.g) k

unfold
let precomp_table_inv (j:nat{j < 16}) =
  Math.Lemmas.lemma_mult_lt_right 15 j 16;
  Math.Lemmas.lemma_mult_le_right 15 (j + 1) 16;
  let bj = sub precomp_basepoint_table_lseq (j * 15) 15 in
  point_inv_lseq bj /\ S.to_aff_point (point_eval_lseq bj) == pow_base_point j

val precomp_basepoint_table_lemma: unit -> Lemma (forall (i:nat{i < 16}). precomp_table_inv i)
let precomp_basepoint_table_lemma () = admit()
