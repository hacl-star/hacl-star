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

inline_for_extraction noextract
let felem_list = x:list uint64{List.Tot.length x == 5}
inline_for_extraction noextract
let point_list = x:list uint64{List.Tot.length x == 15}

inline_for_extraction noextract
let felem_to_list (x:S.felem) : felem_list =
  [@inline_let] let x0 = x % pow52 in
  [@inline_let] let x1 = x / pow52 % pow52 in
  [@inline_let] let x2 = x / pow104 % pow52 in
  [@inline_let] let x3 = x / pow156 % pow52 in
  [@inline_let] let x4 = x / pow208 % pow52 in
  [@inline_let] let r = [u64 x0; u64 x1; u64 x2; u64 x3; u64 x4] in
  assert_norm (List.Tot.length r = 5);
  r

inline_for_extraction noextract
let proj_point_to_list (p:S.proj_point) : point_list =
  [@inline_let] let (px, py, pz) = p in
  FStar.List.Tot.(felem_to_list px @ felem_to_list py @ felem_to_list pz)


inline_for_extraction noextract
let g_i_acc_t (i:nat) =
  S.proj_point & acc:list uint64{List.Tot.length acc == (i + 1) * 15}

inline_for_extraction noextract
val precomp_basepoint_table_f (i:nat) (g_i_acc: g_i_acc_t i) : g_i_acc_t (i + 1)
let precomp_basepoint_table_f i (g_i, acc) =
  let acc = FStar.List.Tot.(acc @ proj_point_to_list g_i) in
  let g_i = Spec.K256.point_add g_i S.g in
  g_i, acc


// == Loops.repeat_right
// val precomp_basepoint_table_list_rec (n:nat) (acc:g_i_acc_t 0) : Tot (g_i_acc_t n) (decreases n)
// let rec precomp_basepoint_table_list_rec n acc =
//   if n = 0 then acc
//   else precomp_basepoint_table_f (n - 1) (precomp_basepoint_table_list_rec (n - 1) acc)

// == Loops.repeat_left
val precomp_basepoint_table_list_rec
  (n:nat) (i:nat{i <= n}) (acc:g_i_acc_t i) : Tot (g_i_acc_t n) (decreases (n - i))
let rec precomp_basepoint_table_list_rec n i acc =
  if i = n then acc
  else precomp_basepoint_table_list_rec n (i + 1) (precomp_basepoint_table_f i acc)


let precomp_basepoint_table_list_aux : x:list uint64{List.Tot.length x = 240} =
  snd (precomp_basepoint_table_list_rec 15 0 (Spec.K256.g, proj_point_to_list S.point_at_inf))


unfold let precomp_basepoint_table_list: x:list uint64{List.Tot.length x = 240} =
  normalize_term (precomp_basepoint_table_list_aux)


let precomp_basepoint_table_lseq : lseq uint64 240 =
  assert_norm (List.Tot.length precomp_basepoint_table_list == 240);
  Seq.seq_of_list precomp_basepoint_table_list


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
