module Hacl.Spec.K256.PrecompTable

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.K256.Field52.Definitions
open Hacl.Impl.K256.Point

module S = Spec.K256
module FL = FStar.List.Tot

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

unfold
let create5 (x0 x1 x2 x3 x4:uint64) : list uint64 = [x0; x1; x2; x3; x4]

inline_for_extraction noextract
let felem_list = x:list uint64{FL.length x == 5}
inline_for_extraction noextract
let point_list = x:list uint64{FL.length x == 15}

inline_for_extraction noextract
let felem_to_list (x:S.felem) : felem_list =
  [@inline_let] let x0 = x % pow52 in
  [@inline_let] let x1 = x / pow52 % pow52 in
  [@inline_let] let x2 = x / pow104 % pow52 in
  [@inline_let] let x3 = x / pow156 % pow52 in
  [@inline_let] let x4 = x / pow208 in
  [@inline_let] let r = create5 (u64 x0) (u64 x1) (u64 x2) (u64 x3) (u64 x4) in
  assert_norm (FL.length r = 5);
  r

inline_for_extraction noextract
let proj_point_to_list (p:S.proj_point) : point_list =
  [@inline_let] let (px, py, pz) = p in
  FL.(felem_to_list px @ felem_to_list py @ felem_to_list pz)

inline_for_extraction noextract
let point_inv_list (p:point_list) =
  let x = Seq.seq_of_list p <: lseq uint64 15 in
  point_inv_lseq x

noextract
let point_eval_list (p:point_list) : GTot S.proj_point =
  let x = Seq.seq_of_list p <: lseq uint64 15 in
  point_eval_lseq x

val proj_point_to_list_lemma: p:S.proj_point ->
  Lemma (point_inv_list (proj_point_to_list p) /\ point_eval_list (proj_point_to_list p) == p)
