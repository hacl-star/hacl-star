module Lib.IntVector.Transpose

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.IntVector
open Lib.NTuple

#set-options "--z3rlimit 10 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
val transposewxw: #t:v_inttype -> #w:width -> ntuple (vec_t t w) w -> ntuple (vec_t t w) w

val transposewxw_lemma: #t:v_inttype -> #w:width -> vs:ntuple (vec_t t w) w ->
  Lemma (forall (i:nat{i < w}) (j:nat{j < w}). (vec_v (transposewxw vs).(|i|)).[j] == (vec_v vs.(|j|)).[i])
