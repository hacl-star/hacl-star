module Lib.IntVector.Transpose

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.IntVector
open Lib.NTuple

#set-options "--z3rlimit 10 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
val transpose4x4: #t:v_inttype -> ntuple (vec_t t 4) 4 -> ntuple (vec_t t 4) 4

inline_for_extraction noextract
val transpose8x8: #t:v_inttype -> ntuple (vec_t t 8) 8 -> ntuple (vec_t t 8) 8

inline_for_extraction noextract
val transpose16x16: #t:v_inttype -> ntuple (vec_t t 16) 16 -> ntuple (vec_t t 16) 16


val transpose4x4_lemma: #t:v_inttype -> vs:ntuple (vec_t t 4) 4 ->
  Lemma (forall (i:nat{i < 4}) (j:nat{j < 4}). (vec_v (transpose4x4 vs).(|i|)).[j] == (vec_v vs.(|j|)).[i])

val transpose8x8_lemma: #t:v_inttype -> vs:ntuple (vec_t t 8) 8 ->
  Lemma (forall (i:nat{i < 8}) (j:nat{j < 8}). (vec_v (transpose8x8 vs).(|i|)).[j] == (vec_v vs.(|j|)).[i])

val transpose16x16_lemma: #t:v_inttype -> vs:ntuple (vec_t t 16) 16 ->
  Lemma (forall (i:nat{i < 16}) (j:nat{j < 16}). (vec_v (transpose16x16 vs).(|i|)).[j] == (vec_v vs.(|j|)).[i])
