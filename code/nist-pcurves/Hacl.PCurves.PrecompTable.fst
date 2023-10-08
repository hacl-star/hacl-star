module Hacl.PCurves.PrecompTable

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence

module LE = Lib.Exponentiation
module SE = Spec.Exponentiation
module SPT = Hacl.Spec.PrecompBaseTable
module SPT256 = Hacl.Spec.PrecompBaseTable256
module SPTK = Hacl.Spec.PCurves.PrecompTable

module S = Spec.PCurves
module SL = Spec.PCurves.Lemmas

open Hacl.Impl.PCurves.Point
include Hacl.Impl.PCurves.Group

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let proj_point_to_list {| cp:S.curve_params |} p =
  SPTK.proj_point_to_list_lemma p;
  SPTK.proj_point_to_list p

let lemma_refl {| cp:S.curve_params |} x =
  SPTK.proj_point_to_list_lemma x

//-----------------

inline_for_extraction noextract
let proj_g_pow2_64_list {| S.curve_params |} {| precomp_g_points |} : SPTK.point_list =
  normalize_term (SPTK.proj_point_to_list proj_g_pow2_64)

inline_for_extraction noextract
let proj_g_pow2_128_list {| S.curve_params |} {| precomp_g_points |} : SPTK.point_list =
  normalize_term (SPTK.proj_point_to_list proj_g_pow2_128)

inline_for_extraction noextract
let proj_g_pow2_192_list {| S.curve_params |} {| precomp_g_points |} : SPTK.point_list =
  normalize_term (SPTK.proj_point_to_list proj_g_pow2_192)

let proj_g_pow2_64_lseq {| cp:S.curve_params |} {| p:precomp_g_points |} : LSeq.lseq uint64 (3 * v S.bn_limbs) =
  normalize_term_spec (SPTK.proj_point_to_list proj_g_pow2_64);
  Seq.seq_of_list (proj_g_pow2_64_list #cp #p)

let proj_g_pow2_128_lseq {| cp:S.curve_params |} {| p:precomp_g_points |} : LSeq.lseq uint64 (3 * v cp.bn_limbs)  =
  normalize_term_spec (SPTK.proj_point_to_list proj_g_pow2_128);
  Seq.seq_of_list proj_g_pow2_128_list

let proj_g_pow2_192_lseq {| cp:S.curve_params |} {| p:precomp_g_points |} : LSeq.lseq uint64 (3 * v cp.bn_limbs) =
  normalize_term_spec (SPTK.proj_point_to_list proj_g_pow2_192);
  Seq.seq_of_list proj_g_pow2_192_list

let proj_g_pow2_64_lemma {| cp:S.curve_params |} {| p:precomp_g_points |} () =
  p.lemma_proj_g_pow2_64_eval ();
  SPT256.a_pow2_64_lemma S.mk_pcurve_concrete_ops S.base_point

let proj_g_pow2_128_lemma {| cp:S.curve_params |} {| p:precomp_g_points |} () =
  p.lemma_proj_g_pow2_128_eval ();
  p.lemma_proj_g_pow2_64_eval ();
  SPT256.a_pow2_128_lemma S.mk_pcurve_concrete_ops S.base_point

let proj_g_pow2_192_lemma {| cp:S.curve_params |} {| p:precomp_g_points |} () =
  p.lemma_proj_g_pow2_192_eval ();
  p.lemma_proj_g_pow2_128_eval ();
  p.lemma_proj_g_pow2_64_eval ();
  SPT256.a_pow2_192_lemma S.mk_pcurve_concrete_ops S.base_point

let proj_g_pow2_64_lseq_lemma {| cp:S.curve_params |} {| p:precomp_g_points |} () =
  normalize_term_spec (SPTK.proj_point_to_list p.proj_g_pow2_64);
  proj_g_pow2_64_lemma ();
  SPTK.proj_point_to_list_lemma p.proj_g_pow2_64

let proj_g_pow2_128_lseq_lemma {| cp:S.curve_params |} {| p:precomp_g_points |} () =
  normalize_term_spec (SPTK.proj_point_to_list proj_g_pow2_128);
  proj_g_pow2_128_lemma ();
  SPTK.proj_point_to_list_lemma proj_g_pow2_128


let proj_g_pow2_192_lseq_lemma {| cp:S.curve_params |} {| p:precomp_g_points |} () =
  normalize_term_spec (SPTK.proj_point_to_list proj_g_pow2_192);
  proj_g_pow2_192_lemma ();
  SPTK.proj_point_to_list_lemma proj_g_pow2_192

#push-options "--fuel 1"
let mk_proj_g_pow2_64 {| cp:S.curve_params |} {| p:precomp_g_points |} () =
  createL proj_g_pow2_64_list

let mk_proj_g_pow2_128 {| cp:S.curve_params |} {| p:precomp_g_points |} () =
  createL proj_g_pow2_128_list

let mk_proj_g_pow2_192 {| cp:S.curve_params |} {| p:precomp_g_points |} () =
  createL proj_g_pow2_192_list
#pop-options

