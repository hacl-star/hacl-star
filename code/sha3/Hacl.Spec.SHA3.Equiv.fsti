module Hacl.Spec.SHA3.Equiv

open Lib.IntTypes
open Lib.NTuple

open Hacl.Spec.SHA3.Vec
open Hacl.Spec.SHA3.Vec.Common
module Spec = Spec.SHA3

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
