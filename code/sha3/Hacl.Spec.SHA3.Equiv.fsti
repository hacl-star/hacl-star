module Hacl.Spec.SHA3.Equiv

open Lib.Sequence
open Lib.IntTypes
open Lib.IntVector
open Lib.NTuple

open Hacl.Spec.SHA3.Vec
open Hacl.Spec.SHA3.Vec.Common
module Spec = Spec.SHA3

(* shake128 *)

val shake128_lemma_l:
  m:m_spec
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
  m:m_spec
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
  m:m_spec
  -> inputByteLen:nat
  -> input:multiseq (lanes m) inputByteLen
  -> output:multiseq (lanes m) 28
  -> l:nat{l < lanes m} ->
  Lemma
   ((sha3_224 m inputByteLen input output).(|l|) ==
      Spec.sha3_224 inputByteLen input.(|l|))

(* sha3_256 *)

val sha3_256_lemma_l:
  m:m_spec
  -> inputByteLen:nat
  -> input:multiseq (lanes m) inputByteLen
  -> output:multiseq (lanes m) 32
  -> l:nat{l < lanes m} ->
  Lemma
   ((sha3_256 m inputByteLen input output).(|l|) ==
      Spec.sha3_256 inputByteLen input.(|l|))

(* sha3_384 *)

val sha3_384_lemma_l:
  m:m_spec
  -> inputByteLen:nat
  -> input:multiseq (lanes m) inputByteLen
  -> output:multiseq (lanes m) 48
  -> l:nat{l < lanes m} ->
  Lemma
   ((sha3_384 m inputByteLen input output).(|l|) ==
      Spec.sha3_384 inputByteLen input.(|l|))

(* sha3_512 *)

val sha3_512_lemma_l:
  m:m_spec
  -> inputByteLen:nat
  -> input:multiseq (lanes m) inputByteLen
  -> output:multiseq (lanes m) 64
  -> l:nat{l < lanes m} ->
  Lemma
   ((sha3_512 m inputByteLen input output).(|l|) ==
      Spec.sha3_512 inputByteLen input.(|l|))

(* Lemmas to prove functions in Hacl.Hash.SHA3 module *)

val absorb_inner_repeat_blocks_multi_lemma:
  r:size_nat{r > 0 /\ r <= 200}
  -> inputByteLen:nat{inputByteLen % r = 0}
  -> input:multiseq 1 inputByteLen
  -> s:lseq uint64 25 ->
  Lemma
   (reveal_vec_1 U64;
    absorb_inner_nblocks #M32 r inputByteLen input s ==
    repeat_blocks_multi r input.(|0|) (Spec.absorb_inner r) s)

val absorb_inner_block_r_lemma:
  r:size_nat{r > 0 /\ r <= 200}
  -> input:multiseq 1 r
  -> s:lseq uint64 25 ->
  Lemma
   (reveal_vec_1 U64;
    absorb_inner_block #M32 r r input 0 s == Spec.absorb_inner r input.(|0|) s)

val absorb_last_r_lemma:
  delimitedSuffix:byte_t
  -> r:size_nat{r > 0 /\ r <= 200}
  -> inputByteLen:nat{inputByteLen < r}
  -> input:multiseq 1 inputByteLen
  -> s:lseq uint64 25 ->
  Lemma
   (reveal_vec_1 U64;
    absorb_final #M32 s r inputByteLen input delimitedSuffix ==
      Spec.absorb_last delimitedSuffix r inputByteLen input.(|0|) s)

val squeeze_s_lemma:
  s:lseq uint64 25
  -> r:size_nat{r > 0 /\ r <= 200}
  -> outputByteLen:size_nat
  -> b:multiseq 1 outputByteLen ->
  Lemma
   (reveal_vec_1 U64;
    (squeeze #M32 s r outputByteLen b).(|0|) == Spec.squeeze s r outputByteLen)
