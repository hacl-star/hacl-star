module Hacl.Impl.Blake2.Constants
open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Lib.LoopCombinators

module ST = FStar.HyperStack.ST
module Seq = Lib.Sequence
module Loops = Lib.LoopCombinators
module Spec = Spec.Blake2_Vec

let sigmaTable : x:ilbuffer Spec.sigma_elt_t 160ul{witnessed x Spec.sigmaTable /\ recallable x} =
  createL_global Spec.list_sigma

let ivTable_S: (x:ilbuffer (Spec.pub_word_t Spec.Blake2S) 8ul{witnessed x (Spec.ivTable Spec.Blake2S) /\ recallable x}) =
  createL_global Spec.list_iv_S

let ivTable_B: (x:ilbuffer (Spec.pub_word_t Spec.Blake2B) 8ul{witnessed x (Spec.ivTable Spec.Blake2B) /\ recallable x}) =
  createL_global Spec.list_iv_B

let rTable_S : x:ilbuffer (rotval U32) 4ul{witnessed x (Spec.rTable Spec.Blake2S) /\ recallable x} =
  createL_global Spec.rTable_list_S

let rTable_B : x:ilbuffer (rotval U64) 4ul{witnessed x (Spec.rTable Spec.Blake2B) /\ recallable x} =
  createL_global Spec.rTable_list_B


