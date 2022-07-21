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
module Spec = Spec.Blake2

/// We need to unfold manually the definition of the sigma table. This definition
/// was not declared as `inline_for_extraction` because otherwise it creates a lot
/// of work for the normalizer during the KaRaMeL extraction (which also explores
/// the ghost code, including the content of the assertions). However, we can't do
/// that by inserting manual calls to `norm` inside the code, because it blocks
/// the normalization performed by KaRaMeL, and we can't normalize as much as we
/// want because of the interface abstractions. The solution is to use post-processing.
noextract
let pp_sigmaTable () : Tactics.Tac unit =
  Tactics.norm [delta_only [`%Spec.list_sigma]]; Tactics.trefl ()

[@(Tactics.postprocess_with pp_sigmaTable)]
let sigmaTable : x:glbuffer Spec.sigma_elt_t 160ul{witnessed x Spec.sigmaTable /\ recallable x} =
  createL_global Spec.list_sigma

let ivTable_S: (x:glbuffer (Spec.pub_word_t Spec.Blake2S) 8ul{witnessed x (Spec.ivTable Spec.Blake2S) /\ recallable x}) =
  createL_global Spec.list_iv_S

let ivTable_B: (x:glbuffer (Spec.pub_word_t Spec.Blake2B) 8ul{witnessed x (Spec.ivTable Spec.Blake2B) /\ recallable x}) =
  createL_global Spec.list_iv_B

let rTable_B : x:glbuffer (rotval U64) 4ul{witnessed x (Spec.rTable Spec.Blake2B) /\ recallable x} =
  createL_global Spec.rTable_list_B


