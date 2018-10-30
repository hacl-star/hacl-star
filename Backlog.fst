module Backlog

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence


/// Spec.ByteSequence.fst:
/// ======================
///
/// I1. There is no definition of empty bytes
///
/// R1. Introduce the following definition to Lib.ByteSequence.fsti ?

let lbytes_empty: lbytes 0 = create 0 (u8 0)




/// Spec.Random.fst:
/// ================
///
/// I1. This module does not work properly.
///
/// R1. Restore this module and use it in Specifications that need it
///     (like Spec.ECIES.fst)




/// Spec.ECIES.fst:
/// ===============
///
/// I1. The following code is needed because Z3 cannot prove the
/// innequalities based on pow2:

let f (a:Spec.Hash.algorithm) (vsize_key_asymmetric: size_nat{vsize_key_asymmetric <= pow2 32 * pow2 3}) =
  assert_norm(pow2 32 * pow2 3 <= pow2 61 - 1);
  assert_norm(pow2 32 * pow2 3 <= pow2 125 - 1);
  assert(vsize_key_asymmetric <= Spec.Hash.max_input a)

/// R1. Remove that code by adding a Lemma in Spec.IntTypes.fsti
///
///
/// I2. There is an assumed function for Randomness.

assume val crypto_random: len:size_nat -> Tot (lbytes len)

/// R2. Use the function provided by Spec.Random instead.
