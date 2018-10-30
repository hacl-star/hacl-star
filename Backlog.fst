module Backlog

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence


/// Lib.ByteSequence.fst:
/// ======================

/// I1. There is no definition of empty bytes
///
/// R1. Introduce the following definition to Lib.ByteSequence.fsti ?

let lbytes_empty: lbytes 0 = create 0 (u8 0)




/// Lib.Buffer.fst:
/// ===============


/// I1. The definition of `salloc1` is nice because it is general but a simpler
///     signature would be preferable for users.
///
/// R1. Experiment in having a `loc_buffer` footprint instead of a `loc`.


/// I2. The naming of `salloc1_trivial` is not user-friendly.
///
/// R2. Rename by aliasing `salloc1_trivial` into `salloc` using the
///     loc_buffer version provided by R1.


/// I3. Specifications should not reason about liveness.
///
/// R3. Experiment to find out if we can remove the liveness clauses recently
///     added, can be removed again:
///     https://everestexpedition.slack.com/archives/C4237009M/p1540224738000100
///     https://github.com/project-everest/hacl-star/commit/60f8f02ccffafd0fcca12ceb4bf5f4ac4e97725c




/// Spec.Random.fst:
/// ================


/// I1. This module does not work properly.
///
/// R1. Restore this module and use it in Specifications that need it
///     (like Spec.ECIES.fst)




/// Spec.ECIES.fst:
/// ===============


/// I1. The following code is needed because Z3 cannot prove the
/// innequalities based on `pow2`:

let f (a:Spec.Hash.algorithm) (vsize_key_asymmetric: size_nat{vsize_key_asymmetric <= pow2 32 * pow2 3}) =
  assert_norm(pow2 32 * pow2 3 <= pow2 61 - 1);
  assert_norm(pow2 32 * pow2 3 <= pow2 125 - 1);
  assert(vsize_key_asymmetric <= Spec.Hash.max_input a)

/// R1. Remove that code by adding a Lemma in Spec.IntTypes.fsti


/// I2. There is an assumed function for Randomness.

assume val crypto_random: len:size_nat -> Tot (lbytes len)

/// R2. Use the function provided by Spec.Random instead.
