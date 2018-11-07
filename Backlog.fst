module Backlog

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence


/// Lib.IntTypes.fst:
/// =================


/// I1. There is a need of having generic types for word and limb:
///     something like:

inline_for_extraction
unfold let inttype_limb (t:inttype{t <> U1 /\ t <> U128}) =
  match t with
  | U8 -> U16
  | U16 -> U32
  | U32 -> U64
  | U64 -> U128

type word_t (t:inttype) = uint_t t SEC
type pub_word_t (t:inttype) = uint_t t PUB
type limb_t (t:inttype{t <> U1 /\ t <> U128}) = uint_t (inttype_limb t) SEC
type pub_limb_t (t:inttype{t <> U1 /\ t <> U128}) = uint_t (inttype_limb t) PUB

inline_for_extraction
let max_limb (t:inttype{t <> U1 /\ t <> U128}) = maxint (inttype_limb t)

inline_for_extraction
let to_word (t:inttype{t <> U1}) (x:size_nat{x <= maxint t}) : word_t t =
  match t with
  | U8 -> u8 x
  | U16 -> u16 x
  | U32 -> u32 x
  | U64 -> u64 x
  | U128 -> u128 x

inline_for_extraction
let to_limb (t:inttype{t <> U1 /\ t <> U128}) (x:nat{x <= max_limb t}) : limb_t t =
  match t with
  | U8 -> u16 x
  | U16 -> u32 x
  | U32 -> u64 x
  | U64 -> u128 x

inline_for_extraction
let limb_to_word (t:inttype{t <> U1 /\ t <> U128}) (x:limb_t t) : word_t t =
  match t with
  | U8 -> to_u8 x
  | U16 -> to_u16 x
  | U32 -> to_u32 x
  | U64 -> to_u64 x


/// R1. Experiment backport of functions from Spec.SHA2 to Lib.IntTypes
///     replacing the index of the type by a uint_t instead of the "alg".



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




/// Spec.SHA2.fst:
/// ==============


/// I1. word and limb functions should not located here.
///
/// R1. Implement functions in Lib.IntTypes and use these instead
///     of the local definitions.
