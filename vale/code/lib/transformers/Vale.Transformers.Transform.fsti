(**

   This module exposes user-friendly transformers and lemmas for them.

   Each transformation takes 1 or more [va_code] object(s) and
   produces a [va_code] object, along with additional data. The lemma
   guarantees that the produced [va_code] object is semantically
   identical to the (first, if more than one) provided [va_code]
   object.

   The additional data that is generated is always a [pbool] which is
   [ttrue] if the transformation succeeded, and otherwise is a [ffalse
   reason].  Under both circumstances, the lemma mentioned above is
   held, and in particular, a failed transformation is still safe to
   use (since in that case, the code returned is exactly the same as
   the first [va_code] object). The additional data is provided only
   for debugging, since we expect that after debugging and fixing
   things, all transformations will succeed.

*)
module Vale.Transformers.Transform

open Vale.X64.Machine_s
open Vale.Def.PossiblyMonad
open Vale.X64.Decls
open Vale.Transformers.Common

(* Re-expose [equiv_states], so that Common doesn't need to be imported *)
unfold let equiv_states (s1 s2:va_state) = equiv_states s1 s2

/// The Instruction Reordering Transformation

val reorder :
  orig:va_code ->
  hint:va_code ->
  va_transformation_result

val lemma_reorder :
  orig:va_code ->
  hint:va_code ->
  transformed:va_code ->
  va_s0:va_state -> va_sM:va_state -> va_fM:va_fuel ->
  Ghost (va_state & va_fuel)
    (requires (
        (va_require_total transformed (reorder orig hint).result va_s0) /\
        (va_get_ok va_s0) /\
        (va_ensure_total orig va_s0 va_sM va_fM) /\
        (va_get_ok va_sM)))
    (ensures (fun (va_sM', va_fM') ->
         (va_fM' == va_fM) /\
         (equiv_states va_sM va_sM') /\
         (va_ensure_total transformed va_s0 va_sM' va_fM') /\
         (va_get_ok va_sM')))

/// Check-if-same-printed-code "transform"
///
/// This "transformation" is a handy debugging tool. It does NOT
/// transform your code, but simply checks if both the original code
/// and hint code print to the same value.
///
/// This is useful for multiple reasons-
///
///   - Testing if some code you've modified is exactly the same
///       (modulo wrapping things in procedures).
///
///   - Sanity-checking the stability of lemmas. The signature of the
///       lemma here is the same as other transformations, and thus
///       can - be used to perform a first-pass sanity check to ensure
///       that - you'll be able to perform other transformations on
///       your code.

val check_if_same_printed_code :
  orig:va_code ->
  hint:va_code ->
  va_transformation_result

val lemma_check_if_same_printed_code :
  orig:va_code ->
  hint:va_code ->
  transformed:va_code ->
  va_s0:va_state -> va_sM:va_state -> va_fM:va_fuel ->
  Ghost (va_state & va_fuel)
    (requires (
        (va_require_total transformed (check_if_same_printed_code orig hint).result va_s0) /\
        (va_get_ok va_s0) /\
        (va_ensure_total orig va_s0 va_sM va_fM) /\
        (va_get_ok va_sM)))
    (ensures (fun (va_sM', va_fM') ->
         (va_fM' == va_fM) /\
         (equiv_states va_sM va_sM') /\
         (va_ensure_total transformed va_s0 va_sM' va_fM') /\
         (va_get_ok va_sM')))

/// Transformation to replace movbes -> mov + bswap.
///
/// The movbe instruction does not exist on some older generations of
/// the processor. This transform replaces movbe with the semantically
/// equivalent mov + bswap.

val movbe_elim :
  orig:va_code ->
  va_transformation_result

val lemma_movbe_elim :
  orig:va_code ->
  transformed:va_code ->
  va_s0:va_state -> va_sM:va_state -> va_fM:va_fuel ->
  Ghost (va_state & va_fuel)
    (requires (
        (va_require_total transformed (movbe_elim orig).result va_s0) /\
        (va_get_ok va_s0) /\
        (va_ensure_total orig va_s0 va_sM va_fM) /\
        (va_get_ok va_sM)))
    (ensures (fun (va_sM', va_fM') ->
         (va_fM' == va_fM) /\
         (equiv_states va_sM va_sM') /\
         (va_ensure_total transformed va_s0 va_sM' va_fM') /\
         (va_get_ok va_sM')))

/// Transformation to replace mov + mov -> mov.
///
/// This transformation exists simply as a demonstration of the
/// capability of the peephole transformer to support many-to-*
/// peephole transformations. In practice, it just behaves as a
/// trivially-dead code eliminator, where trivially dead means that a
/// mov into a location is immediately superceded by another move into
/// that same location, such that that move is independent of the
/// first.

val mov_mov_elim :
  orig:va_code ->
  va_transformation_result

val lemma_mov_mov_elim :
  orig:va_code ->
  transformed:va_code ->
  va_s0:va_state -> va_sM:va_state -> va_fM:va_fuel ->
  Ghost (va_state & va_fuel)
    (requires (
        (va_require_total transformed (mov_mov_elim orig).result va_s0) /\
        (va_get_ok va_s0) /\
        (va_ensure_total orig va_s0 va_sM va_fM) /\
        (va_get_ok va_sM)))
    (ensures (fun (va_sM', va_fM') ->
         (va_fM' == va_fM) /\
         (equiv_states va_sM va_sM') /\
         (va_ensure_total transformed va_s0 va_sM' va_fM') /\
         (va_get_ok va_sM')))
