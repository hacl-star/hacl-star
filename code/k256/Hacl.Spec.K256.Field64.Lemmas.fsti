module Hacl.Spec.K256.Field64.Lemmas

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

module S = Spec.K256

module SD = Hacl.Spec.Bignum.Definitions
module SB = Hacl.Spec.Bignum

include Hacl.Spec.K256.Field64

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val carry_pass_small_lemma: f:felem -> cin:uint64{(v cin + 1) * prime_c < pow2 64} ->
  Lemma (SD.bn_v (carry_pass_small f cin) % S.prime == (SD.bn_v f + v cin * pow2 256) % S.prime)

val carry_pass_lemma: f:felem -> cin:uint64 ->
  Lemma (SD.bn_v (carry_pass f cin) % S.prime == (SD.bn_v f + v cin * pow2 256) % S.prime)

val carry_wide_lemma: f:felem_wide ->
  Lemma (SD.bn_v (carry_wide f) % S.prime == SD.bn_v f % S.prime)

val fadd4_lemma: f1:felem -> f2:felem ->
  Lemma (SD.bn_v (fadd4 f1 f2) % S.prime == S.fadd (SD.bn_v f1 % S.prime) (SD.bn_v f2 % S.prime))

val fsub4_lemma: f1:felem -> f2:felem ->
  Lemma (SD.bn_v (fsub4 f1 f2) % S.prime == S.fsub (SD.bn_v f1 % S.prime) (SD.bn_v f2 % S.prime))

val fmul4_lemma: f1:felem -> r:felem ->
  Lemma (SD.bn_v (fmul4 f1 r) % S.prime == S.fmul (SD.bn_v f1 % S.prime) (SD.bn_v r % S.prime))

val fmul14_lemma: f1:felem -> f2:uint64{v f2 < pow2 17} ->
  Lemma (SD.bn_v (fmul14 f1 f2) % S.prime == SD.bn_v f1 % S.prime * v f2 % S.prime)

val fsqr4_lemma: f:felem ->
  Lemma (SD.bn_v (fsqr4 f) % S.prime == S.fmul (SD.bn_v f % S.prime) (SD.bn_v f % S.prime))
