module Hacl.Spec.Curve25519.Field64.Definition

open Lib.Sequence
open Lib.IntTypes

module P = Spec.Curve25519

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let felem4 = (uint64 * uint64 * uint64 * uint64)

open FStar.Mul

noextract
val as_nat4: f:felem4 -> GTot nat
let as_nat4 f =
  let (s0, s1, s2, s3) = f in
  v s0 + v s1 * pow2 64 + v s2 * pow2 64 * pow2 64 +
  v s3 * pow2 64 * pow2 64 * pow2 64

let feval4 (f:felem4) : GTot P.elem = as_nat4 f % P.prime


val bn_v_is_as_nat: e:lseq uint64 4 ->
  Lemma (as_nat4 (e.[0], e.[1], e.[2], e.[3]) == Hacl.Spec.Bignum.Definitions.bn_v #U64 #4 e)
let bn_v_is_as_nat e =
  Hacl.Impl.Curve25519.Lemmas.lemma_nat_from_uints64_le_4 e;
  assert (as_nat4 (e.[0], e.[1], e.[2], e.[3]) == Lib.ByteSequence.nat_from_intseq_le e);
  Hacl.Spec.Bignum.Convert.bn_v_is_nat_from_intseq_le_lemma 4 e;
  assert (Hacl.Spec.Bignum.Definitions.bn_v #U64 #4 e == Lib.ByteSequence.nat_from_intseq_le e)
