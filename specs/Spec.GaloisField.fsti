module Spec.GaloisField

open FStar.BitVector

(* We represent GF(2^n) with irreducible polynomial x^n + p(x), deg(p) <= n-1
   by GF n bv where bv is the big-endian bitvector for p(x)   *)
type polynomial (degree:nat) = bv_t (degree + 1)
type field' = | GF: bits:pos -> irred: polynomial (bits - 1) -> field'
let field = field'

val numbits: field -> pos
val mk_field: bits:pos -> irred:nat{irred < pow2 bits} -> f:field{numbits f = bits}
val felem (f:field) : Type0

val to_felem: #f:field -> n:nat{n < pow2 (numbits f)} -> felem f
val from_felem: #f:field -> felem f -> n:nat{n < pow2 (numbits f)}

val zero: #f:field -> felem f
val one: #f:field -> felem f

val fadd: #f:field -> a:felem f -> b:felem f -> c:felem f
val add_comm: #f:field -> a:felem f -> b:felem f -> Lemma (a `fadd` b == b `fadd` a)
val add_asso: #f:field -> a:felem f -> b:felem f -> c:felem f -> Lemma (a `fadd` b `fadd` c == a `fadd` (b `fadd` c))
val add_zero: #f:field -> a:felem f -> Lemma (a `fadd` zero == a)

val fmul: #f:field -> a:felem f -> b:felem f -> c:felem f
val fmul_intel:
  #f:field{f.bits = 128 /\ f.irred = (UInt.to_vec #128 0xe1000000000000000000000000000000)} ->
  a:felem f ->
  b:felem f ->
  c:felem f

(* val finv: #f:field -> irr:felem f ->  a:felem f -> c:felem f *)
