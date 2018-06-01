module Spec.Bignum.LL.Lib

open FStar.Mul
open FStar.Math.Lemmas

open Spec.Lib.IntTypes
open Spec.Lib.RawIntTypes
open Spec.Lib.IntSeq
open Spec.Lib.IntSeq.Lemmas

type bignum = nat

type lseqbn len = intseq U64 len
type carry = uint64

let x_i (i:size_nat) = pow2 (64 * i)

val eval_i:
    len:size_nat{len > 0} -> s:lseqbn len -> i:size_nat{i <= len} -> Tot bignum (decreases i)
let rec eval_i len s i =
    if i = 0 then 0
    else eval_i len s (i - 1) + (uint_to_nat s.[i - 1]) * x_i (i - 1)

val eval:
    len:size_nat{len > 0} -> s:lseqbn len -> Tot bignum
let eval len s = eval_i len s len

val lemma_eval_i:
    len:size_nat -> s1:lseqbn len -> s2:lseqbn len -> i:size_nat{i < len} -> Lemma
    (requires (forall (j:size_nat). j < i ==> s1.[j] == s2.[j]))
    (ensures (eval_i len s1 i == eval_i len s2 i))
    (decreases i)
let rec lemma_eval_i len s1 s2 i =
    if i = 0 then ()
    else lemma_eval_i len s1 s2 (i - 1)

val lemma_eval_incr:
    len:size_nat{len > 0} ->  s:lseqbn len -> i:size_nat{0 < i /\ i <= len} -> Lemma
    (requires (True))
    (ensures (eval_i len s i == eval_i len s (i - 1) + (uint_to_nat s.[i - 1]) * x_i (i - 1)))
let rec lemma_eval_incr len s i = ()

val lemma_eval_init_seq_is_0: 
    len:size_nat{len > 0} -> s:lseqbn len -> i:size_nat{i <= len} -> Lemma
    (requires (forall (j:size_nat). j < len ==> uint_to_nat s.[j] = 0))
    (ensures (eval_i len s i = 0))
    (decreases i)

#reset-options "--z3rlimit 50 --max_fuel 2"

let rec lemma_eval_init_seq_is_0 len s i =
    if i = 0 then ()
    else lemma_eval_init_seq_is_0 len s (i - 1)

val lemma_mult_x1_xi1:
    i:size_nat{i > 0} -> x1:nat -> xi1:nat -> Lemma
    (requires (x1 = x_i 1 /\ xi1 = x_i (i - 1)))
    (ensures (x1 * xi1 = x_i i))
let lemma_mult_x1_xi1 i x1 xi =
    pow2_plus (64 * 1) (64 * (i - 1));
    assert (pow2 (64 * 1) * pow2 (64 * (i - 1)) = pow2 (64 * 1 + 64 * (i - 1)));
    assert (pow2 (64 * 1) * pow2 (64 * (i - 1)) = pow2 (64 * i))

val lemma_mult_xi_xj:
    i:size_nat -> j:size_nat -> xi:nat -> xj:nat -> Lemma
    (requires (xi = x_i i /\ xj = x_i j /\ i + j < max_size_t))
    (ensures (i + j < max_size_t /\ xi * xj = x_i (i + j)))
let lemma_mult_xi_xj i j xi xj =
    pow2_plus (64 * i) (64 * j)

val lemma_mul_assoc:
    a:nat -> b:nat -> c:nat -> Lemma
    (a * b * c = a * (b * c))
let lemma_mul_assoc a b c = ()

val lemma_distributivity_add_add_sub: 
  a:nat -> b:nat -> c:nat -> d:nat -> e:nat -> Lemma
  ((a + b + c - d) * e = a * e + b * e + c * e - d * e)
let lemma_distributivity_add_add_sub a b c d e = ()

val lemma_distributivity_add_fold: 
  a:nat -> b:nat -> c:nat -> Lemma
  (a * b + a * c = a * (b + c))
let lemma_distributivity_add_fold a b c = ()
