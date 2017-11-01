module Spec.Bignum.LL.Lib

open FStar.Seq
open FStar.Mul
open FStar.UInt
open FStar.Math.Lemmas
open Spec.Seq.Lib
open Spec.Bignum.Lib

module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U128 = FStar.UInt128
open U32

type bignum = nat
type seqbn = Spec.Seq.Lib.seq U64.t
type lseqbn len = s:seqbn{length s = U32.v len}
type carry = U64.t //c:U64.t{U64.v c = 1 \/ U64.v c = 0}

let x_i i = pow2 (64 * v i)

val eval_i: s:seqbn -> i:U32.t{v i <= length s} -> Tot bignum (decreases (v i))
let rec eval_i s i =
    if i =^ 0ul then 0
    else eval_i s (i -^ 1ul) + U64.v s.[i -^ 1ul] * x_i (i -^ 1ul)

val eval: s:seqbn -> Tot bignum
let eval s = eval_i s (seq_length s)

val lemma_eval_incr: s:seqbn -> i:U32.t{0 < v i /\ v i <= length s} -> Lemma
    (requires (True))
    (ensures (eval_i s i = eval_i s (i -^ 1ul) + U64.v s.[i -^ 1ul] * x_i (i -^ 1ul)))
let lemma_eval_incr s i = ()

val lemma_mult_x1_xi1: i:U32.t{v i > 0} -> x1:nat -> xi1:nat -> Lemma
    (requires (x1 = x_i 1ul /\ xi1 = x_i (i -^ 1ul)))
    (ensures (x1 * xi1 = x_i i))
let lemma_mult_x1_xi1 i x1 xi =
    pow2_plus (64 * U32.v 1ul) (64 * U32.v (i -^ 1ul));
    assert (pow2 (64 * U32.v 1ul) * pow2 (64 * U32.v (i -^ 1ul)) = pow2 ((64 * U32.v 1ul) + (64 * U32.v (i -^ 1ul))));
    assert (pow2 (64 * U32.v 1ul) * pow2 (64 * U32.v (i -^ 1ul)) = pow2 (64 * U32.v i))

val lemma_mult_xi_xj: i:U32.t -> j:U32.t -> xi:nat -> xj:nat -> Lemma
    (requires (xi = x_i i /\ xj = x_i j /\ v i + v j < pow2 32))
    (ensures (v i + v j < pow2 32 /\ xi * xj = x_i (i +^ j)))
let lemma_mult_xi_xj i j xi xj =
    pow2_plus (64 * U32.v i) (64 * U32.v j)

val lemma_upd: len:U32.t -> s:lseqbn len -> s':lseqbn len -> i1:U32.t{U32.v i1 < U32.v len} -> s_i1:U64.t -> Lemma
    (requires (s' = (s.[i1] <- s_i1)))
    (ensures (forall i. (i <> v i1 /\ i < v len) ==> s.[uint_to_t i] = s'.[uint_to_t i]))
let lemma_upd len s s' i1 s_i1 = ()

val lemma_eval_i: len:U32.t -> s1:lseqbn len -> s2:lseqbn len -> i:U32.t{v i < v len} -> Lemma
    (requires (forall j. v j  <  v i ==> s1.[j] == s2.[j]))
    (ensures (eval_i s1 i == eval_i s2 i))
    (decreases (v i))
let rec lemma_eval_i len s1 s2 i =
    if i =^ 0ul then ()
    else lemma_eval_i len s1 s2 (i -^ 1ul)

#reset-options "--z3rlimit 30 --max_fuel 0"

val lemma_eval_upd: len:U32.t -> s:lseqbn len -> i1:U32.t{v i1 < length s} -> s_i1:U64.t -> Lemma
    (requires (True))
    (ensures (let s' = s.[i1] <- s_i1 in eval_i s i1 == eval_i s' i1))
let lemma_eval_upd len s i1 s_i1 =
    let s' = s.[i1] <- s_i1 in
    lemma_upd len s s' i1 s_i1;
    assert (slice s 0ul i1 == slice s' 0ul i1);
    lemma_eval_i len s s' i1;
    assert (eval_i s i1 == eval_i s' i1)

#reset-options "--z3rlimit 30 --max_fuel 2"

val lemma_eval_init_seq_is_0: len:U32.t -> s:lseqbn len -> i:U32.t{v i <= v len} -> Lemma
    (requires (forall j. v j < v len ==> s.[j] = 0uL))
    (ensures (eval_i s i = 0))
    (decreases (v i))
let rec lemma_eval_init_seq_is_0 len s i =
    if i =^ 0ul then ()
    else lemma_eval_init_seq_is_0 len s (i -^ 1ul)

#reset-options 

val lemma_distributivity_add_fold: a:int -> b:int -> c:int -> Lemma
  (a * b + a * c = a * (b + c))
let lemma_distributivity_add_fold a b c = ()

val lemma_distributivity_add_fold_right: a:int -> b:int -> c:int -> Lemma
  (b * a + c * a = (b + c) * a)
let lemma_distributivity_add_fold_right a b c = ()

val lemma_distributivity_add_add_sub: a:int -> b:int -> c:int -> d:int -> e:int -> Lemma
  ((a + b + c - d) * e = a * e + b * e + c * e - d * e)
let lemma_distributivity_add_add_sub a b c d e = ()

#reset-options "--z3rlimit 50 --max_fuel 0"

val lemma_mult_add_add_64: a:U64.t -> b:U64.t -> c:U64.t -> d:U64.t -> Lemma
    (U64.v a * U64.v b + U64.v c + U64.v d < pow2 128)

let lemma_mult_add_add_64 a b c d =
    let n = pow2 64 in
    assert (U64.v a <= n - 1 /\ U64.v b <= n - 1 /\ U64.v c <= n - 1 /\ U64.v d <= n - 1);
    assert (U64.v a * U64.v b + U64.v c + U64.v d <= (n - 1) * (n - 1) + (n - 1) + (n - 1));
    assert ((n - 1) * (n - 1) + (n - 1) + (n - 1) == n * n - 1);
    pow2_plus 64 64