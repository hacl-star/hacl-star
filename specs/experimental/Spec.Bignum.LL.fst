module Spec.Bignum.LL

open FStar.Seq
open FStar.Mul
open FStar.UInt
open FStar.Math.Lemmas
open Spec.Seq.Lib
open Spec.Bignum.Lib

module U32 = FStar.UInt32
module U64 = FStar.UInt64
open U32

type bignum = nat
type seqbn = Spec.Seq.Lib.seq U64.t
type lseqbn len = s:seqbn{length s = U32.v len}
type carry = U64.t //c:U64.t{U64.v c = 1 \/ U64.v c = 0}

let x_i i = pow2 (64 * v i)

val eval_: s:seqbn -> i:U32.t{v i <= length s} -> Tot bignum (decreases (v i))
let rec eval_ s i =
    if i =^ 0ul then 0
    else eval_ s (i -^ 1ul) + U64.v s.[i -^ 1ul] * x_i (i -^ 1ul)

val eval_i: s:seqbn -> i:U32.t{v i <= length s} -> Tot bignum
let eval_i s i = eval_ s i

val eval: s:seqbn{length s > 0} -> Tot bignum
let eval s = eval_i s (seq_length s)

val add_with_carry: a:U64.t -> b:U64.t -> c:carry -> Pure (tuple2 carry U64.t)
    (requires (True))
    (ensures (fun (c', r) -> U64.v r + U64.v c' * x_i 1ul = U64.v a + U64.v b + U64.v c))

let add_with_carry a b c =
    let r = U64.(a +%^ b +%^ c) in
    assert (U64.v r = (U64.v a + U64.v b + U64.v c) % pow2 64);
    let (c', r) = if U64.(r <^ a) then (1uL, r) else (0uL, r) in
    assume (U64.v c' = (U64.v a + U64.v b + U64.v c) / pow2 64);
    lemma_div_mod (U64.v a + U64.v b + U64.v c) (pow2 64);
    assert (x_i 1ul = pow2 64);
    (c', r)

val lemma_mult_x1_xi1: i:U32.t{v i > 0} -> x1:nat -> xi1:nat -> Lemma
    (requires (x1 = x_i 1ul /\ xi1 = x_i (i -^ 1ul)))
    (ensures (x1 * xi1 = x_i i))
let lemma_mult_x1_xi1 i x1 xi =
    pow2_plus (64 * U32.v 1ul) (64 * U32.v (i -^ 1ul));
    assert (pow2 (64 * U32.v 1ul) * pow2 (64 * U32.v (i -^ 1ul)) = pow2 ((64 * U32.v 1ul) + (64 * U32.v (i -^ 1ul))));
    assert (pow2 (64 * U32.v 1ul) * pow2 (64 * U32.v (i -^ 1ul)) = pow2 (64 * U32.v i))
    
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

#reset-options "--z3rlimit 150 --max_fuel 2"

val sum_:
    len:U32.t -> a:lseqbn len -> b:lseqbn len ->
    i:U32.t{v i <= v len} -> res:lseqbn len -> Pure (tuple2 carry (lseqbn len))
    (requires (True))
    (ensures (fun (c', res') -> eval_i res' i + U64.v c' * x_i i == eval_i a i + eval_i b i))
    (decreases (v i))

let rec sum_ len a b i res =
    if i =^ 0ul then
       (0uL, res)
    else begin
        let i1 = i -^ 1ul in
        let (c, r) = sum_ len a b i1 res in
        assert (eval_i r i1 + U64.v c * x_i i1 == eval_i a i1 + eval_i b i1); // from rec ind hypo
        let (c', res_i) = add_with_carry a.[i1] b.[i1] c in
        assert (U64.v res_i + U64.v c' * x_i 1ul == U64.v a.[i1] + U64.v b.[i1] + U64.v c); // from add_with_carry
        let res' = r.[i1] <- res_i in
        lemma_eval_upd len r i1 res_i;
        assert (eval_i res' i1 == eval_i r i1); // from upd
        assert (eval_i res' i == eval_i res' i1 + U64.v res'.[i1] * x_i i1); //from eval_i
        assert (eval_i res' i == eval_i a i1 + eval_i b i1 - U64.v c * x_i i1 + (U64.v a.[i1] + U64.v b.[i1] + U64.v c - U64.v c' * x_i 1ul) * x_i i1); //expansion
        assert (eval_i res' i == eval_i a i1 + eval_i b i1 - U64.v c * x_i i1 + U64.v a.[i1] * x_i i1  + U64.v b.[i1] * x_i i1  + U64.v c * x_i i1  - U64.v c' * x_i 1ul * x_i i1);
        assert (eval_i res' i == eval_i a i1 + eval_i b i1 + U64.v a.[i1] * x_i i1  + U64.v b.[i1] * x_i i1  - U64.v c' * x_i 1ul * x_i i1);
        assert (eval_i res' i + U64.v c' * x_i 1ul * x_i i1  == eval_i a i + eval_i b i);
        lemma_mult_x1_xi1 i (x_i 1ul) (x_i i1);
        (c', res')
    end

val sum: 
    len:U32.t -> a:lseqbn len -> b:lseqbn len -> Pure (tuple2 carry (lseqbn len))
    (requires (True))
    (ensures (fun (c', res') -> eval_i res' len + U64.v c' * x_i len = eval_i a len + eval_i b len))
let sum len a b =
    let res = create len 0uL in
    sum_ len a b len res