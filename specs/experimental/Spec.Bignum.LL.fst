module Spec.Bignum.LL

open FStar.Seq
open FStar.Mul
open FStar.UInt
open FStar.Math.Lemmas
open Spec.Seq.Lib
open Spec.Bignum.Lib
open Spec.Bignum.LL.Lib

module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U128 = FStar.UInt128
open U32

(*
#reset-options "--z3rlimit 150 --max_fuel 0"

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
*)

#reset-options "--z3rlimit 50 --max_fuel 0"

val mult_by_limb_addj_f:
    a_i:U64.t -> l:U64.t -> c:U64.t -> r_ij:U64.t -> Pure (tuple2 carry U64.t)
    (requires (True))
    (ensures (fun (c', r) -> U64.v r + U64.v c' * x_i 1ul == U64.v a_i * U64.v l + U64.v c + U64.v r_ij))

let mult_by_limb_addj_f a_i l c r_ij =
    lemma_mult_add_add_64 a_i l c r_ij;
    let res = U128.(mul_wide a_i l +^ uint64_to_uint128 c +^ uint64_to_uint128 r_ij) in
    let r = U128.uint128_to_uint64 res in
    let c' = U128.shift_right res 64ul in
    let c' = U128.uint128_to_uint64 c' in
    lemma_div_mod (U64.v a_i * U64.v l + U64.v c + U64.v r_ij) (pow2 64);
    (c', r)

#reset-options "--z3rlimit 300 --max_fuel 0"

(* (forall k. (v i1 + v j <= k /\ k < v resLen) ==> res.[uint_to_t k] = r1.[uint_to_t k]) *)
val mult_by_limb_addj_inner:
    len:U32.t -> a:lseqbn len -> l:U64.t -> i1:U32.t{v i1 < v len} ->
    j:U32.t -> resLen:U32.t{v len + v j < v resLen} ->
    res:lseqbn resLen -> c1:carry -> r1:lseqbn resLen ->
    Pure (tuple2 carry (lseqbn resLen))
    (requires (eval_i r1 (i1 +^ j) + U64.v c1 * x_i (i1 +^ j) == eval_i res (i1 +^ j) + eval_i a i1 * U64.v l * x_i j /\
               res.[i1 +^ j] = r1.[i1 +^ j]))
    (ensures (fun (c', res') -> let i = i1 +^ 1ul in
        eval_i res' (i +^ j) + U64.v c' * x_i (i +^ j) == eval_i res (i +^ j) + eval_i a i * U64.v l * x_i j))

let mult_by_limb_addj_inner len a l i1 j resLen res c1 r1 =
    let i = i1 +^ 1ul in
    let (c', res_ij) = mult_by_limb_addj_f a.[i1] l c1 r1.[i1 +^ j] in
    let res' = r1.[i1 +^ j] <- res_ij in
    lemma_eval_upd resLen r1 (i1 +^ j) res_ij;
    lemma_eval_incr res' (i +^ j);
    assert (eval_i res' (i +^ j) == eval_i res' (i +^ j -^ 1ul) + U64.v res'.[i +^ j -^ 1ul] * x_i (i +^ j -^ 1ul));
    assert (eval_i res' (i +^ j) ==
            eval_i res (i1 +^ j) + eval_i a i1 * U64.v l * x_i j - U64.v c1 * x_i (i1 +^ j) +
            (U64.v a.[i1] * U64.v l + U64.v c1 + U64.v r1.[i1 +^ j] - U64.v c' * x_i 1ul) * x_i (i1 +^ j));
    lemma_distributivity_add_add_sub (U64.v a.[i1] * U64.v l) (U64.v c1) (U64.v r1.[i1 +^ j]) (U64.v c' * x_i 1ul) (x_i (i1 +^ j));
    lemma_mult_x1_xi1 (i +^ j) (x_i 1ul) (x_i (i1 +^ j));
    assert (eval_i res' (i +^ j) + U64.v c' * x_i (i +^ j) ==
            eval_i res (i1 +^ j) + eval_i a i1 * U64.v l * x_i j + U64.v a.[i1] * U64.v l * x_i (i1 +^ j) +
            U64.v r1.[i1 +^ j] * x_i (i1 +^ j));
    assert (res.[i1 +^ j] = r1.[i1 +^ j]);
    lemma_eval_incr res (i +^ j);
    lemma_mult_xi_xj i1 j (x_i i1) (x_i j);
    lemma_distributivity_add_fold_right (U64.v l * x_i j) (eval_i a i1) (U64.v a.[i1] * x_i i1);
    lemma_eval_incr a i;
    (c', res')

#reset-options "--z3rlimit 50 --max_fuel 2"

//(forall k. (v i + v j <= k /\ k < v resLen) ==> res.[uint_to_t k] = res'.[uint_to_t k])
val mult_by_limb_addj_:
    len:U32.t -> a:lseqbn len -> l:U64.t -> i:U32.t{v i <= v len} ->
    j:U32.t -> resLen:U32.t{v len + v j < v resLen} ->
    res:lseqbn resLen -> Pure (tuple2 carry (lseqbn resLen))
    (requires (True))
    (ensures (fun (c', res') -> eval_i res' (i +^ j) + U64.v c' * x_i (i +^ j) ==
                                eval_i res (i +^ j) + eval_i a i * U64.v l * x_i j /\ 
                                (forall k. (v i + v j <= k /\ k < v resLen) ==> res.[uint_to_t k] = res'.[uint_to_t k])))
    (decreases (v i))

let rec mult_by_limb_addj_ len a l i j resLen res =
    if i =^ 0ul then
        (0uL, res)
    else begin
        let i1 = i -^ 1ul in
        let (c1, r1) = mult_by_limb_addj_ len a l i1 j resLen res in
        assert (res.[i1 +^ j] = r1.[i1 +^ j]); //from ind hypo
        let (c', res') = mult_by_limb_addj_inner len a l i1 j resLen res c1 r1 in
        (c', res')
    end

#reset-options

val mult_by_limb_addj:
    len:U32.t -> a:lseqbn len -> l:U64.t -> j:U32.t ->
    resLen:U32.t{v len + v j < v resLen} ->
    res:lseqbn resLen -> Pure (tuple2 carry (lseqbn resLen))
    (requires (True))
    (ensures (fun (c', res') -> eval_i res' (len +^ j) + U64.v c' * x_i (len +^ j) ==
                                eval_i res (len +^ j) + eval a * U64.v l * x_i j))

let mult_by_limb_addj len a l j resLen res = mult_by_limb_addj_ len a l len j resLen res

#reset-options "--z3rlimit 300 --max_fuel 0"

val mult_inner:
    len:U32.t -> a:lseqbn len -> b:lseqbn len ->
    resLen:U32.t{v resLen = v len + v len} ->
    j1:U32.t{v j1 < v len} -> r:lseqbn resLen -> Pure (lseqbn resLen)
    (requires (eval_i r (len +^ j1) == eval a * eval_i b j1))
    (ensures (fun res' -> let j = j1 +^ 1ul in
        eval_i res' (len +^ j) == eval a * eval_i b j))

let mult_inner len a b resLen j1 r =
    let j = j1 +^ 1ul in
    let (c', res') = mult_by_limb_addj len a b.[j1] j1 resLen r in
    assert (eval_i r (len +^ j1) + eval a * U64.v b.[j1] * x_i j1 ==
            eval a * eval_i b j1 + eval a * U64.v b.[j1] * x_i j1);
    lemma_distributivity_add_fold (eval a) (eval_i b j1) (U64.v b.[j1] * x_i j1);
    lemma_eval_incr b j;
    assert (eval_i res' (len +^ j1) + U64.v c' * x_i (len +^ j1) == eval a * eval_i b j);
    let res1 = res'.[len +^ j1] <- c' in
    lemma_eval_upd resLen res' (len +^ j1) c';
    lemma_eval_incr res1 (len +^ j);
    assert (eval_i res1 (len +^ j) == eval a * eval_i b j);
    res1

#reset-options "--z3rlimit 50 --max_fuel 2"

val mult_:
    len:U32.t -> a:lseqbn len -> b:lseqbn len ->
    resLen:U32.t{v resLen = v len + v len} ->
    j:U32.t{v j <= v len} -> Tot (res':lseqbn resLen{eval_i res' (len +^ j) == eval a * eval_i b j})
    (decreases (v j))

let rec mult_ len a b resLen j  =
    if j =^ 0ul then begin
        let res' = create resLen 0uL in
        lemma_eval_init_seq_is_0 resLen res' (len +^ j);
        res'
        end
    else begin
        let j1 = j -^ 1ul in
        let r = mult_ len a b resLen j1 in
        mult_inner len a b resLen j1 r 
    end

#reset-options

val mult:
    len:U32.t -> a:lseqbn len -> b:lseqbn len ->
    resLen:U32.t{v resLen = v len + v len} ->
    Tot (res':lseqbn resLen{eval res' == eval a * eval b})

let mult len a b resLen = mult_ len a b resLen len