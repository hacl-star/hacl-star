module Spec.Bignum.LL

open FStar.Mul
open FStar.Math.Lemmas

open Spec.Lib.IntTypes
open Spec.Lib.RawIntTypes
open Spec.Lib.IntSeq
open Spec.Lib.IntSeq.Lemmas
open Spec.Bignum.LL.Lib

(* ADDITION *)
val add_with_carry:
  a:uint64 -> b:uint64 -> c:carry -> Pure (tuple2 carry uint64)
  (requires (True))
  (ensures (fun (c', r) -> uint_v r + uint_v c' * x_i 1 = uint_v a + uint_v b + uint_v c))
  #reset-options "--z3rlimit 50 --max_fuel 0"
let add_with_carry a b c =
  let tmp = to_u128 a +! to_u128 b +! to_u128 c in
  let r = to_u64 tmp in
  assert (uint_v r = (uint_v a + uint_v b + uint_v c) % pow2 64);
  let c' = to_u64 (tmp >>. (u32 64)) in
  assert (uint_v c' = (uint_v a + uint_v b + uint_v c) / pow2 64);
  lemma_div_mod (uint_v a + uint_v b + uint_v c) (pow2 64);
  assert_norm (x_i 1 = pow2 64);
  (c', r)

val bn_add_pred:
  len:size_nat{len > 0} -> a:lseqbn len -> b:lseqbn len -> i:size_nat{i <= len} -> tuple2 carry (lseqbn len) -> Tot Type0
let bn_add_pred len a b i (c, res) = eval_i len res i + uint_v c * x_i i == eval_i len a i + eval_i len b i

val bn_add_f:
  len:size_nat{len > 0} -> a:lseqbn len -> b:lseqbn len -> Tot (repeatable #(tuple2 carry (lseqbn len)) #len (bn_add_pred len a b))
  #reset-options "--z3rlimit 150 --max_fuel 2"
let bn_add_f len a b i (c, res) =
  let (c', res_i) = add_with_carry a.[i] b.[i] c in
  assert (uint_v res_i + uint_v c' * x_i 1 = uint_v a.[i] + uint_v b.[i] + uint_v c);
  let res' = res.[i] <- res_i in
  lemma_eval_i len res res' i;
  assert (eval_i len res' (i + 1) == eval_i len res' i + (uint_v res'.[i]) * x_i i); //from eval_i
  assert (eval_i len res' (i + 1) == eval_i len a i + eval_i len b i - uint_v c * x_i i + (uint_v a.[i] + uint_v b.[i] + uint_v c - uint_v c' * x_i 1) * x_i i); //expansion
  assume (eval_i len res' (i + 1) == eval_i len a i + eval_i len b i - uint_v c * x_i i + uint_v a.[i] * x_i i + uint_v b.[i] * x_i i + uint_v c * x_i i - uint_v c' * x_i 1 * x_i i);
  assert (eval_i len res' (i + 1) == eval_i len a i + eval_i len b i + uint_v a.[i] * x_i i + uint_v b.[i] * x_i i - uint_v c' * x_i 1 * x_i i);
  assert (eval_i len res' (i + 1) + uint_v c' * x_i 1 * x_i i == eval_i len a (i + 1) + eval_i len b (i + 1));
  lemma_mul_assoc (uint_v c') (x_i 1) (x_i i);
  lemma_mult_x1_xi1 (i + 1) (x_i 1) (x_i i);
  assert (eval_i len res' (i + 1) + uint_v c' * x_i (i + 1)  == eval_i len a (i + 1) + eval_i len b (i + 1));
  (c', res')

val bn_add_:
  len:size_nat{len > 0} -> a:lseqbn len -> b:lseqbn len -> c:uint64 -> res:lseqbn len -> Pure (tuple2 carry (lseqbn len))
  (requires (bn_add_pred len a b 0 (c, res)))
  (ensures (fun (c', res') -> bn_add_pred len a b len (c', res')))
let bn_add_ len a b c res =
  repeati_inductive len (bn_add_pred len a b) (bn_add_f len a b) (c, res)

val bn_add:
  len:size_nat{len > 0} -> a:lseqbn len -> b:lseqbn len -> Pure (tuple2 carry (lseqbn len))
  (requires True)
  (ensures (fun (c', res') -> eval_i len res' len + uint_v c' * x_i len = eval_i len a len + eval_i len b len))
let bn_add len a b =
  let res = create len (u64 0) in
  bn_add_ len a b (u64 0) res

(*
(* MULTIPLICATION *)

val lemma_mult_add_add_64:
    a:uint64 -> b:uint64 -> c:uint64 -> d:uint64 -> Lemma
    (uint_v a * uint_v b + uint_v c + uint_v d < pow2 128)

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let lemma_mult_add_add_64 a b c d =
    let n = pow2 64 in
    assert (uint_v a <= n - 1 /\ uint_v b <= n - 1 /\ uint_v c <= n - 1 /\ uint_v d <= n - 1);
    assert (uint_v a * uint_v b + uint_v c + uint_v d <= (n - 1) * (n - 1) + (n - 1) + (n - 1));
    assert ((n - 1) * (n - 1) + (n - 1) + (n - 1) == n * n - 1);
    pow2_plus 64 64

assume val mult_by_limb_addj_f:
    a_i:uint64 -> l:uint64 -> c:uint64 -> r_ij:uint64 -> Pure (tuple2 carry uint64)
    (requires (True))
    (ensures (fun (c', r) -> uint_v r + uint_v c' * x_i 1 == uint_v a_i * uint_v l + uint_v c + uint_v r_ij))

(*
let mult_by_limb_addj_f a_i l c r_ij =
    lemma_mult_add_add_64 a_i l c r_ij;
    //let res = mul_wide a_i l +! to_u128 c +! to_u128 r_ij in
    let res = to_u128 c +! to_u128 r_ij in
    let r = to_u64 res in
    let c' = res >>. u32 64 in
    let c' = to_u64 c' in
    lemma_div_mod (uint_v a_i * uint_v l + uint_v c + uint_v r_ij) (pow2 64);
    (c', r)
*)

(* (forall k. (v i1 + v j <= k /\ k < v resLen) ==> res.[uint_to_t k] = r1.[uint_to_t k]) *)
val mult_by_limb_addj_inner:
    len:size_nat -> a:lseqbn len -> l:uint64 -> i1:size_nat{i1 < len} ->
    j:size_nat -> resLen:size_nat{len + j < resLen} ->
    res:lseqbn resLen -> c1:carry -> r1:lseqbn resLen -> Pure (tuple2 carry (lseqbn resLen))
    (requires (eval_i resLen r1 (i1 + j) + uint_v c1 * x_i (i1 + j) == eval_i resLen res (i1 + j) + eval_i len a i1 * uint_v l * x_i j /\
	      uint_v res.[i1 + j] = uint_v r1.[i1 + j]))
    (ensures (fun (c', res') -> let i = i1 + 1 in
	      eval_i resLen res' (i + j) + uint_v c' * x_i (i + j) == eval_i resLen res (i + j) + eval_i len a i * uint_v l * x_i j))

#reset-options "--z3rlimit 150 --max_fuel 0"

let mult_by_limb_addj_inner len a l i1 j resLen res c1 r1 =
    let i = i1 + 1 in
    let (c', res_ij) = mult_by_limb_addj_f a.[i1] l c1 r1.[i1 + j] in
    assert (uint_v res_ij + uint_v c' * x_i 1 == uint_v a.[i1] * uint_v l + uint_v c1 + uint_v r1.[i1 + j]);
    let res' = r1.[i1 + j] <- res_ij in
    lemma_eval_i resLen r1 res' (i1 + j);
    lemma_eval_incr resLen res' (i + j);
    assert (eval_i resLen res' (i + j) == eval_i resLen res' (i + j - 1) + uint_v res'.[i + j - 1] * x_i (i + j - 1));
    assert (eval_i resLen res' (i1 + j) == eval_i resLen r1 (i1 + j));
    assert (eval_i resLen res' (i + j) == eval_i resLen res (i1 + j) + eval_i len a i1 * uint_v l * x_i j - uint_v c1 * x_i (i1 + j) +
            (uint_v a.[i1] * uint_v l + uint_v c1 + uint_v r1.[i1 + j] - uint_v c' * x_i 1) * x_i (i1 + j));
    lemma_distributivity_add_add_sub (uint_v a.[i1] * uint_v l) (uint_v c1) (uint_v r1.[i1 + j]) (uint_v c' * x_i 1) (x_i (i1 + j));
    lemma_mult_x1_xi1 (i + j) (x_i 1) (x_i (i1 + j));
    assert (eval_i resLen res' (i + j) + uint_v c' * x_i (i + j) ==
            eval_i resLen res (i1 + j) + eval_i len a i1 * uint_v l * x_i j + uint_v a.[i1] * uint_v l * x_i (i1 + j) + uint_v r1.[i1 + j] * x_i (i1 + j));
    lemma_eval_incr resLen res (i + j);
    lemma_mult_xi_xj i1 j (x_i i1) (x_i j);
    lemma_eval_incr len a i;
    (c', res')

//(forall k. (v i + v j <= k /\ k < v resLen) ==> res.[uint_to_t k] = res'.[uint_to_t k])
val mult_by_limb_addj_:
    len:size_nat{len > 0} -> a:lseqbn len -> l:uint64 -> i:size_nat{i <= len} ->
    j:size_nat -> resLen:size_nat{len + j < resLen} ->
    res:lseqbn resLen -> Pure (tuple2 carry (lseqbn resLen))
    (requires (True))
    (ensures (fun (c', res') -> eval_i resLen res' (i + j) + uint_v c' * x_i (i + j) == eval_i resLen res (i + j) + eval_i len a i * uint_v l * x_i j /\
                             (forall k. (i + j <= k /\ k < resLen) ==> uint_v res.[k] = uint_v res'.[k])))
    (decreases i)

#reset-options "--z3rlimit 100 --max_fuel 2"

let rec mult_by_limb_addj_ len a l i j resLen res =
    if i = 0 then
        (u64 0, res)
    else begin
        let i1 = i - 1 in
        let (c1, r1) = mult_by_limb_addj_ len a l i1 j resLen res in
        assert (uint_v res.[i1 + j] = uint_v r1.[i1 + j]); //from ind hypo
        let (c', res') = mult_by_limb_addj_inner len a l i1 j resLen res c1 r1 in
        (c', res')
    end

val mult_by_limb_addj:
    len:size_nat{len > 0} -> a:lseqbn len -> l:uint64 -> j:size_nat ->
    resLen:size_nat{len + j < resLen} ->
    res:lseqbn resLen -> Pure (tuple2 carry (lseqbn resLen))
    (requires (True))
    (ensures (fun (c', res') -> eval_i resLen res' (len + j) + uint_v c' * x_i (len + j) == eval_i resLen res (len + j) + eval len a * uint_v l * x_i j))

let mult_by_limb_addj len a l j resLen res = mult_by_limb_addj_ len a l len j resLen res


val mult_inner:
    len:size_nat -> a:lseqbn len -> b:lseqbn len ->
    resLen:size_nat{resLen = len + len} ->
    j1:size_nat{j1 < len} -> r:lseqbn resLen -> Pure (lseqbn resLen)
    (requires (eval_i resLen r (len + j1) == eval len a * eval_i len b j1))
    (ensures (fun res' -> let j = j1 + 1 in
        eval_i resLen res' (len + j) == eval len a * eval_i len b j))

#reset-options "--z3rlimit 300 --max_fuel 0"

let mult_inner len a b resLen j1 r =
    let j = j1 + 1 in
    assert (eval_i resLen r (len + j1) + eval len a * uint_v b.[j1] * x_i j1 == eval len a * eval_i len b j1 + eval len a * uint_v b.[j1] * x_i j1);
    lemma_distributivity_add_fold (eval len a) (eval_i len b j1) (uint_v b.[j1] * x_i j1);
    lemma_eval_incr len b j;
    assert (eval_i resLen r (len + j1) + eval len a * uint_v b.[j1] * x_i j1 == eval len a * eval_i len b j);

    let (c', res') = mult_by_limb_addj len a b.[j1] j1 resLen r in
    assert (eval_i resLen res' (len + j1) + uint_v c' * x_i (len + j1) == eval len a * eval_i len b j);
    let res1 = res'.[len + j1] <- c' in
    lemma_eval_i resLen res' res1 (len + j1);
    lemma_eval_incr resLen res1 (len + j);
    assert (eval_i resLen res1 (len + j) == eval len a * eval_i len b j);
    res1

val mult_:
    len:size_nat{len > 0} -> a:lseqbn len -> b:lseqbn len ->
    resLen:size_nat{resLen = len + len} ->
    j:size_nat{j <= len} -> Tot (res':lseqbn resLen{eval_i resLen res' (len + j) == eval len a * eval_i len b j})
    (decreases j)

#reset-options "--z3rlimit 50 --max_fuel 2"

let rec mult_ len a b resLen j  =
    if j = 0 then begin
        let res' = create resLen (u64 0) in
        lemma_eval_init_seq_is_0 resLen res' (len + j);
        res' end
    else begin
        let j1 = j - 1 in
        let r = mult_ len a b resLen j1 in
        mult_inner len a b resLen j1 r
    end

val mult:
    len:size_nat{len > 0} -> a:lseqbn len -> b:lseqbn len ->
    resLen:size_nat{resLen = len + len} ->
    Tot (res':lseqbn resLen{eval resLen res' == eval len a * eval len b})

let mult len a b resLen = mult_ len a b resLen len
*)
