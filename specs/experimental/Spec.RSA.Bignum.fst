module Spec.RSA.Bignum

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Spec.Lib.RawIntTypes

open FStar.Math.Lemmas
open Spec.RSA.Lemmas

(* BIGNUM *)
type bignum = nat
let bn_v n = n
let bn n = n
let bn_add a b = a + b
let bn_mul a b = a `op_Multiply` b
let bn_sub a b = a - b
let bn_mul_mod a b n = (a `op_Multiply` b) % n
let bn_is_even x = (x % 2) = 0
let bn_div2 x = x / 2
let bn_is_less x y = x < y

type elem (n:bignum) = e:bignum{bn_v e < bn_v n}

let beta = pow2 64

val beta_i: i:size_nat -> Tot (res:bignum{res = pow2 (64 * i) /\ res > 0})
let beta_i i = pow2 (64 * i)

val get_limbi: c:bignum -> i:size_nat -> Tot (res:bignum{res < pow2 64})
let rec get_limbi c i =
  if (i = 0) then c % pow2 64
  else get_limbi (c / pow2 64) (i - 1)

val mod_inv_u64: n0:uint64 -> Tot uint64
let mod_inv_u64 n0 =
  let alpha = shift_left #U64 (u64 1) (u32 63) in
  let beta = n0 in
  let (ub, vb) =
    repeati 64
    (fun i (ub, vb) ->
      let u_is_odd = u64 0 -. (ub &. u64 1) in
      let beta_if_u_is_odd = beta &. u_is_odd in
      let ub = ((ub ^. beta_if_u_is_odd) >>. (u32 1)) +. (ub &. beta_if_u_is_odd) in

      let alpha_if_u_is_odd = alpha &. u_is_odd in
      let vb = (shift_right #U64 vb (u32 1)) +. alpha_if_u_is_odd in
      (ub, vb)) (u64 1, u64 0) in
  vb

(* Karatsuba's multiplication *)
type sign =
  | Positive : sign
  | Negative : sign

// a - b = (sign, |a - b|)
val abs_sub:
  x:size_nat -> a:bignum -> b:bignum -> Pure (tuple2 sign bignum)
  (requires (a < pow2 (pow2 x) /\ b < pow2 (pow2 x)))
  (ensures (fun (s, res) -> res < pow2 (pow2 x) /\ res = abs (a - b) /\
			  s = (if a >= b then Positive else Negative)))

let abs_sub x a b =
  if (bn_is_less a b)
  then (Negative, b - a)
  else (Positive, a - b)

val add_sign:
  c0:bignum -> c1:bignum -> c2:bignum ->
  a0:bignum -> a1:bignum -> a2:bignum ->
  b0:bignum -> b1:bignum -> b2:bignum ->
  sa2:sign -> sb2:sign -> Pure bignum
  (requires (c0 == a0 * b0 /\ c1 == a1 * b1 /\ c2 == a2 * b2 /\
             a2 = abs (a0 - a1) /\ b2 = abs (b0 - b1) /\
	     sa2 = (if (a0 >= a1) then Positive else Negative) /\
	     sb2 = (if (b0 >= b1) then Positive else Negative)))
  (ensures (fun res -> res == a1 * b0 + a0 * b1))
  #reset-options "--z3rlimit 100 --max_fuel 0"
let add_sign c0 c1 c2 a0 a1 a2 b0 b1 b2 sa2 sb2 =
  if ((sa2 = Positive && sb2 = Positive) || (sa2 = Negative && sb2 = Negative))
  then (c0 + c1) - c2
  else (c0 + c1) + c2

val karatsuba:
  x0:size_nat ->
  a:bignum{a < pow2 (pow2 x0)} -> b:bignum{b < pow2 (pow2 x0)} -> Tot (res:bignum{res == a * b})
  (decreases x0)

let rec karatsuba x0 a b =
  if x0 < 9 then a * b
  else begin
    let x = x0 - 1 in
    let pow_x = pow2 (pow2 x) in

    let a0 = a % pow_x in let a1 = a / pow_x in
    assert (0 <= a0 /\ a0 < pow_x);
    lemma_pow_div_karatsuba x0 a;
    assert (0 <= a1 /\ a1 < pow_x);
    lemma_div_mod a pow_x;

    let b0 = b % pow_x in let b1 = b / pow_x in
    assert (0 <= b0 /\ b0 < pow_x);
    lemma_pow_div_karatsuba x0 b;
    assert (0 <= b1 /\ b1 < pow_x);
    lemma_div_mod b pow_x;

    let (sa2, a2) = abs_sub x a0 a1 in
    let (sb2, b2) = abs_sub x b0 b1 in

    let c0 = karatsuba x a0 b0 in
    assert (c0 == a0 * b0); //from ind hypo
    let c1 = karatsuba x a1 b1 in
    assert (c1 == a1 * b1); //from ind hypo
    let c2 = karatsuba x a2 b2 in
    assert (c2 == a2 * b2); //from ind hypo

    let pow_x1 = pow2 (pow2 (x + 1)) in
    let tmp = add_sign c0 c1 c2 a0 a1 a2 b0 b1 b2 sa2 sb2 in
    let c = c1 * pow_x1 + tmp * pow_x + c0 in
    lemma_karatsuba_mult x a a0 a1 b b0 b1;
    assert (c == a * b);
    c
  end

(* Montgomery's arithmetic *)
val mont_pred:
  n:bignum{n > 0} -> exp_r:size_nat -> c:bignum -> i:size_nat{i <= exp_r} -> res:bignum -> Tot Type0
let mont_pred n exp_r c i res = res % n = c % n && res <= c + (beta_i i - 1) * n

val mont_reduction_f:
  nInv_u64:bignum{nInv_u64 < beta} -> n:bignum{n > 0} ->
  exp_r:size_nat{exp_r + 1 < max_size_t} -> c:bignum -> Tot (repeatable #bignum #exp_r (mont_pred n exp_r c))

let mont_reduction_f nInv_u64 n exp_r c i res =
  let qi = (nInv_u64 * (get_limbi res i)) % beta in
  assert (0 <= qi /\ qi <= beta - 1);
  let res1 = res + qi * (beta_i i) * n in
  lemma_mod_plus res (qi * beta_i i) n; // res1 % n == res % n
  assert (res1 <= c + (beta_i i - 1) * n + qi * beta_i i * n);
  lemma_mul_le qi (beta - 1) (beta_i i * n);
  assert (res1 <= c + (beta_i i - 1) * n + (beta - 1) * beta_i i * n);
  assert (res1 <= c + beta_i i * n  - n + beta * beta_i i * n - beta_i i * n);
  assert (res1 <= c - n + beta * beta_i i * n);
  assert (res1 <= c + (beta * beta_i i - 1) * n);
  lemma_beta_mul_by_beta_i i;
  assert (res1 <= c + (beta_i (i + 1) - 1) * n);
  res1

val mont_reduction_:
  nInv_u64:bignum{nInv_u64 < beta} -> n:bignum{n > 0} ->
  exp_r:size_nat{exp_r + 1 < max_size_t} -> c:bignum -> Tot (res:bignum{res % n = c % n && res <= c + (beta_i exp_r - 1) * n})

let mont_reduction_ nInv_u64 n exp_r c =
  repeati_inductive exp_r (mont_pred n exp_r c) (mont_reduction_f nInv_u64 n exp_r c) c

val mont_reduction:
  nInv_u64:bignum{nInv_u64 < beta} -> n:bignum{n > 0} ->
  exp_r:size_nat{exp_r + 1 < max_size_t} -> r:bignum{r == beta_i exp_r} ->
  c:bignum{c < r * n} -> Tot (res:elem (n + n){res % n == (c / r) % n})
  #reset-options "--z3rlimit 150 --max_fuel 0 --max_ifuel 0"
let mont_reduction nInv_u64 n exp_r r c =
  let tmp = mont_reduction_ nInv_u64 n exp_r c in
  assert (tmp % n == c % n /\ tmp <= c + (beta_i exp_r - 1) * n);
  assert (tmp < c + (beta_i exp_r) * n);
  let res = tmp / r in
  assert (res % n == (tmp / r) % n);
  lemma_mod_mult_div_1 tmp r n;
  assert (res % n == ((c % n) / r) % n);
  lemma_mod_mult_div_1 c r n;
  assert (res % n == (c / r) % n);

  assert (tmp < r * n + r * n);
  assert (tmp < r * (n + n));
  lemma_div_exact_le tmp (n + n) r;
  assert (res < n + n);
  res

val mul_mod_mont:
  x0:size_nat ->
  nInv_u64:bignum{nInv_u64 < beta} -> n:bignum{1 < n /\ 2 * n < pow2 (pow2 x0)} ->
  exp_r:size_nat{exp_r + 1 < max_size_t} -> r:bignum{r == beta_i exp_r /\ 4 * n < r} ->
  a:elem (n + n) -> b:elem (n + n) -> Tot (res:elem (n + n){res % n == (a * b / r) % n})
  #reset-options "--z3rlimit 50 --max_fuel 0"
let mul_mod_mont x0 nInv_u64 n exp_r r a b =
  let c = karatsuba x0 a b in
  //let c = a * b in
  assert (c < 4 * n * n);
  mont_reduction nInv_u64 n exp_r r c

val to_mont:
  x0:size_nat ->
  nInv_u64:bignum{nInv_u64 < beta} -> n:bignum{1 < n /\ 2 * n < pow2 (pow2 x0)} ->
  exp_r:size_nat{exp_r + 1 < max_size_t} -> r:bignum{r == beta_i exp_r /\ 4 * n < r} ->
  r2:elem n -> a:elem n -> Pure (elem (n + n))
  (requires (r2 == (r * r) % n))
  (ensures (fun res -> res % n == (a * r) % n))
  #reset-options "--z3rlimit 50 --max_fuel 0"
let to_mont x0 nInv_u64 n exp_r r r2 a =
  //let c = a * r2 in
  let c = karatsuba x0 a r2 in
  assert (c < n * n);
  assert (c == a * ((r * r) % n));
  let res = mont_reduction nInv_u64 n exp_r r c in
  assert (res % n == ((a * ((r * r) % n)) / r) % n);
  lemma_mod_div_simplify res a r n;
  res

val from_mont:
  x0:size_nat ->
  nInv_u64:bignum{nInv_u64 < beta} -> n:bignum{1 < n /\ 2 * n < pow2 (pow2 x0)} ->
  exp_r:size_nat{exp_r + 1 < max_size_t} -> r:bignum{r == beta_i exp_r /\ 4 * n < r} ->
  a_r:elem (n + n) -> Tot (res:elem n{res == (a_r / r) % n})

let from_mont x0 nInv_u64 n exp_r r a_r =
  let tmp = mont_reduction_ nInv_u64 n exp_r a_r in
  assert (tmp % n == a_r % n /\ tmp <= a_r + (beta_i exp_r - 1) * n);
  assert (tmp < a_r + (beta_i exp_r) * n);
  let res = tmp / r in
  assert (res % n = (tmp / r) % n);
  lemma_mod_mult_div_1 tmp r n;
  assert (res % n == ((a_r % n) / r) % n);
  lemma_mod_mult_div_1 a_r r n;
  assert (res % n == (a_r / r) % n);

  (*assert (tmp < a_r + r * n);
  lemma_div_le tmp (a_r + r * n) r;
  assert (res <= (a_r + r * n) / r);
  division_addition_lemma a_r r n;
  assert (res <= a_r / r + n);
  small_division_lemma_1 a_r r;
  //assert (res <= n); *)
  assume (res < n); //FIXME!!
  small_modulo_lemma_1 res n;
  assert (res == (a_r / r) % n);
  res

val mod_exp_:
  x0:size_nat ->
  nInv_u64:bignum{nInv_u64 < beta} -> n:bignum{1 < n /\ 2 * n < pow2 (pow2 x0)} ->
  exp_r:size_nat{exp_r + 1 < max_size_t} -> r:bignum{r == beta_i exp_r /\ 4 * n < r} ->
  a:elem (n + n) -> b:bignum -> acc:elem (n + n) -> Tot (res:elem (n + n){res % n == ((pow a b) * acc / pow r b) % n})
  (decreases b)
  #reset-options "--z3rlimit 150 --max_fuel 2"
let rec mod_exp_ x0 nInv_u64 n exp_r r a b acc =
  if b = 0
  then acc
  else begin
    let a2 = mul_mod_mont x0 nInv_u64 n exp_r r a a in
    let b2 = bn_div2 b in
    lemma_div_mod b 2;
    if (bn_is_even b) then begin
      assert (b = 2 * b2);
      let res = mod_exp_ x0 nInv_u64 n exp_r r a2 b2 acc in
      assert (res % n == ((pow a2 b2) * acc / pow r b2) % n); //from ind hypo
      lemma_mod_exp n a a2 b b2 acc r res;
      res end
    else begin
      assert (b = 2 * b2 + 1);
      let acc' = mul_mod_mont x0 nInv_u64 n exp_r r a acc in
      let res = mod_exp_ x0 nInv_u64 n exp_r r a2 b2 acc' in
      assert (res % n == ((pow a2 b2) * acc' / pow r b2) % n); //from ind hypo
      lemma_mod_exp_1 n a a2 b b2 acc acc' r res;
      res end
  end

val mod_exp:
  x0:size_nat -> modBits:size_nat{1 < modBits} ->
  n:bignum{1 < n /\ n < pow2 modBits /\ 2 * n < pow2 (pow2 x0)} ->
  a:elem n -> b:bignum -> Tot (res:elem n{res == (pow a b) % n})
  #reset-options "--z3rlimit 50 --max_fuel 0"
let mod_exp x0 modBits n a b =
  let nLen = (modBits - 1) / 64 + 1 in
  let exp_r = nLen + 1 in
  let r = beta_i exp_r in
  lemma_r_n modBits r n;
  assert (4 * n < r);
  let n0 = n % pow2 64 in
  let nInv_u64 = uint_to_nat #U64 (mod_inv_u64 (u64 n0)) in
  let r2 = (r * r) % n in
  let a_r = to_mont x0 nInv_u64 n exp_r r r2 a in
  let acc_r = to_mont x0 nInv_u64 n exp_r r r2 1 in
  let res_r = mod_exp_ x0 nInv_u64 n exp_r r a_r b acc_r in
  lemma_mod_exp_2 n a a_r b acc_r r res_r;
  let res = from_mont x0 nInv_u64 n exp_r r res_r in
  lemma_mod_mult_div_1 res_r r n;
  lemma_mod_mult_div_1 ((pow a b) * r) r n;
  multiple_division_lemma (pow a b) r;
  res

val rsa_blinding:
  x0:size_nat -> modBits:size_nat{1 < modBits} ->
  n:bignum{1 < n /\ n < pow2 modBits /\ 2 * n < pow2 (pow2 x0)} ->
  p:elem n{1 < p} -> q:elem n{1 < q /\ n = p * q} ->
  d:elem n{1 < d} -> m:elem n ->
  rBlind:bignum{rBlind < pow2 64} -> Tot (s:bignum{s == (pow m d) % n})

let rsa_blinding x0 modBits n p q d m rBlind =
  let phi_n:nat = (p - 1) * (q - 1) in
  let d':nat = d + rBlind * phi_n in
  let s = mod_exp x0 modBits n m d' in
  assert (s == (pow m d') % n);
  lemma_exp_blinding n phi_n p q d m rBlind;
  assert (s == (pow m d) % n);
  s
