module Spec.RSA.Lemmas

open FStar.Mul
open FStar.Math.Lemmas
open Spec.Lib.IntTypes
open Spec.Bignum.Basic

(* LEMMAS *)
#reset-options "--z3rlimit 30 --max_fuel 2"
val pow : x:nat -> n:nat -> Tot nat
let rec pow x n =
  match n with
  | 0 -> 1
  | n -> x * pow x (n - 1)

val lemma_pow: x:nat -> n:nat -> m:nat -> Lemma
  (pow x n * pow x m = pow x (n + m))
let rec lemma_pow x n m =
  let ass (x y z : nat) : Lemma ((x*y)*z == x*(y*z)) = () in
  match n with
  | 0 -> ()
  | _ -> lemma_pow x (n-1) m; ass x (pow x (n-1)) (pow x m)

val lemma_pow_greater_0: a:nat{a > 0} -> b:nat -> Lemma
  (pow a b > 0)
  [SMTPat (pow a b)]
let rec lemma_pow_greater_0 a b =
  match b with
  | 0 -> ()
  | _ -> lemma_pow_greater_0 a (b - 1)

val lemma_pow_0: b:nat{b > 0} -> Lemma (pow 0 b = 0)
let rec lemma_pow_0 b =
  match b with
  | 1 -> ()
  | _ -> lemma_pow_0 (b - 1)

val lemma_pow_1: b:nat -> Lemma (pow 1 b = 1)
let rec lemma_pow_1 b =
  match b with
  |  0 -> ()
  | _ -> lemma_pow_1 (b - 1)

#reset-options "--z3rlimit 30 --max_fuel 0"

val lemma_pow_pow:
  a:nat -> b:nat -> c:nat -> Lemma
  (pow a (b * c) = pow (pow a b) c)
let lemma_pow_pow a b c = admit()

val lemma_pow_mul:
  a:nat -> b:nat -> c:nat -> Lemma
  (pow (a * b) c = (pow a c) * (pow b c))
let lemma_pow_mul a b c = admit()

val lemma_pow_mod:
  a:nat -> b:nat -> n:pos -> Lemma
  ((pow a b) % n == (pow (a % n) b) % n)
let lemma_pow_mod a b n = admit()

// (1 / d) % n is an inverse element of d
val lemma_mod_mult_div_1:
  a:nat -> d:nat{d > 0} -> n:nat{n > 0} -> Lemma
  ((a / d) % n == ((a % n) / d) % n)
let lemma_mod_mult_div_1 a d n = admit()

val lemma_mod_mult_div:
  a:nat -> b:nat -> d:nat{d > 0} -> n:nat{n > 0} -> Lemma
  ((a * b / d) % n == ((a % n) * b / d) % n)
let lemma_mod_mult_div a b d n =
  lemma_mod_mult_div_1 (a * b) d n;
  lemma_mod_mul_distr_l a b n;
  lemma_mod_mult_div_1 ((a % n) * b) d n

val lemma_mul_div_mod:
  a:nat -> b:pos -> c:nat -> d:pos -> e:pos -> n:pos -> Lemma
  (((a / b) * (c / d)) / e % n == ((a * c) / (b * d * e)) % n)
let lemma_mul_div_mod a b c d e n = admit()

(* Lemmas for Montgomery's arithmetic *)
val lemma_mont_reduction_f:
  #nBits:size_pos -> #cBits:size_pos ->
  rBits:size_pos{nBits < rBits /\ nBits + 1 + rBits < max_size_t} ->
  n:bignum nBits{bn_v n > 0} ->
  c:bignum cBits{cBits < nBits + rBits} -> i:size_nat{64*(i+1)<=rBits} -> Lemma
  (requires True)
  (ensures (bn_v c + (pow2 (64*(i+1)) - 1) * bn_v n < pow2 (nBits+1+rBits)))
  #reset-options "--z3rlimit 50 --max_fuel 0"
let lemma_mont_reduction_f #nBits #cBits rBits n c i =
  pow2_le_compat rBits (64*(i+1));
  assert (bn_v c + (pow2 (64*(i+1)) - 1) * bn_v n < pow2 cBits + pow2 rBits * pow2 nBits);
  pow2_plus rBits nBits;
  pow2_lt_compat (nBits+rBits) cBits;
  assert (bn_v c + (pow2 (64*(i+1)) - 1) * bn_v n < pow2 (nBits+rBits) + pow2 (nBits+rBits));
  pow2_double_sum (nBits+rBits)

val lemma_mont_reduction:
  #nBits:size_pos -> #cBits:size_pos ->
  rBits:size_pos{nBits < rBits /\ nBits+1+rBits < max_size_t} ->
  n:bignum nBits{bn_v n > 0} ->
  c:bignum cBits{cBits < nBits + rBits} -> Lemma
  (requires True)
  (ensures (bn_v c + (pow2 rBits - 1) * bn_v n < pow2 (nBits+1+rBits)))
  #reset-options "--z3rlimit 50 --max_fuel 0"
let lemma_mont_reduction #nBits #cBits rBits n c =
  assert (bn_v c + (pow2 rBits - 1) * bn_v n < pow2 cBits + pow2 rBits * pow2 nBits);
  pow2_plus rBits nBits;
  pow2_lt_compat (nBits+rBits) cBits;
  assert (bn_v c + (pow2 rBits - 1) * bn_v n < pow2 (nBits+rBits) + pow2 (nBits+rBits));
  pow2_double_sum (nBits+rBits)

val lemma_mont_reduction_fi:
  #nBits:size_pos -> #cBits:size_pos ->
  rBits:size_pos{nBits < rBits /\ nBits+1+rBits < max_size_t} ->
  qi:bignum 64 -> n:bignum nBits{bn_v n > 0} ->
  c:bignum cBits ->
  i:size_nat{i <= rBits / 64} -> res:bignum (nBits + 1 + rBits) -> Lemma
  (requires (bn_v res + bn_v n * pow2 (64*i) * bn_v qi <= bn_v c + (pow2 (64*i)-1) * bn_v n + bn_v n * pow2 (64*i) * bn_v qi))
  (ensures (bn_v res + bn_v n * pow2 (64*i) * bn_v qi <= bn_v c + (pow2 (64*(i+1)) - 1) * bn_v n))
  #reset-options "--z3rlimit 150 --max_fuel 0"
let lemma_mont_reduction_fi #nBits #cBits rBits qi n c i res =
  let res1 = bn_v res + bn_v n * pow2 (64*i) * bn_v qi in
  assert (res1 <= bn_v c + (pow2 (64*i)-1) * bn_v n + bn_v n * pow2 (64*i) * bn_v qi); //from ind hypo
  assert (bn_v qi < pow2 64);
  assert (res1 <= bn_v c + (pow2 (64*i)-1) * bn_v n + bn_v n * pow2 (64*i) * (pow2 64 - 1));
  assert (res1 <= bn_v c + pow2 (64*i) * bn_v n - bn_v n + bn_v n * pow2 (64*i) * (pow2 64 - 1));
  assert (res1 <= bn_v c + pow2 (64*i) * bn_v n - bn_v n + bn_v n * pow2 (64*i) * pow2 64 - bn_v n * pow2 (64*i));
  assert (res1 <= bn_v c - bn_v n + bn_v n * pow2 (64*i) * pow2 64);
  assert (res1 <= bn_v c + (pow2 (64*i) * pow2 64 - 1) * bn_v n);
  pow2_plus (64*i) 64;
  assert (res1 <= bn_v c + (pow2 (64*(i+1)) - 1) * bn_v n)

(* LEMMAS for modular exponentiation *)
assume val bn_get_bits_first:#n:size_pos -> b:bignum n -> i:size_nat{i <= n} -> Tot (c:bignum i{bn_v c == bn_v b % pow2 i})

val lemma_get_bit_first:
  bBits:size_pos -> b:bignum bBits -> i:size_nat{i < bBits} -> Lemma
  (bn_v b % pow2 (i+1) == bn_v b % pow2 i + pow2 i * bn_get_bit b i)
let lemma_get_bit_first bBits b i =
  let c = bn_v b % pow2 (i+1) in
  euclidean_division_definition c (pow2 i);
  pow2_modulo_modulo_lemma_1 (bn_v b) i (i+1);
  pow2_modulo_division_lemma_1 (bn_v b) i (i+1)

val mod_exp_pred:
  nBits:size_pos ->
  rBits:size_pos{nBits + 1 < rBits /\ nBits + rBits + 1 < max_size_t /\ rBits % 64 == 0} ->
  nInv_u64:bignum 64 -> n:bignum nBits{bn_v n > 0} ->
  bBits:size_pos -> b:bignum bBits ->
  a0:bignum (nBits+1) -> acc0:bignum (nBits+1) ->
  i:size_nat{i <= bBits} ->
  a_acc:tuple2 (bignum (nBits+1)) (bignum (nBits+1)) -> Tot Type0
let mod_exp_pred nBits rBits nInv_u64 n bBits b a0 acc0 i (a, acc) =
  if i = 0 then
    bn_v acc % bn_v n = bn_v acc0 % bn_v n &&
    bn_v a % bn_v n = bn_v a0 % bn_v n
  else
    bn_v acc % bn_v n = ((pow (bn_v a0) (bn_v (bn_get_bits_first b i)) * bn_v acc0) / pow (pow2 rBits) (bn_v (bn_get_bits_first b i))) % bn_v n &&
    bn_v a % bn_v n = (pow (bn_v a0) (pow2 i) / pow (pow2 rBits) (pow2 i - 1)) % bn_v n

val lemma_mod_exp_f1:
  nBits:size_pos -> rBits:size_pos{nBits + 2 < rBits /\ nBits + rBits + 1 < max_size_t /\ rBits % 64 == 0} ->
  nInv_u64:bignum 64 -> n:bignum nBits{bn_v n > 0} ->
  bBits:size_pos -> b:bignum bBits ->
  a0:bignum (nBits+1) -> acc0:bignum (nBits+1) ->
  a:bignum (nBits+1) -> acc:bignum (nBits+1) ->
  a1:bignum (nBits+1) -> i:size_nat{i < bBits /\ bn_get_bit b i = 0} -> Lemma
  (requires (mod_exp_pred nBits rBits nInv_u64 n bBits b a0 acc0 i (a, acc) /\
             bn_v a1 % bn_v n = (pow (bn_v a0) (pow2 (i+1)) / pow (pow2 rBits) (pow2 (i+1) - 1)) % bn_v n))
  (ensures (mod_exp_pred nBits rBits nInv_u64 n bBits b a0 acc0 (i+1) (a1, acc)))
  #reset-options "--z3rlimit 150 --max_fuel 0"
let lemma_mod_exp_f1 nBits rBits nInv_u64 n bBits b a0 acc0 a acc a1 i =
  lemma_get_bit_first bBits b i;
  assert (bn_v (bn_get_bits_first b (i+1)) == bn_v (bn_get_bits_first b i) + pow2 i * bn_get_bit b i);
  assert (bn_v (bn_get_bits_first b (i+1)) == bn_v (bn_get_bits_first b i));
  if i = 0 then begin
     assert (bn_v acc % bn_v n == bn_v acc0 % bn_v n);
     assert (bn_v a % bn_v n = bn_v a0 % bn_v n);
     assert_norm (bn_v (bn_get_bits_first b i) == 0);
     assert_norm (pow (bn_v a0) (bn_v (bn_get_bits_first b (i+1))) == 1);
     assert_norm (pow (pow2 rBits) (bn_v (bn_get_bits_first b (i+1))) == 1);
     assert (mod_exp_pred nBits rBits nInv_u64 n bBits b a0 acc0 (i+1) (a1, acc)) end
  else begin
     assert (bn_v acc % bn_v n = ((pow (bn_v a0) (bn_v (bn_get_bits_first b i)) * bn_v acc0) / pow (pow2 rBits) (bn_v (bn_get_bits_first b i))) % bn_v n);
     assert (mod_exp_pred nBits rBits nInv_u64 n bBits b a0 acc0 (i+1) (a1, acc))
  end

val lemma_mul_mul:
  a:nat -> b:nat -> c:nat -> Lemma
  (a * b * c == a * c * b)
let lemma_mul_mul a b c = ()

val lemma_mod_exp_f20:
  nBits:size_pos -> rBits:size_pos{nBits + 2 < rBits /\ nBits + rBits + 1 < max_size_t /\ rBits % 64 == 0} ->
  nInv_u64:bignum 64 -> n:bignum nBits{bn_v n > 0} ->
  bBits:size_pos -> b:bignum bBits ->
  a0:bignum (nBits+1) -> acc0:bignum (nBits+1) ->
  a:bignum (nBits+1) -> acc:bignum (nBits+1) ->
  a1:bignum (nBits+1) -> acc1:bignum (nBits+1) ->
  i:size_nat{0 < i /\ i < bBits /\ bn_get_bit b i = 1} -> Lemma
  (requires (mod_exp_pred nBits rBits nInv_u64 n bBits b a0 acc0 i (a, acc) /\
             bn_v a1 % bn_v n == (pow (bn_v a0) (pow2 (i+1)) / pow (pow2 rBits) (pow2 (i+1) - 1)) % bn_v n /\
	     bn_v acc1 % bn_v n == ((bn_v a * bn_v acc) / pow2 rBits) % bn_v n))
  (ensures (mod_exp_pred nBits rBits nInv_u64 n bBits b a0 acc0 (i+1) (a1, acc1)))
  #reset-options "--z3rlimit 150 --max_fuel 0"
let lemma_mod_exp_f20 nBits rBits nInv_u64 n bBits b a0 acc0 a acc a1 acc1 i =
  assert (bn_v acc1 % bn_v n == ((bn_v a * bn_v acc) / pow2 rBits) % bn_v n);
  lemma_mod_mult_div_1 (bn_v a * bn_v acc) (pow2 rBits) (bn_v n);
  lemma_mod_plus_mul_distr 0 (bn_v a) (bn_v acc) (bn_v n);
  let a_n = pow (bn_v a0) (pow2 i) / pow (pow2 rBits) (pow2 i - 1) in
  let acc_n = (pow (bn_v a0) (bn_v (bn_get_bits_first b i)) * bn_v acc0) / pow (pow2 rBits) (bn_v (bn_get_bits_first b i)) in
  lemma_mod_plus_mul_distr 0 a_n acc_n (bn_v n);
  lemma_mod_mult_div_1 (a_n * acc_n) (pow2 rBits) (bn_v n);
  assert (bn_v acc1 % bn_v n == ((a_n * acc_n) / pow2 rBits) % bn_v n);
  let al = pow (bn_v a0) (pow2 i) in
  let bl = pow (pow2 rBits) (pow2 i - 1) in
  let cl = pow (bn_v a0) (bn_v (bn_get_bits_first b i)) * bn_v acc0 in
  let dl = pow (pow2 rBits) (bn_v (bn_get_bits_first b i)) in
  lemma_mul_div_mod al bl cl dl (pow2 rBits) (bn_v n);
  assert (bn_v acc1 % bn_v n == ((al * cl) / (bl * dl * pow2 rBits)) % bn_v n);
  lemma_get_bit_first bBits b i;
  lemma_pow (bn_v a0) (pow2 i) (bn_v (bn_get_bits_first b i));
  assert (al * cl == pow (bn_v a0) (bn_v (bn_get_bits_first b (i+1))) * bn_v acc0);
  lemma_pow (pow2 rBits) (pow2 i - 1) 1;
  assert_norm (pow2 rBits == pow (pow2 rBits) 1);
  lemma_pow (pow2 rBits) (pow2 i) (bn_v (bn_get_bits_first b i));
  lemma_mul_mul  bl dl (pow2 rBits);
  assert (bl * dl * pow2 rBits == pow (pow2 rBits) (bn_v (bn_get_bits_first b (i+1))))

val lemma_mod_exp_f2:
  nBits:size_pos -> rBits:size_pos{nBits + 2 < rBits /\ nBits + rBits + 1 < max_size_t /\ rBits % 64 == 0} ->
  nInv_u64:bignum 64 -> n:bignum nBits{bn_v n > 0} ->
  bBits:size_pos -> b:bignum bBits ->
  a0:bignum (nBits+1) -> acc0:bignum (nBits+1) ->
  a:bignum (nBits+1) -> acc:bignum (nBits+1) ->
  a1:bignum (nBits+1) -> acc1:bignum (nBits+1) ->
  i:size_nat{i < bBits /\ bn_get_bit b i = 1} -> Lemma
  (requires (mod_exp_pred nBits rBits nInv_u64 n bBits b a0 acc0 i (a, acc) /\
             bn_v a1 % bn_v n == (pow (bn_v a0) (pow2 (i+1)) / pow (pow2 rBits) (pow2 (i+1) - 1)) % bn_v n /\
	     bn_v acc1 % bn_v n == ((bn_v a * bn_v acc) / pow2 rBits) % bn_v n))
  (ensures (mod_exp_pred nBits rBits nInv_u64 n bBits b a0 acc0 (i+1) (a1, acc1)))
  #reset-options "--z3rlimit 150 --max_fuel 0"
let lemma_mod_exp_f2 nBits rBits nInv_u64 n bBits b a0 acc0 a acc a1 acc1 i =
  lemma_get_bit_first bBits b i;
  assert (bn_v (bn_get_bits_first b (i+1)) == bn_v (bn_get_bits_first b i) + pow2 i * bn_get_bit b i);
  assert (bn_v (bn_get_bits_first b (i+1)) == bn_v (bn_get_bits_first b i) + pow2 i);
  if i = 0 then begin
    assert (bn_v acc % bn_v n == bn_v acc0 % bn_v n);
    assert (bn_v a % bn_v n == bn_v a0 % bn_v n);
    assert_norm (bn_v (bn_get_bits_first b i) == 0);
    assert (bn_v (bn_get_bits_first b (i+1)) == 1);
    assert_norm (pow (bn_v a0) 1 == bn_v a0);
    assert_norm (pow (pow2 rBits) 1 == pow2 rBits);
    assert_norm (pow2 rBits > 0);
    assert (bn_v acc1 % bn_v n == ((bn_v a * bn_v acc) / pow2 rBits) % bn_v n);
    lemma_mod_mult_div_1 (bn_v a * bn_v acc) (pow2 rBits) (bn_v n);
    lemma_mod_plus_mul_distr 0 (bn_v a) (bn_v acc) (bn_v n);
    lemma_mod_plus_mul_distr 0 (bn_v a0) (bn_v acc0) (bn_v n);
    lemma_mod_mult_div_1 (bn_v a0 * bn_v acc0) (pow2 rBits) (bn_v n);
    assert (bn_v acc1 % bn_v n == ((bn_v a0 * bn_v acc0) / pow2 rBits) % bn_v n);
    assert (mod_exp_pred nBits rBits nInv_u64 n bBits b a0 acc0 (i+1) (a1, acc1)) end
  else lemma_mod_exp_f20 nBits rBits nInv_u64 n bBits b a0 acc0 a acc a1 acc1 i

val lemma_mod_exp_a2:
  nBits:size_pos -> rBits:size_pos{nBits + 2 < rBits /\ nBits + rBits + 1 < max_size_t /\ rBits % 64 == 0} ->
  nInv_u64:bignum 64 -> n:bignum nBits{bn_v n > 0} ->
  bBits:size_pos -> b:bignum bBits ->
  a0:bignum (nBits+1) -> acc0:bignum (nBits+1) ->
  a:bignum (nBits+1) -> acc:bignum (nBits+1) ->
  a1:bignum (nBits+1) -> i:size_nat{i < bBits} -> Lemma
  (requires (mod_exp_pred nBits rBits nInv_u64 n bBits b a0 acc0 i (a, acc) /\
             bn_v a1 % bn_v n == ((bn_v a * bn_v a) / pow2 rBits) % bn_v n))
  (ensures (bn_v a1 % bn_v n == (pow (bn_v a0) (pow2 (i+1)) / pow (pow2 rBits) (pow2 (i+1) - 1)) % bn_v n))
  #reset-options "--z3rlimit 150 --max_fuel 0"
let lemma_mod_exp_a2 nBits rBits nInv_u64 n bBits b a0 acc0 a acc a1 i =
  if (i = 0) then begin
    assert (bn_v a % bn_v n = bn_v a0 % bn_v n);
    assert (bn_v a1 % bn_v n == ((bn_v a * bn_v a) / pow2 rBits) % bn_v n);
    lemma_mod_mult_div_1 (bn_v a * bn_v a) (pow2 rBits) (bn_v n);
    lemma_mod_plus_mul_distr 0 (bn_v a) (bn_v a) (bn_v n);
    lemma_mod_plus_mul_distr 0 (bn_v a0) (bn_v a0) (bn_v n);
    lemma_mod_mult_div_1 (bn_v a0 * bn_v a0) (pow2 rBits) (bn_v n);
    assert_norm (pow2 1 = 2);
    assert_norm (pow (pow2 rBits) (pow2 1 - 1) == pow2 rBits);
    assert_norm (pow (bn_v a0) 2 = bn_v a0 * bn_v a0);
    assert (bn_v a1 % bn_v n == (pow (bn_v a0) (pow2 1) / pow (pow2 rBits) (pow2 1 - 1)) % bn_v n) end
  else begin
    assert (bn_v a % bn_v n = (pow (bn_v a0) (pow2 i) / pow (pow2 rBits) (pow2 i - 1)) % bn_v n);
    assert (bn_v a1 % bn_v n == ((bn_v a * bn_v a) / pow2 rBits) % bn_v n);
    lemma_mod_mult_div_1 (bn_v a * bn_v a) (pow2 rBits) (bn_v n);
    lemma_mod_plus_mul_distr 0 (bn_v a) (bn_v a) (bn_v n);
    let a_n = pow (bn_v a0) (pow2 i) / pow (pow2 rBits) (pow2 i - 1) in
    lemma_mod_plus_mul_distr 0 a_n a_n (bn_v n);
    lemma_mod_mult_div_1 (a_n * a_n) (pow2 rBits) (bn_v n);
    let al = pow (bn_v a0) (pow2 i) in
    let bl = pow (pow2 rBits) (pow2 i - 1) in
    lemma_mul_div_mod al bl al bl (pow2 rBits) (bn_v n);
    assert (bn_v a1 % bn_v n == ((al * al) / (bl * bl * pow2 rBits)) % bn_v n);
    lemma_pow (bn_v a0) (pow2 i) (pow2 i);
    pow2_double_sum i;
    assert (al * al == pow (bn_v a0) (pow2 (i + 1)));
    lemma_pow (pow2 rBits) (pow2 i - 1) (pow2 i - 1);
    pow2_double_sum i;
    assert (bl * bl == pow (pow2 rBits) (pow2 (i+1) - 2));
    lemma_pow (pow2 rBits) (pow2 (i+1) - 2) 1;
    assert_norm (pow (pow2 rBits) 1 == pow2 rBits);
    assert (bl * bl * pow2 rBits == pow (pow2 rBits) (pow2 (i+1) - 1))
  end

val lemma_mod_exp_2:
  n:nat{n > 0} -> a:nat -> a_r:nat ->
  b:nat -> acc_r:nat -> r:nat{r > 0} -> res_r:nat -> Lemma
  (requires (a_r % n == (a * r) % n /\ acc_r % n == r % n /\
             res_r % n == ((pow a_r b) * acc_r / pow r b) % n))
  (ensures (res_r % n == ((pow a b) * r) % n))
  #reset-options "--z3rlimit 50 --max_fuel 0"
let lemma_mod_exp_2 n a a_r b acc_r r res_r =
  assert (res_r % n == ((pow a_r b) * acc_r / pow r b) % n);
  lemma_mod_mult_div (pow a_r b) acc_r (pow r b) n;
  lemma_pow_mod a_r b n;
  lemma_pow_mod (a * r) b n;
  assert ((pow a_r b) % n == (pow (a * r) b) % n);
  lemma_pow_mul a r b;
  assert (res_r % n == (((pow a b * pow r b) % n) * acc_r / pow r b) % n);
  lemma_mod_mult_div (pow a b * pow r b) acc_r (pow r b) n;
  assert (res_r % n == (pow a b * pow r b * acc_r / pow r b) % n);
  lemma_mul_mul (pow a b) (pow r b) acc_r;
  multiple_division_lemma ((pow a b) * acc_r) (pow r b);
  lemma_mod_mul_distr_l acc_r (pow a b) n;
  lemma_mod_mul_distr_l r (pow a b) n

(* LEMMAS for Karatsuba's multiplication *)
val abs: x:int -> Tot (y:nat{(x >= 0 ==> y = x) /\ (x < 0 ==> y = -x)})
let abs x = if x >= 0 then x else -x

val lemma_distributivity_mult:
  a:nat -> b:nat -> c:nat -> d:nat -> Lemma
  ((a + b) * (c + d) = a * c + a * d + b * c + b * d)
let lemma_distributivity_mult a b c d = ()

val lemma_add_sign1:
  a0Bits:size_pos -> a1Bits:size_pos{a0Bits + a1Bits + 1 < max_size_t} ->
  a0:bignum a0Bits -> a1:bignum a1Bits ->
  b0:bignum a0Bits -> b1:bignum a1Bits -> Lemma
  (bn_v a1 * bn_v b0 + bn_v a0 * bn_v b1 < pow2 (a0Bits + a1Bits + 1))
let lemma_add_sign1 a0Bits a1Bits a0 a1 b0 b1 =
  assert (bn_v a1 * bn_v b0 + bn_v a0 * bn_v b1 < pow2 a1Bits * pow2 a0Bits + pow2 a0Bits * pow2 a1Bits);
  pow2_plus a1Bits a0Bits;
  pow2_double_sum (a0Bits + a1Bits)

val lemma_karatsuba_mult:
  aBits:size_pos -> a0Bits:size_pos -> a1Bits:size_pos{a0Bits + a1Bits == aBits} ->
  a:nat{a < pow2 aBits} -> a0:nat{a0 < pow2 a0Bits} -> a1:nat{a1 < pow2 a1Bits} ->
  b:nat{b < pow2 aBits} -> b0:nat{b0 < pow2 a0Bits} -> b1:nat{b1 < pow2 a1Bits} -> Lemma
  (requires (a == a1 * pow2 a0Bits + a0 /\ b == b1 * pow2 a0Bits + b0))
  (ensures (a * b == a1 * b1 * pow2 (a0Bits + a0Bits) + (a0 * b1 + a1 * b0) * pow2 a0Bits + a0 * b0))
  #reset-options "--z3rlimit 50 --max_fuel 0"
let lemma_karatsuba_mult aBits a0Bits a1Bits a a0 a1 b b0 b1 =
  assert (a * b == (a1 * pow2 a0Bits + a0) * (b1 * pow2 a0Bits + b0));
  lemma_distributivity_mult (a1 * pow2 a0Bits) a0 (b1 * pow2 a0Bits) b0;
  assert (a * b == a0 * b0 + a1 * b1 * pow2 a0Bits * pow2 a0Bits + a0 * b1 * pow2 a0Bits + a1 * b0 * pow2 a0Bits);
  pow2_plus a0Bits a0Bits

val lemma_mul_pow2:
  aBits:size_pos -> a:bignum aBits -> b:bignum aBits -> Lemma
  (bn_v a * bn_v b < pow2 (aBits + aBits))
let lemma_mul_pow2 aBits a b =
  assert (bn_v a * bn_v b < pow2 aBits * pow2 aBits);
  pow2_plus aBits aBits

val lemma_get_bits:
  aBits:size_pos -> a0Bits:size_pos{a0Bits % 64 == 0 /\ a0Bits < aBits} -> a:bignum aBits ->
  a0:bignum a0Bits -> a1:bignum (aBits - a0Bits) -> Lemma
  (requires (bn_v a0 == bn_v (bn_get_bits a 0 a0Bits) /\ bn_v a1 == bn_v (bn_get_bits a a0Bits aBits)))
  (ensures (bn_v a == bn_v a0 + bn_v a1 * pow2 a0Bits))
let lemma_get_bits aBits a0Bits a a0 a1 =
  assert (bn_v a0 == bn_v a % pow2 a0Bits);
  assert (bn_v a1 == (bn_v a / pow2 a0Bits) % pow2 (aBits - a0Bits));
  pow2_modulo_division_lemma_1 (bn_v a) a0Bits aBits;
  assert (bn_v a1 == (bn_v a % pow2 aBits) / pow2 a0Bits);
  small_modulo_lemma_1 (bn_v a) (pow2 aBits);
  assert (bn_v a1 == bn_v a / pow2 a0Bits);
  euclidean_division_definition (bn_v a) (pow2 a0Bits)

(* LEMMAS for exponent blinding *)
let elem n = x:nat{x < n}

val lemma_mod_pq:
  a:nat -> b:nat -> p:nat{p > 1} -> q:nat{q > 1} -> Lemma
  (requires (a % p == b % p /\ a % q == b % q))
  (ensures (a % (p * q) == b % (p * q)))
let lemma_mod_pq a b p q = admit()

// m ^ (p - 1) = 1 (mod p) where gcd(m, p) = 1 and p is a prime number
val fermat_little_theorem:
  p:nat{p > 1} -> m:nat{m > 0} -> Lemma
  (requires (m % p <> 0))
  (ensures ((pow m (p - 1)) % p == 1))
let fermat_little_theorem p m = admit()

val lemma_exp_blinding_q:
  n:nat{n > 1} -> phi_n:nat -> p:elem n{p > 1} ->
  q:elem n{q > 1} -> m:elem n{m > 0} -> Lemma
  (requires (phi_n == (p - 1) * (q - 1) /\ n = p * q /\ m % q <> 0))
  (ensures ((pow m phi_n) % q == 1))
  #reset-options "--z3rlimit 50 --max_fuel 0"
let lemma_exp_blinding_q n phi_n p q m =
  let res = (pow m phi_n) % q in
  lemma_pow_pow m (q - 1) (p - 1);
  lemma_pow_mod (pow m (q - 1)) (p - 1) q;
  fermat_little_theorem q m;
  lemma_pow_1 (p - 1)

val lemma_exp_blinding_pq:
  n:nat{n > 1} -> phi_n:nat -> p:elem n{p > 1} ->
  q:elem n{q > 1} -> m:elem n{m > 0} -> Lemma
  (requires (phi_n == (p - 1) * (q - 1) /\ n = p * q /\ m % p <> 0 /\ m % q <> 0))
  (ensures ((pow m phi_n) % (p * q) == 1))
  #reset-options "--z3rlimit 50 --max_fuel 0"
let lemma_exp_blinding_pq n phi_n p q m =
  lemma_exp_blinding_q n phi_n p q m;
  small_modulo_lemma_1 1 q;
  lemma_exp_blinding_q n phi_n q p m;
  small_modulo_lemma_1 1 p;
  lemma_mod_pq (pow m phi_n) 1 p q;
  small_modulo_lemma_1 1 n

val lemma_exp_blinding_1:
  n:nat{n > 1} -> phi_n:nat -> p:elem n{p > 1} -> q:elem n{q > 1} ->
  d:elem n{d > 0} -> m:elem n{m > 0} -> r:nat -> Lemma
  (requires (phi_n = (p - 1) * (q - 1) /\ n = p * q /\ m % p <> 0 /\ m % q <> 0))
  (ensures ((pow m (d + r * phi_n)) % n  == (pow m d) % n))
let lemma_exp_blinding_1 n phi_n p q d m r =
  lemma_exp_blinding_pq n phi_n p q m;
  assert ((pow m phi_n) % (p * q) == 1);
  let res:nat = (pow m (d + r * phi_n)) % n in
  lemma_pow m d (r * phi_n);
  lemma_pow_pow m phi_n r;
  lemma_pow_mod (pow m phi_n) r n;
  assert ((pow (pow m phi_n) r) % n == (pow ((pow m phi_n) % n) r) % n);
  //assert ((pow (pow m phi_n) r) % n == (pow 1 r) % n);
  lemma_pow_1 r;
  modulo_lemma 1 n;
  lemma_mod_mul_distr_l (pow m (r * phi_n)) (pow m d) n

val lemma_exp_blinding_0_q0:
  n:nat{n > 1} -> phi_n:nat -> p:elem n{p > 1} -> q:elem n{q > 1} ->
  d:elem n{d > 0} -> m:elem n{m > 0} -> r:nat -> Lemma
  (requires (phi_n = (p - 1) * (q - 1) /\ n = p * q /\ m % q = 0))
  (ensures ((pow m (d + r * phi_n)) % q == (pow m d) % q))
let lemma_exp_blinding_0_q0 n phi_n p q d m r =
  let res:nat = pow m (d + r * phi_n) in
  assert (res % q == (pow m (d + r * phi_n)) % q);
  lemma_pow_mod m (d + r * phi_n) q;
  lemma_pow_0 (d + r * phi_n);
  lemma_pow_mod m d q;
  lemma_pow_0 d

val lemma_exp_blinding_0_q1:
  n:nat{n > 1} -> phi_n:nat -> p:elem n{p > 1} -> q:elem n{q > 1} ->
  d:elem n{d > 0} -> m:elem n{m > 0} -> r:nat -> Lemma
  (requires (phi_n = (p - 1) * (q - 1) /\ n = p * q /\ m % p <> 0))
  (ensures ((pow m (d + r * phi_n)) % p == (pow m d) % p))
let lemma_exp_blinding_0_q1 n phi_n p q d m r =
  lemma_exp_blinding_q n phi_n q p m;
  assert ((pow m phi_n) % p == 1);
  let res:nat = pow m (d + r * phi_n) in
  assert (res % p == (pow m (d + r * phi_n)) % p);
  lemma_pow m d (r * phi_n);
  assert (res % p == ((pow m d) * (pow m (r * phi_n))) % p);
  lemma_mod_mul_distr_l (pow m (r * phi_n)) (pow m d) p;
  lemma_pow_pow m phi_n r;
  lemma_pow_mod (pow m phi_n) r p;
  assert ((pow m (r * phi_n)) % p == (pow ((pow m phi_n) % p) r) % p);
  assert ((pow (pow m phi_n) r) % p == (pow 1 r) % p);
  lemma_pow_1 r;
  modulo_lemma 1 p;
  assert (res % p == ((pow m d) * 1) % p)

val lemma_exp_blinding_0_q:
  n:nat{n > 1} -> phi_n:nat -> p:elem n{p > 1} -> q:elem n{q > 1} ->
  d:elem n{d > 0} -> m:elem n{m > 0} -> r:nat -> Lemma
  (requires (phi_n = (p - 1) * (q - 1) /\ n = p * q /\ m % q = 0 /\ m % p <> 0))
  (ensures ((pow m (d + r * phi_n)) % n == (pow m d) % n))
let lemma_exp_blinding_0_q n phi_n p q d m r =
  let res:nat = pow m (d + r * phi_n) in
  lemma_exp_blinding_0_q0 n phi_n p q d m r;
  lemma_exp_blinding_0_q1 n phi_n p q d m r;
  lemma_mod_pq res (pow m d) p q;
  assert (res % n == (pow m d) % n)

val lemma_exp_blinding_0_pq:
  n:nat{n > 1} -> phi_n:nat -> p:elem n{p > 1} -> q:elem n{q > 1} ->
  d:elem n{d > 0} -> m:elem n -> r:nat -> Lemma
  (requires (phi_n = (p - 1) * (q - 1) /\ n = p * q /\ m % q = 0 /\ m % p = 0))
  (ensures ((pow m (d + r * phi_n)) % n == (pow m d) % n))
let lemma_exp_blinding_0_pq n phi_n p q d m r =
  small_modulo_lemma_1 0 p;
  small_modulo_lemma_1 0 q;
  lemma_mod_pq m 0 p q;
  small_modulo_lemma_1 0 n;
  assert (m % n == 0);
  small_modulo_lemma_1 m n;
  assert (m = 0);
  lemma_pow_0 (d + r * phi_n);
  lemma_pow_0 d

val lemma_exp_blinding_0:
  n:nat{n > 1} -> phi_n:nat -> p:elem n{p > 1} -> q:elem n{q > 1} ->
  d:elem n{d > 0} -> m:elem n -> r:nat -> Lemma
  (requires (phi_n = (p - 1) * (q - 1) /\ n = p * q /\
            (m = 0 \/ m % p = 0 \/ m % q = 0)))
  (ensures ((pow m (d + r * phi_n)) % n  == (pow m d) % n))
let lemma_exp_blinding_0 n phi_n p q d m r =
  if (m = 0) then begin
    lemma_pow_0 (d + r * phi_n);
    lemma_pow_0 d end
  else begin
    if (m % p = 0 && m % q <> 0) then
      lemma_exp_blinding_0_q n phi_n q p d m r
    else begin
      if (m % q = 0 && m % p <> 0) then
	lemma_exp_blinding_0_q n phi_n p q d m r
      else begin
	assert (m % p = 0 && m % q = 0);
	lemma_exp_blinding_0_pq n phi_n p q d m r end
    end
  end

val lemma_exp_blinding:
  n:nat{n > 1} -> phi_n:nat -> p:elem n{p > 1} -> q:elem n{q > 1} ->
  d:elem n{d > 0} -> m:elem n -> r:nat -> Lemma
  (requires (phi_n = (p - 1) * (q - 1) /\ n = p * q))
  (ensures ((pow m (d + r * phi_n)) % n  == (pow m d) % n))
let lemma_exp_blinding n phi_n p q d m r =
  if (m = 0 || m % p = 0 || m % q = 0) then
    lemma_exp_blinding_0 n phi_n p q d m r
  else lemma_exp_blinding_1 n phi_n p q d m r

val lemma_exp_blinding_bn:
  #nBits:size_pos -> #pBits:size_pos -> #qBits:size_pos{pBits + qBits < max_size_t} ->
  #dBits:size_pos -> #mBits:size_pos ->
  n:bignum nBits{bn_v n > 1} -> phi_n:bignum (pBits+qBits) ->
  p:bignum pBits{1 < bn_v p /\ bn_v p < bn_v n} -> q:bignum qBits{1 < bn_v q /\ bn_v q < bn_v n} ->
  d:bignum dBits{0 < bn_v d /\ bn_v d < bn_v n} -> m:bignum mBits{bn_v m < bn_v n} ->
  r:bignum 64 -> Lemma
  (requires (bn_v phi_n == (bn_v p - 1) * (bn_v q - 1) /\ bn_v n = bn_v p * bn_v q))
  (ensures ((pow (bn_v m) (bn_v d + bn_v r * bn_v phi_n)) % bn_v n  == (pow (bn_v m) (bn_v d)) % bn_v n))
let lemma_exp_blinding_bn #nBits #pBits #qBits #dBits #mBits n phi_n p q d m r =
  lemma_exp_blinding (bn_v n) (bn_v phi_n) (bn_v p) (bn_v q) (bn_v d) (bn_v m) (bn_v r)
