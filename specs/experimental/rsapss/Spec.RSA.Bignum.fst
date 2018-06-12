module Spec.RSA.Bignum

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Spec.Lib.RawIntTypes

open FStar.Math.Lemmas
open Spec.RSA.Lemmas
open Spec.Bignum.Basic

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

val abs_sub:
  #aBits:size_pos -> #bBits:size_pos{bBits <= aBits} ->
  a:bignum aBits -> b:bignum bBits -> Pure (tuple2 sign (bignum aBits))
  (requires True)
  (ensures (fun (s, res) -> bn_v res = abs (bn_v a - bn_v b) /\ s = (if bn_v a >= bn_v b then Positive else Negative)))
let abs_sub #aBits #bBits a b =
  if (bn_is_less a b)
  then begin
    let res = bn_sub b a in
    pow2_le_compat aBits bBits;
    let res = bn_cast_gt aBits res in
    (Negative, res) end
  else begin
    assert (bn_v a >= bn_v b);
    (Positive, bn_sub a b) end

val lemma_add_sign:
  c0:nat -> c1:nat -> c2:nat ->
  a0:nat -> a1:nat -> a2:nat ->
  b0:nat -> b1:nat -> b2:nat ->
  sa2:sign -> sb2:sign -> Lemma
  (requires (c0 == a0 * b0 /\ c1 == a1 * b1 /\ c2 == a2 * b2 /\
             a2 == abs (a0 - a1) /\ b2 == abs (b0 - b1) /\
	     sa2 = (if (a0 >= a1) then Positive else Negative) /\
	     sb2 = (if (b0 >= b1) then Positive else Negative)))
  (ensures (if (sa2 = sb2) then (c0 + c1 - c2 == a1 * b0 + a0 * b1) else (c0 + c1 + c2 == a1 * b0 + a0 * b1)))
let lemma_add_sign c0 c1 c2 a0 a1 a2 b0 b1 b2 sa2 sb2 = ()

val add_sign:
  #a0Bits:size_pos{a0Bits+a0Bits+1 < max_size_t} ->
  #a1Bits:size_pos{a1Bits+a1Bits < max_size_t /\ a1Bits <= a0Bits} ->
  c0:bignum (a0Bits + a0Bits) -> c1:bignum (a1Bits + a1Bits) -> c2:bignum (a0Bits + a0Bits) ->
  a0:bignum a0Bits -> a1:bignum a1Bits -> a2:bignum a0Bits ->
  b0:bignum a0Bits -> b1:bignum a1Bits -> b2:bignum a0Bits ->
  sa2:sign -> sb2:sign -> Pure (res:bignum (a0Bits + a0Bits + 1))
  (requires (bn_v c0 == bn_v a0 * bn_v b0 /\ bn_v c1 == bn_v a1 * bn_v b1 /\ bn_v c2 == bn_v a2 * bn_v b2 /\
             bn_v a2 == abs (bn_v a0 - bn_v a1) /\ bn_v b2 == abs (bn_v b0 - bn_v b1) /\
	     sa2 = (if (bn_v a0 >= bn_v a1) then Positive else Negative) /\
	     sb2 = (if (bn_v b0 >= bn_v b1) then Positive else Negative)))
  (ensures (fun res -> bn_v res == bn_v (bn_add_carry (bn_mul a1 b0) (bn_mul a0 b1))))
  #reset-options "--z3rlimit 150 --max_fuel 0"
let add_sign #a0Bits #a1Bits c0 c1 c2 a0 a1 a2 b0 b1 b2 sa2 sb2 =
  lemma_add_sign (bn_v c0) (bn_v c1) (bn_v c2) (bn_v a0) (bn_v a1) (bn_v a2) (bn_v b0) (bn_v b1) (bn_v b2) sa2 sb2;
  let c01 = bn_add_carry c0 c1 in
  if (sa2 = sb2)
  then bn_sub c01 c2
  else begin
    assert ((bn_v c0 + bn_v c1) + bn_v c2 == bn_v a0 * bn_v b1 + bn_v a1 * bn_v b0);
    lemma_add_sign1 a0Bits a1Bits a0 a1 b0 b1;
    pow2_le_compat (a0Bits+a0Bits+1) (a0Bits+a1Bits+1);
    assert ((bn_v c0 + bn_v c1) + bn_v c2 < pow2 (a0Bits + a0Bits + 1));
    bn_add c01 c2
  end

val karatsuba_f:
  #aBits:size_pos{aBits + aBits < max_size_t} -> #a0Bits:size_pos ->
  #a1Bits:size_pos{a0Bits + a1Bits = aBits /\ a1Bits <= a0Bits} ->
  c0:bignum (a0Bits + a0Bits) -> c1:bignum (a1Bits + a1Bits) ->
  tmp:bignum (a0Bits+a0Bits+1){bn_v tmp < pow2 (a0Bits+a1Bits+1)} -> Pure (res:bignum (aBits + aBits))
  (requires (bn_v c0 + bn_v c1 * pow2 (a0Bits + a0Bits) + bn_v tmp * pow2 a0Bits < pow2 (aBits + aBits)))
  (ensures (fun res -> bn_v res == bn_v c0 + bn_v c1 * pow2 (a0Bits + a0Bits) + bn_v tmp * pow2 a0Bits))
let karatsuba_f #aBits #a0Bits #a1Bits c0 c1 tmp =
  let c = bn_const_0 #(aBits + aBits) in
  pow2_lt_compat (aBits + aBits) (a0Bits + a0Bits);
  let res0 = bn_add c c0 in
  assert (bn_v res0 == bn_v c + bn_v c0);
  pow2_lt_compat (aBits + aBits) (a1Bits + a1Bits);
  let res1 = bn_lshift_add c1 (a0Bits + a0Bits) res0 in
  assert (bn_v res1 == bn_v c0 + bn_v c1 * pow2 (a0Bits + a0Bits));
  let tmp = bn_cast_le (a0Bits+a1Bits+1) tmp in
  pow2_lt_compat (aBits + aBits) (a0Bits + a1Bits + 1);
  let res2 = bn_lshift_add tmp a0Bits res1 in
  assert (bn_v res2 == bn_v c0 + bn_v c1 * pow2 (a0Bits + a0Bits) + bn_v tmp * pow2 a0Bits);
  res2

val karatsuba:
  aBits:size_pos{aBits + aBits < max_size_t} ->
  a:bignum aBits -> b:bignum aBits-> Tot (res:bignum (aBits + aBits){bn_v res == bn_v a * bn_v b})
  (decreases aBits)
  #reset-options "--z3rlimit 150 --max_fuel 2"
let rec karatsuba aBits a b =
  if aBits < 10 * 64 then bn_mul a b
  else begin
    let len = blocks aBits 64 in
    let a0Bits = 64 * (blocks len 2) in
    let a1Bits = aBits - a0Bits in
    assert (a1Bits <= a0Bits);

    let a0 = bn_get_bits a 0 a0Bits in
    let a1 = bn_get_bits a a0Bits aBits in
    lemma_get_bits aBits a0Bits a a0 a1;

    let b0 = bn_get_bits b 0 a0Bits in
    let b1 = bn_get_bits b a0Bits aBits in
    lemma_get_bits aBits a0Bits b b0 b1;

    let (sa2, a2) = abs_sub a0 a1 in
    let (sb2, b2) = abs_sub b0 b1 in

    let c0 = karatsuba a0Bits a0 b0 in
    assert (bn_v c0 == bn_v a0 * bn_v b0);
    let c1 = karatsuba a1Bits a1 b1 in
    assert (bn_v c1 == bn_v a1 * bn_v b1);
    let c2 = karatsuba a0Bits a2 b2 in
    assert (bn_v c2 == bn_v a2 * bn_v b2);

    let tmp = add_sign #a0Bits #a1Bits c0 c1 c2 a0 a1 a2 b0 b1 b2 sa2 sb2 in
    assert (bn_v tmp == bn_v a0 * bn_v b1 + bn_v a1 * bn_v b0);
    lemma_karatsuba_mult aBits a0Bits a1Bits (bn_v a) (bn_v a0) (bn_v a1) (bn_v b) (bn_v b0) (bn_v b1);
    lemma_mul_pow2 aBits a b;
    let res = karatsuba_f #aBits #a0Bits #a1Bits c0 c1 tmp in
    assert (bn_v res == bn_v a * bn_v b);
    res
  end

(* Montgomery's arithmetic *)
val mont_pred:
  #nBits:size_pos -> #cBits:size_pos ->
  rBits:size_pos{nBits < rBits /\ nBits+1+rBits < max_size_t} ->
  nInv_u64:bignum 64 -> n:bignum nBits{bn_v n > 0} ->
  c:bignum cBits ->
  i:size_nat{i <= rBits / 64} -> res:bignum (nBits + 1 + rBits) -> Tot Type0
let mont_pred #nBits #cBits rBits nInv_u64 n c i res = bn_v res % bn_v n = bn_v c % bn_v n && bn_v res <= bn_v c + (pow2 (64*i) - 1) * bn_v n

val mont_reduction_f:
  #nBits:size_pos -> #cBits:size_pos ->
  rBits:size_pos{nBits + 1 + rBits < max_size_t} ->
  nInv_u64:bignum 64 -> n:bignum nBits{bn_v n > 0} ->
  c:bignum cBits{nBits < rBits /\ cBits < nBits + rBits} ->
  Tot (repeatable #(bignum (nBits + 1 + rBits)) #(rBits/64) (mont_pred #nBits #cBits rBits nInv_u64 n c))
  #reset-options "--z3rlimit 150 --max_fuel 0"
let mont_reduction_f #nBits #cBits rBits nInv_u64 n c i res =
  let res_i = bn_get_bits res (i * 64) ((i + 1)*64) in
  let qi = bn_get_bits (bn_mul nInv_u64 res_i) 0 64 in
  assert (bn_v res + bn_v n * pow2 (64*i) * bn_v qi <= bn_v c + (pow2 (64*i)-1) * bn_v n + bn_v n * pow2 (64*i) * bn_v qi);
  lemma_mont_reduction_fi #nBits #cBits rBits qi n c i res;
  lemma_mont_reduction_f #nBits #cBits rBits n c i;
  assert (bn_v res + bn_v n * pow2 (64*i) * bn_v qi < pow2 (nBits+1+rBits));
  let res1 = bn_lshift_mul_add n (64*i) qi res in
  lemma_mod_plus (bn_v res) (pow2 (64*i) * bn_v qi) (bn_v n); // res1 % n == res % n
  res1

val mont_reduction_:
  #nBits:size_pos -> #cBits:size_pos ->
  rBits:size_pos{nBits < rBits /\ nBits + 1 + rBits < max_size_t /\ rBits % 64 == 0} ->
  nInv_u64:bignum 64 -> n:bignum nBits{bn_v n > 0} ->
  c:bignum cBits{cBits < nBits + rBits} ->
  Tot (res:bignum (nBits + 1 + rBits){bn_v res % bn_v n = bn_v c % bn_v n && bn_v res <= bn_v c + (pow2 rBits - 1) * bn_v n})

let mont_reduction_ #nBits #cBits rBits nInv_u64 n c =
  pow2_lt_compat (nBits+1+rBits) cBits;
  let tmp = bn_cast_gt (nBits+1+rBits) c in
  let rLen = rBits / 64 in
  let res = repeati_inductive rLen
    (mont_pred #nBits #cBits rBits nInv_u64 n c)
    (fun i res ->
      mont_reduction_f rBits nInv_u64 n c i res) tmp in
  res

val mont_reduction:
  #nBits:size_pos -> #cBits:size_pos ->
  rBits:size_pos{nBits < rBits /\ nBits + 1 + rBits < max_size_t /\ rBits % 64 == 0} ->
  nInv_u64:bignum 64 -> n:bignum nBits{bn_v n > 0} ->
  c:bignum cBits{cBits < nBits + rBits} -> Tot (res:bignum (nBits+1){bn_v res % bn_v n == (bn_v c / pow2 rBits) % bn_v n})

let mont_reduction #nBits #cBits rBits nInv_u64 n c =
  let tmp = mont_reduction_ rBits nInv_u64 n c in
  assert (bn_v tmp % bn_v n = bn_v c % bn_v n && bn_v tmp <= bn_v c + (pow2 rBits - 1) * bn_v n);
  lemma_mont_reduction #nBits #cBits rBits n c;
  let res = bn_rshift tmp rBits in
  assert (bn_v res % bn_v n == (bn_v tmp / pow2 rBits) % bn_v n);
  lemma_mod_mult_div_1 (bn_v tmp) (pow2 rBits) (bn_v n);
  assert (bn_v res % bn_v n == ((bn_v c % bn_v n) / pow2 rBits) % bn_v n);
  lemma_mod_mult_div_1 (bn_v c) (pow2 rBits) (bn_v n);
  res

val mul_mod_mont:
  nBits:size_pos ->
  rBits:size_pos{nBits + 2 < rBits /\ nBits + rBits + 1 < max_size_t /\ rBits % 64 == 0} ->
  nInv_u64:bignum 64 -> n:bignum nBits{bn_v n > 0} ->
  a:bignum (nBits+1) -> b:bignum (nBits+1) -> Tot (res:bignum (nBits+1){bn_v res % bn_v n == ((bn_v a * bn_v b) / pow2 rBits) % bn_v n})
let mul_mod_mont nBits rBits nInv_u64 n a b =
  //let c = bn_mul a b in
  let c = karatsuba (nBits+1) a b in
  assert (bn_v c < pow2 (nBits + nBits + 2));
  mont_reduction rBits nInv_u64 n c

val to_mont:
  #aBits:size_pos -> nBits:size_pos ->
  rBits:size_pos{nBits < rBits /\ nBits + rBits + 1 < max_size_t /\ rBits % 64 == 0} ->
  nInv_u64:bignum 64 -> n:bignum nBits{bn_v n > 0} ->
  r2:bignum nBits{bn_v r2 == pow2 (2*rBits) % bn_v n} ->
  a:bignum aBits{aBits <= nBits} -> Tot (res:bignum (nBits+1){bn_v res % bn_v n == (bn_v a * pow2 rBits) % bn_v n})
  #reset-options "--z3rlimit 50 --max_fuel 0"
let to_mont #aBits nBits rBits nInv_u64 n r2 a =
  let c = bn_mul a r2 in
  assert (bn_v c < pow2 (aBits + nBits));
  let res = mont_reduction rBits nInv_u64 n c in
  assert (bn_v res % bn_v n == (bn_v c / pow2 rBits) % bn_v n);
  lemma_mod_mult_div_1 (bn_v c) (pow2 rBits) (bn_v n);
  assert (bn_v c % bn_v n == (bn_v a * bn_v r2) % bn_v n);
  lemma_mod_mul_distr_l (bn_v r2) (bn_v a) (bn_v n);
  lemma_mod_mul_distr_l (pow2 (2*rBits)) (bn_v a) (bn_v n);
  lemma_mod_mult_div_1 (bn_v a * pow2 (2*rBits)) (pow2 rBits) (bn_v n);
  assert (bn_v res % bn_v n == ((bn_v a * pow2 (2*rBits)) / pow2 rBits) % bn_v n);
  pow2_multiplication_division_lemma_1 (bn_v a) rBits (2*rBits);
  assert (bn_v res % bn_v n == (bn_v a * pow2 rBits) % bn_v n);
  res

val from_mont:
  nBits:size_pos ->
  rBits:size_pos{nBits < rBits /\ nBits + rBits + 1 < max_size_t /\ rBits % 64 == 0} ->
  nInv_u64:bignum 64 -> n:bignum nBits{bn_v n > 0} ->
  a_r:bignum (nBits+1) -> Tot (res:bignum nBits{bn_v res == (bn_v a_r / pow2 rBits) % bn_v n})
  #reset-options "--z3rlimit 50 --max_fuel 0"
let from_mont nBits rBits nInv_u64 n a_r =
  let tmp = mont_reduction_ rBits nInv_u64 n a_r in
  assert (bn_v tmp % bn_v n = bn_v a_r % bn_v n && bn_v tmp < bn_v a_r + pow2 rBits * bn_v n);
  let res = bn_rshift tmp rBits in
  lemma_mod_mult_div_1 (bn_v tmp) (pow2 rBits) (bn_v n);
  lemma_mod_mult_div_1 (bn_v a_r) (pow2 rBits) (bn_v n);
  assume (bn_v res < bn_v n);
  let res = bn_cast_le nBits res in
  small_modulo_lemma_1 (bn_v res) (bn_v n);
  res

val mod_exp_f:
  nBits:size_pos ->
  rBits:size_pos{nBits + 2 < rBits /\ nBits + rBits + 1 < max_size_t /\ rBits % 64 == 0} ->
  nInv_u64:bignum 64 -> n:bignum nBits{bn_v n > 0} ->
  bBits:size_pos -> b:bignum bBits ->
  a0:bignum (nBits+1) -> acc0:bignum (nBits+1) -> Tot (repeatable #(tuple2 (bignum (nBits+1)) (bignum (nBits+1))) #bBits (mod_exp_pred nBits rBits nInv_u64 n bBits b a0 acc0))
  #reset-options "--z3rlimit 150 --max_fuel 0"
let mod_exp_f nBits rBits nInv_u64 n bBits b a0 acc0 i (a, acc) =
  let a1 = mul_mod_mont nBits rBits nInv_u64 n a a in
  assert (bn_v a1 % bn_v n == ((bn_v a * bn_v a) / pow2 rBits) % bn_v n);
  lemma_mod_exp_a2 nBits rBits nInv_u64 n bBits b a0 acc0 a acc a1 i;
  assert (bn_v a1 % bn_v n = (pow (bn_v a0) (pow2 (i+1)) / pow (pow2 rBits) (pow2 (i+1) - 1)) % bn_v n);
  if (bn_get_bit b i = 1) then begin
    let acc1 = mul_mod_mont nBits rBits nInv_u64 n a acc in
    lemma_mod_exp_f2 nBits rBits nInv_u64 n bBits b a0 acc0 a acc a1 acc1 i;
    (a1, acc1) end
  else begin
    let acc1 = acc in
    lemma_mod_exp_f1 nBits rBits nInv_u64 n bBits b a0 acc0 a acc a1 i;
    (a1, acc1) end

val mod_exp_:
  nBits:size_pos ->
  rBits:size_pos{nBits + 2 < rBits /\ nBits + rBits + 1 < max_size_t /\ rBits % 64 == 0} ->
  nInv_u64:bignum 64 -> n:bignum nBits{bn_v n > 0} ->
  a0:bignum (nBits+1) ->
  bBits:size_pos -> b:bignum bBits ->
  acc0:bignum (nBits+1) -> Tot (res:bignum (nBits+1){bn_v res % bn_v n == ((pow (bn_v a0) (bn_v b)) * (bn_v acc0) / pow (pow2 rBits) (bn_v b)) % bn_v n})
  #reset-options "--z3rlimit 150 --max_fuel 0"
let mod_exp_ nBits rBits nInv_u64 n a0 bBits b acc0 =
  let (a, acc) = repeati_inductive bBits
    (mod_exp_pred nBits rBits nInv_u64 n bBits b a0 acc0)
    (fun i (a, acc) -> mod_exp_f nBits rBits nInv_u64 n bBits b a0 acc0 i (a, acc))
    (a0, acc0) in
  assert (bn_v acc % bn_v n = ((pow (bn_v a0) (bn_v (bn_get_bits_first b bBits)) * bn_v acc0) / pow (pow2 rBits) (bn_v (bn_get_bits_first b bBits))) % bn_v n);
  assert (bn_v b < pow2 bBits);
  small_modulo_lemma_1 (bn_v b) (pow2 bBits);
  assert (bn_v (bn_get_bits_first b bBits) == bn_v b);
  acc

val mod_exp:
  #aBits:size_pos ->
  nBits:size_pos{64 <= nBits /\ 2 * 64 * (blocks nBits 64 + 1) < max_size_t} ->
  n:bignum nBits{0 < bn_v n} -> a:bignum aBits{aBits <= nBits} ->
  bBits:size_pos -> b:bignum bBits -> Tot (res:bignum nBits{bn_v res == (pow (bn_v a) (bn_v b)) % bn_v n})
let mod_exp #aBits nBits n a bBits b =
  let nLen = blocks nBits 64 in
  let rBits = 64 * (nLen + 1) in
  let r2 = bn_pow2_r_mod n (rBits * 2) in
  let n0 = bn_get_bits n 0 64 in
  let nInv_u64 = bn_from_u64 (mod_inv_u64 (bn_to_u64 n0)) in
  let a_r = to_mont nBits rBits nInv_u64 n r2 a in
  let acc_r = to_mont nBits rBits nInv_u64 n r2 (bn_const_1 #nBits) in
  let res_r = mod_exp_ nBits rBits nInv_u64 n a_r bBits b acc_r in
  lemma_mod_exp_2 (bn_v n) (bn_v a) (bn_v a_r) (bn_v b) (bn_v acc_r) (pow2 rBits) (bn_v res_r);
  let res = from_mont nBits rBits nInv_u64 n res_r in
  lemma_mod_mult_div_1 (bn_v res_r) (pow2 rBits) (bn_v n);
  lemma_mod_mult_div_1 ((pow (bn_v a) (bn_v b)) * pow2 rBits) (pow2 rBits) (bn_v n);
  multiple_division_lemma (pow (bn_v a) (bn_v b)) (pow2 rBits);
  res

val rsa_blinding:
  #mBits:size_pos ->
  nBits:size_pos{64 <= nBits /\ 2 * 64 * (blocks nBits 64 + 1) < max_size_t} -> n:bignum nBits{1 < bn_v n} ->
  pBits:size_pos -> p:bignum pBits{1 < bn_v p /\ bn_v p < bn_v n} ->
  qBits:size_pos{pBits + qBits + 65 < max_size_t} -> q:bignum qBits{1 < bn_v q /\ bn_v q < bn_v n /\ bn_v n == bn_v p * bn_v q} ->
  m:bignum mBits{mBits <= nBits /\ bn_v m < bn_v n} ->
  dBits:size_pos{dBits < pBits + qBits + 64} -> d:bignum dBits{0 < bn_v d /\ bn_v d < bn_v n} ->
  rBlind:bignum 64 -> Tot (s:bignum nBits{bn_v s == (pow (bn_v m) (bn_v d)) % bn_v n})
  #reset-options "--z3rlimit 150 --max_fuel 0"
let rsa_blinding #mBits nBits n pBits p qBits q m dBits d rBlind =
  let bn_1 = bn_const_1 #1 in
  let p1 = bn_sub p bn_1 in
  let q1 = bn_sub q bn_1 in
  let phi_n = bn_mul p1 q1 in
  let d1 = bn_mul phi_n rBlind in
  let d2 = bn_add_carry d1 d in
  assert (bn_v d2 == bn_v d + bn_v rBlind * bn_v phi_n);
  let s = mod_exp nBits n m (pBits + qBits + 65) d2 in
  lemma_exp_blinding_bn #nBits #pBits #qBits #dBits #mBits n phi_n p q d m rBlind;
  s
