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

#reset-options "--z3rlimit 150 --max_fuel 0"

val mont_reduction:
	modBits:size_nat{1 < modBits /\ modBits < pow2 32} ->
	r:nat{r = pow2 (modBits + 2) /\ r > 0} ->
	n:nat{1 < n /\ 4 * n < r} -> n':bignum ->
	c:nat{c < 4 * n * n} -> Pure (elem (n + n))
	(requires (True))
	(ensures (fun res -> res % n == (c / r) % n))
let mont_reduction modBits r n n' c =
	let m = (c * n') % r in
	assert (0 <= m /\ m < r);
	let m = r - m in
	assert (0 < m /\ m <= r);
	let res:nat = (c + n * m) / r in
	assert (c + m * n < 4 * n * n + r * n);
	assert (c + m * n < r * n + r * n);
    distributivity_add_right r n n;
	lemma_div_lt_ab (c + m * n) (r * (n + n)) r;
	multiple_division_lemma (n + n) r;
	lemma_mont_reduction res r c n m;
	res

val mul_mod_mont:
	modBits:size_nat{1 < modBits /\ modBits < pow2 32} ->
	r:nat{r = pow2 (modBits + 2) /\ r > 0} ->
	n:nat{1 < n /\ 4 * n < r} -> n':bignum ->
	a:elem (n + n) -> b:elem (n + n) -> Pure (elem (n + n))
	(requires (True))
	(ensures (fun res -> res % n == (a * b / r) % n))
let mul_mod_mont modBits r n n' a b =
	let c = a * b in
 	mont_reduction modBits r n n' c

val to_mont:
	modBits:size_nat{1 < modBits /\ modBits < pow2 32} ->
	r:nat{r = pow2 (modBits + 2) /\ r > 0} ->
	n:nat{1 < n /\ 4 * n < r} -> n':bignum ->
	r2:elem n -> a:elem n -> Pure (elem (n + n))
	(requires (r2 == (r * r) % n))
	(ensures (fun res -> res % n == (a * r) % n))
let to_mont modBits r n n' r2 a =
	let c = a * r2 in
	let res = mont_reduction modBits r n n' c in
	lemma_mod_div_simplify a r n;
	res

val from_mont:
	modBits:size_nat{1 < modBits /\ modBits < pow2 32} ->
	r:nat{r = pow2 (modBits + 2) /\ r > 0} ->
	n:nat{1 < n /\ 4 * n < r} -> n':bignum ->
	a_r:elem (n + n) -> Pure (elem n)
	(requires (True))
	(ensures (fun res -> res == (a_r / r) % n))
let from_mont modBits r n n' a_r =
	let m = (a_r * n') % r in
	assert (0 <= m /\ m < r);
	let m = r - m in
	assert (0 < m /\ m <= r);
	let res:nat = (a_r + n * m) / r in
	assert (a_r + m * n < n + n + r * n);
	lemma_div_lt_ab (a_r + m * n) (n + n + r * n) r;
	division_addition_lemma (n + n) r n;
	assert (n + n < 4 * n);
	assert (n + n < r);
	small_division_lemma_1 (n + n) r;
	lemma_mont_reduction_1 res r a_r n m;
	res

#reset-options "--z3rlimit 50 --max_fuel 2"

val mont_inverse_:
	n:bignum -> exp_2:size_nat -> nInv:bignum -> i:size_nat{1 < i /\ i <= exp_2} ->
	pow2_i1:bignum{0 < pow2_i1} -> pow2_i:bignum -> Tot bignum
	(decreases (exp_2 - i))
let rec mont_inverse_ n exp_2 nInv i pow2_i1 pow2_i =
	if i < exp_2 then begin
		let pow2_i1 = pow2_i1 * 2 in
		let pow2_i = pow2_i1 * 2 in
		let nnInv = (n * nInv) % pow2_i in
		let nInv = if (pow2_i1 < nnInv) then nInv + pow2_i1 else nInv in
		mont_inverse_ n exp_2 nInv (i + 1) pow2_i1 pow2_i end
	else nInv

#reset-options "--z3rlimit 50 --max_fuel 0"

//res = n^(-1) % 2^(exp_2)
val mont_inverse:
	n:bignum -> exp_2:size_nat{1 < exp_2 /\ exp_2 + 1 <= max_size_t} -> Tot bignum
let mont_inverse n exp_2 = mont_inverse_ n (exp_2 + 1) 1 2 1 0

#reset-options "--z3rlimit 150 --max_fuel 2"

val mod_exp_:
	modBits:size_nat{1 < modBits /\ modBits < pow2 32} ->
	r:nat{r = pow2 (modBits + 2) /\ r > 0} ->
	n:nat{1 < n /\ 4 * n < r} -> n':bignum ->
	a:elem (n + n) -> b:nat -> acc:elem (n + n) -> Pure (elem (n + n))
	(requires True)
	(ensures (fun res -> res % n == ((pow a b) * acc / pow r b) % n))
	(decreases b)
let rec mod_exp_ modBits r n n' a b acc =
	if b = 0
	then acc
	else begin
		let a2 = mul_mod_mont modBits r n n' a a in
		assert (a2 % n == (a * a / r) % n);
		let b2 = bn_div2 b in
		lemma_div_mod b 2;
		if (bn_is_even b) then begin
			assert (b = 2 * b2);
			let res = mod_exp_ modBits r n n' a2 b2 acc in
			assert (res % n == ((pow a2 b2) * acc / pow r b2) % n); //from ind hypo
			lemma_mod_exp n a a2 b b2 acc r res;
			res end
		else begin
			assert (b = 2 * b2 + 1);
			let acc' = mul_mod_mont modBits r n n' a acc in
			assert (acc' % n == (a * acc / r) % n);
		    let res = mod_exp_ modBits r n n' a2 b2 acc' in
			assert (res % n == ((pow a2 b2) * acc' / pow r b2) % n); //from ind hypo
			lemma_mod_exp_1 n a a2 b b2 acc acc' r res;
			res end
		end

#reset-options "--z3rlimit 150 --max_fuel 0"

val mod_exp:
	modBits:size_nat{1 < modBits /\ modBits + 3 < pow2 32} ->
	n:bignum{1 < n /\ n < pow2 modBits} ->
	a:elem n -> b:bignum -> Pure (elem n)
	(requires True)
	(ensures (fun res -> res == (pow a b) % n))
let mod_exp modBits n a b =
	let r = pow2 (2 + modBits) in
	lemma_r_n modBits r n;
	assert (4 * n < r);
	let n'= mont_inverse n (2 + modBits) in
	let r2 = (r * r) % n in
	let a_r = to_mont modBits r n n' r2 a in
	assert (a_r % n == (a * r) % n);
	let acc_r = to_mont modBits r n n' r2 1 in
	assert (acc_r % n == r % n);
	let res_r = mod_exp_ modBits r n n' a_r b acc_r in
	assert (res_r % n == ((pow a_r b) * acc_r / pow r b) % n);
	lemma_mod_exp_2 n a a_r b acc_r r res_r;
	assert (res_r % n == ((pow a b) * r) % n);
	let res = from_mont modBits r n n' res_r in
	assert (res == (res_r / r) % n);
	lemma_mod_mult_div_1 res_r r n;
	assert (res == ((res_r % n) / r) % n);
	assert (res == ((((pow a b) * r) % n) / r) % n);
	lemma_mod_mult_div_1 ((pow a b) * r) r n;
	assert (res == ((pow a b) * r / r) % n);
	multiple_division_lemma (pow a b) r;
	assert (res == (pow a b) % n);
	res

(* BIGNUM CONVERT FUNCTIONS *)
val os2ip:
	bLen:size_nat{bLen > 0} -> b:lbytes bLen -> Tot (res:bignum{bn_v res < pow2 (8 * bLen)})
let os2ip bLen b = nat_from_intseq_be #U8 #bLen b

val i2osp:
	n:bignum -> bLen:size_nat{bn_v n < pow2 (8 * bLen)} -> b:lbytes bLen -> Tot (lbytes bLen)
let i2osp n bLen b = nat_to_bytes_be bLen n