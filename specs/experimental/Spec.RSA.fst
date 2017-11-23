module Spec.RSA

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Spec.Lib.RawIntTypes

open FStar.Math.Lemmas
open FStar.Math.Lib

module Hash = Spec.SHA2

(* BIGNUM *)
type bignum = nat
let bn_v n = n
let bn n = n
let bn_add a b = a + b
let bn_mul a b = a `op_Multiply` b
let bn_sub (a:bignum) (b:bignum{bn_v a >= bn_v b}) = a - b
let bn_mod a b = a % b
let bn_div a b = a / b
let bn_mul_mod a b n = (a `op_Multiply` b) % n
let bn_is_even x = (x % 2) = 0
let bn_div2 x = x / 2
let bn_is_less x y = x < y

type elem (n:bignum) = e:bignum{bn_v e < bn_v n}

(* a*x + b*y = gcd(a,b) *)
val extended_eucl: a:bignum -> b:bignum -> Tot (tuple2 int int) (decreases b)
let rec extended_eucl a b =
	if b = 0 then (1, 0)
	else
		match (extended_eucl b (bn_mod a b)) with
		| (x, y) -> (y, x - (bn_mul (bn_div a b) y))

(* LEMMAS from FStar.Math.Lemmas *)
#reset-options "--z3rlimit 30 --initial_fuel 0 --max_fuel 0"

val lemma_div_mod: a:nat -> p:pos -> Lemma (a = p * (a / p) + a % p)
let lemma_div_mod a p = ()

#reset-options "--z3rlimit 30 --initial_fuel 1 --max_fuel 1"

val pow2_double_sum: n:nat -> Lemma (pow2 n + pow2 n = pow2 (n + 1))
let pow2_double_sum n = ()

val pow2_lt_compat: n:nat -> m:nat -> Lemma
  (requires (m < n))
  (ensures  (pow2 m < pow2 n))
  (decreases (n - m))
let rec pow2_lt_compat n m =
  match n-m with
  | 1 -> ()
  | _ -> pow2_lt_compat (n-1) m; pow2_lt_compat n (n-1)

val pow2_le_compat: n:nat -> m:nat -> Lemma
  (requires (m <= n))
  (ensures  (pow2 m <= pow2 n))
  (decreases (n - m))
let pow2_le_compat n m =
  match n-m with
  | 0 -> ()
  | _ -> pow2_lt_compat n m

#reset-options "--z3rlimit 30 --max_fuel 1"

val pow2_plus: n:nat -> m:nat -> Lemma
  (ensures (pow2 n * pow2 m = pow2 (n + m)))
  (decreases n)
let rec pow2_plus n m =
  match n with
  | 0 -> ()
  | _ -> pow2_plus (n - 1) m

#reset-options "--z3rlimit 30 --initial_fuel 0 --max_fuel 0"

val lemma_div_lt: a:nat -> n:nat -> m:nat{m <= n} -> Lemma
	(requires (a < pow2 n))
	(ensures  (a / pow2 m < pow2 (n-m)))
let lemma_div_lt a n m =
  lemma_div_mod a (pow2 m);
  assert(a = pow2 m * (a / pow2 m) + a % pow2 m);
  pow2_plus m (n-m);
  assert(pow2 n = pow2 m * pow2 (n - m))

(* LEMMAS *)

val lemma_distributivity_mult: a:int -> b:int -> c:int -> d:int -> Lemma
  ((a + b) * (c + d) = a * c + a * d + b * c + b * d)
let lemma_distributivity_mult a b c d = ()

#reset-options "--z3rlimit 300 --initial_fuel 0 --max_fuel 0"

val lemma_karatsuba_mult:
	x:size_t -> a:bignum -> a0:bignum -> a1:bignum ->
	b:bignum -> b0:bignum -> b1:bignum -> Lemma
	(requires (let pow_x = pow2 (pow2 x) in
		a == a1 * pow_x + a0 /\ b == b1 * pow_x + b0))
	(ensures (let pow_x = pow2 (pow2 x) in
		let pow_x1 = pow2 (pow2 (x + 1)) in
		a * b == a1 * b1 * pow_x1 + (a0 * b1 + a1 * b0) * pow_x + a0 * b0))

let lemma_karatsuba_mult x a a0 a1 b b0 b1 =
	let pow_x = pow2 (pow2 x) in
	let pow_x1 = pow2 (pow2 (x + 1)) in
	assert (a * b == (a1 * pow_x + a0) * (b1 * pow_x + b0));
	lemma_distributivity_mult (a1 * pow_x) a0 (b1 * pow_x) b0;
	assert (a * b == a1 * b1 * pow_x * pow_x + (a0 * b1 + a1 * b0) * pow_x + a0 * b0);
	pow2_plus (pow2 x) (pow2 x);
	assert (pow2 (pow2 x) * pow2 (pow2 x) == pow2 (pow2 x + pow2 x));
	pow2_double_sum x;
	assert (pow2 x + pow2 x == pow2 (x + 1))

#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0"

val lemma_pow_div_karatsuba:
	x0:size_t{x0 > 0} -> b:bignum{bn_v b < pow2 (pow2 x0)} -> Lemma
	(requires (True))
	(ensures (let pow_x = pow2 (pow2 (x0 - 1)) in
		let b1 = bn_div b pow_x in
	 	0 <= bn_v b1 /\ bn_v b1 < pow_x))		 
let lemma_pow_div_karatsuba x0 b =
	let x = x0 - 1 in
	let pow_x = pow2 (pow2 x) in
	pow2_lt_compat x0 x;
	lemma_div_lt b (pow2 x0) (pow2 x);
	assert (bn_div b pow_x < pow2 (pow2 x0 - pow2 x));
	pow2_plus (x0 - 1) 1;
	assert (pow2 1 = 2);
	assert (pow2 x0 - pow2 (x0 - 1) == (pow2 (x0 - 1)) * (2 - 1))

val abs: x:int -> Tot (y:int{ (x >= 0 ==> y = x) /\ (x < 0 ==> y = -x) })
let abs x = if x >= 0 then x else -x

type sign =
	| Positive : sign
	| Negative : sign

(* a - b = (sign, |a - b|) *)
val abs_sub: x:size_t -> a:bignum -> b:bignum -> Pure (tuple2 sign bignum)
	(requires (bn_v a < pow2 (pow2 x) /\ bn_v b < pow2 (pow2 x)))
	(ensures (fun (s, res) -> bn_v res < pow2 (pow2 x) /\ bn_v res = abs (a - b)))
let abs_sub x a b =
	if (bn_is_less a b)
	then begin
		assert (bn_v b >= bn_v a);
		(Negative, bn_sub b a) end
	else begin
		assert (bn_v a >= bn_v b);
		(Positive, bn_sub a b) end

#reset-options "--z3rlimit 150 --initial_fuel 0 --max_fuel 0"

val add_sign:
	c0:bignum -> c1:bignum -> c2:bignum ->
	a0:bignum -> a1:bignum -> a2:bignum ->
	b0:bignum -> b1:bignum -> b2:bignum -> Pure bignum
	(requires (c0 == a0 * b0 /\ c1 == a1 * b1 /\ c2 == a2 * b2 /\
			   a2 = abs (a0 - a1) /\ b2 = abs (b0 - b1)))
	(ensures (fun res -> res == a1 * b0 + a0 * b1))

let add_sign c0 c1 c2 a0 a1 a2 b0 b1 b2 =
	let sa2 = if (a0 >= a1) then Positive else Negative in
	let sb2 = if (b0 >= b1) then Positive else Negative in
	if ((sa2 = Positive && sb2 = Positive) || (sa2 = Negative && sb2 = Negative)) 
	then begin
		bn_sub (c0 + c1) c2 end
	else bn_add (c0 + c1) c2

#reset-options "--z3rlimit 350 --max_fuel 2"

val karatsuba:
	x0:size_t -> a:bignum{bn_v a < pow2 (pow2 x0)} -> b:bignum{bn_v b < pow2 (pow2 x0)} -> Pure bignum
	(requires (True))
	(ensures (fun res -> res == a * b))
	(decreases x0)
let rec karatsuba x0 a b =
	if x0 < 11 then a * b
	else begin
		let x = x0 - 1 in
		let pow_x = pow2 (pow2 x) in
		
		let a0 = bn_mod a pow_x in let a1 = bn_div a pow_x in
		assert (0 <= bn_v a0 /\ bn_v a0 < pow_x);
		lemma_pow_div_karatsuba x0 a;
		assert (0 <= bn_v a1 /\ bn_v a1 < pow2 (pow2 x));
		lemma_div_mod a pow_x;

		let b0 = bn_mod b pow_x in let b1 = bn_div b pow_x in
		assert (0 <= bn_v b0 /\ bn_v b0 < pow_x);
		lemma_pow_div_karatsuba x0 b;
		assert (0 <= bn_v b1 /\ bn_v b1 < pow2 (pow2 x));
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
		let tmp = add_sign c0 c1 c2 a0 a1 a2 b0 b1 b2 in
		let c = c1 * pow_x1 + tmp * pow_x + c0 in
		lemma_karatsuba_mult x a a0 a1 b b0 b1;
		assert (c == a * b);
		c
	end

#reset-options "--max_fuel 0"

val lemma_distributivity_div:
	a:bignum -> b:bignum -> c:bignum{c > 0} -> Lemma
	((a + b) / c == a / c + b / c)
let lemma_distributivity_div a b c = admit()

val lemma_mult_div_mod:
	a:bignum -> b:bignum{b > 0} -> n:bignum{n > 0} -> Lemma
	(((a * n) / b) % n == 0)
let lemma_mult_div_mod a b n = admit()

val lemma_mult_div_mod1:
	a:bignum -> b:bignum{b > 0} -> n:bignum{n > 0} -> Lemma
	((n - (a * n) / b) % n == 0)
let lemma_mult_div_mod1 a b n = admit()

val lemma_sub_minus:
	a:bignum -> b:bignum -> Lemma
	(a - b == -(b - a))
let lemma_sub_minus a b = admit()

val lemma_mod_minus_distr_l: a:nat -> b:nat -> p:pos -> Lemma
  ((a - b) % p = ((a - b % p) % p))
let lemma_mod_minus_distr_l a b p = admit()

val lemma_mont_reduction1_rm: n:nat{n > 0} -> r:nat -> m:nat{m < r} -> Lemma
  (n - (m * n) / r > 0)
let lemma_mont_reduction1_rm n r m = admit()

val lemma_mod_div_simplify: a:nat -> r:nat{r > 0} -> n:nat{n > 0} -> Lemma
  (((a * ((r * r) % n))/ r) % n == (a * r) % n)
let lemma_mod_div_simplify a r n = admit()

val lemma_mod_mul_distr: a:nat -> b:nat -> n:nat{n > 0} -> Lemma
	((a * b) % n = ((a % n) * (b % n)) % n)
let lemma_mod_mul_distr a b n = admit()

#reset-options "--z3rlimit 50 --max_fuel 0"

val lemma_mont_reduction1:
	r:bignum -> c:bignum -> n:bignum{0 < n /\ n < r} -> m:bignum{m < r} -> Lemma
	(requires (0 <= (c + m * n) / r - n /\ (c + m * n) / r - n < n))
	(ensures ((c + m * n) / r - n == (c / r) % n))
let lemma_mont_reduction1 r c n m =
	small_modulo_lemma_1 ((c + m * n) / r - n) n;
	//assert ((c + m * n) / r - n == ((c + m * n) / r - n) % n);
	lemma_distributivity_div c (m * n) r;
	//assert ((c + m * n) / r - n == c / r + (m * n) / r - n);
	lemma_sub_minus ((m * n) / r) n;
	//assert ((c + m * n) / r - n == c / r - (n - (m * n) / r));
	lemma_mont_reduction1_rm n r m;
	lemma_mod_minus_distr_l (c / r) (n - (m * n) / r) n;
	lemma_mult_div_mod1 m r n;
	//assert (c / r + (m * n) / r - n == (c / r) % n);
	assert ((c + m * n) / r - n == (c / r) % n)

#reset-options "--z3rlimit 50 --max_fuel 0"

val lemma_mont_reduction2:
	r:bignum -> c:bignum -> n:bignum{0 < n /\ n < r} -> m:bignum -> Lemma
	(requires ((c + m * n) / r < n))
	(ensures ((c + m * n) / r == (c / r) % n ))
let lemma_mont_reduction2 r c n m =
	small_modulo_lemma_1 ((c + m * n) / r) n;
	//assert ((c + m * n) / r == ((c + m * n) / r) % n);
	lemma_distributivity_div c (m * n) r;
	//assert ((c + m * n) / r == c / r + (m * n) / r);
	lemma_mod_plus_distr_l ((m * n) / r) (c / r) n;
	lemma_mult_div_mod m r n;
	assert ((c + m * n) / r == (c / r) % n)

#reset-options "--z3rlimit 150 --max_fuel 0"

(* res = c / r mod n *)
val mont_reduction:
	r:bignum -> n:bignum{0 < n /\ n < r} -> n':int -> c:bignum -> Pure (elem n)
	(requires (c < n * n))
	(ensures (fun res -> res == (c / r) % n))
let mont_reduction r n n' c =
	assert (c < r * n);
	let m = (c * n') % r in
	assert (m < r);
	let u = (c + m * n) / r in
	assert (c + m * n < r * n + r * n);
	distributivity_add_right r n n;
	multiple_division_lemma (n + n) r;
	assert (u < n + n);
	let res =
		if u >= n then begin
			let res = u - n in
			assert (res < n);
			assert (res == (c + m * n) / r - n);
			assert ((c + m * n) / r - n < n);
			lemma_mont_reduction1 r c n m;
	 		res end
		else begin
			let res = u in
			assert (res < n);
			assert (res == (c + m * n) / r);
			assert ((c + m * n) / r < n);
			lemma_mont_reduction2 r c n m;
			res
		end in
	res

#reset-options "--z3rlimit 50 --max_fuel 0"

val karatsuba_mont_mod:
	x:size_t -> r:bignum{r = pow2 (pow2 x)} -> n:bignum{1 < n /\ n < r} -> n':int ->
	a:elem n -> b:elem n -> Pure (elem n)
	(requires (True))
	(ensures (fun res -> res == (a * b / r) % n))
let karatsuba_mont_mod x r n n' a b =
	let c = karatsuba x a b in
	assert (c == a * b);
	assert (c < n * n);
 	mont_reduction r n n' c

#reset-options "--z3rlimit 50 --max_fuel 0"

val to_mont:
	r:bignum -> n:bignum{1 < n /\ n < r} -> n':int -> a:elem n -> Pure (elem n)
	(requires (True))
	(ensures (fun res -> res == (a * r) % n))
let to_mont r n n' a =
	let r2 = (r * r) % n in
	assert (r2 < n);
	let c = a * r2 in
	assert (c < n * n);
	let res = mont_reduction r n n' c in
	assert (res == (c / r) % n);
	lemma_mod_div_simplify a r n;
	res

#reset-options "--z3rlimit 30 --max_fuel 0"

val from_mont:
	r:bignum -> n:bignum{1 < n /\ n < r} -> n':int -> a_r:elem n -> Pure (elem n)
	(requires (True))
	(ensures (fun res -> res == (a_r / r) % n))
let from_mont r n n' a_r = mont_reduction r n n' a_r

#reset-options "--z3rlimit 50"

val mod_exp_:
	x:size_t -> n:bignum{1 < n /\ n < pow2 (pow2 x)} -> a:elem n -> b:elem n -> Pure (res:elem n)
	(ensures (True))
	(requires (fun res -> res == (powx a b) % n))
	(decreases b)
let rec mod_exp_ x n a b =
	if b = 0 then 1
	else begin
		let b2 = bn_div2 b in
		let res' = mod_exp_ x n a b2 in
		assert (res' == (powx a b2) % n); //from ind hypo
		lemma_div_mod b 2;
		assert (b = 2 * b2 + b % 2);
		powx_lemma2 a b2 b2;
		assert (powx a (2 * b2) == powx a b2 * powx a b2); //property of exp
		//lemma_mod_mul_distr (powx a b2) (powx a b2) n;
		assume ((powx a b2 * powx a b2) % n == (((powx a b2) % n) * ((powx a b2) % n)) % n); //property of modular arithmetic
		let res = (res' * res') % n in
		assert (res == (powx a (2 * b2)) % n);
		let res =
			if (bn_is_even b) then begin
				assert (b % 2 = 0);
				assert (b = 2 * b2);
				assert (res == (powx a b) % n);
				res end
			else begin
				assert (b % 2 = 1);
				assert (b = 2 * b2 + 1);
				let res = (res * a) % n in
				powx_lemma2 a (2 * b2) 1;
				assert (powx a b == powx a (2 * b2) * powx a 1); //property of exp
				powx_lemma1 a; //assert (powx a 1 = a)
				//lemma_mod_mul_distr_l (powx a (2 * b2)) a n;
				assume ((powx a b) % n == (((powx a (2 * b2)) % n) * a) % n); //property of modular arithmetic
				assert (res == (powx a b) % n);
				res end in
		res
	end

val mod_exp:
	x:size_t -> n:bignum{1 < n /\ n < pow2 (pow2 x)} -> a:elem n -> b:elem n -> Pure (res:elem n)
	(ensures (True))
	(requires (fun res -> res == (powx a b) % n))
let mod_exp x n a b = mod_exp_ x n a b

(*
val mod_exp_:
	x:size_t -> r:bignum{r = pow2 (pow2 x)} -> n:bignum{1 < n /\ n < r} -> n':int ->
	a:elem n -> b:elem n -> Pure (res:elem n)
	(ensures (True))
	(requires (fun res -> res == ((powx a b) / powx r (b - 1)) % n))
	(decreases b)
let rec mod_exp_ x r n n' a b =
	if b = 0 then to_mont r n n' 1
	else begin
		let res' = mod_exp_ x r n n' a (bn_div2 b) in
		let res = karatsuba_mont_mod x r n n' res' res' in
		let res = if (bn_is_even b) then res else karatsuba_mont_mod x r n n' res a in
		res
	end

val mod_exp:
	x:size_t -> n:bignum{1 < n /\ n < pow2 (pow2 x)} -> 
	a:elem n -> b:elem n -> Pure (res:elem n)
	(ensures (True))
	(requires (fun res -> res == (powx a b) % n))
let mod_exp x n a b =
	let r = pow2 (pow2 x) in
	let n', _ = extended_eucl n r in
	let n' = -1 * n' in
	let a_r = to_mont r n n' a in
	let res_r = mod_exp_ x r n n' a_r b in
	let res = from_mont r n n' res_r in
	assume (res == (powx a b) % n);
	res
*)

(* BIGNUM CONVERT FUNCTIONS *)
#reset-options "--z3rlimit 50 --max_fuel 0"

val os2ip: bLen:size_t{bLen > 0} -> b:lbytes bLen -> Tot bignum
let os2ip bLen b =
  if (bLen = 0) 
  then (bn 0)
  else
    let next (i:size_t{i < bLen - 1}) (a:bignum): bignum =
	       bn_mul (bn_add a (bn (uint_to_nat b.[i]))) (bn 256) in
	let acc = repeati (bLen - 1) next (bn 0) in
    bn_add acc (bn (uint_to_nat (b.[bLen - 1])))

val i2osp:
	n:bignum -> bLen:size_t{bn_v n < pow2 (8 * bLen)} -> b:lbytes bLen ->
	Tot (lbytes bLen)
let i2osp n bLen b =
	if (bLen = 0)
	then b
	else
	let next (i:size_t{i < bLen}) (c:tuple2 bignum (lbytes bLen)) : tuple2 bignum (lbytes bLen) =
	    let (n, b) = c in
		let b_i = bn_v (bn_mod n (bn 256)) in
		assert (b_i < pow2 8);
	    let b' = b.[bLen - i - 1] <- nat_to_uint #U8 b_i in
	    let n' = bn_div n (bn 256) in
	    (n',b') in
  
        let (n',b') = repeati bLen next (n, b) in
	b'

#reset-options "--z3rlimit 50"

val blocks: x:size_t{x > 0} -> m:size_t{m > 0} -> r:size_t{r > 0 /\ x <= m * r}
let blocks x m = (x - 1) / m + 1

val xor_bytes: len:size_t -> b1:lbytes len -> b2:lbytes len -> Tot (res:lbytes len)
let xor_bytes len b1 b2 = map2 (fun x y -> x ^. y) b1 b2

val eq_bytes: len:size_t -> b1:lbytes len -> b2:lbytes len -> Tot bool
let eq_bytes len b1 b2 = for_all2 (fun x y -> uint_to_nat #U8 x = uint_to_nat #U8 y) b1 b2

(* SHA256 *)
let max_input_len_sha256 = pow2 61
unfold let hLen = 32
val hash_sha256:
	msgLen:size_t{msgLen < max_input_len_sha256} ->
	msg:lbytes msgLen ->
	hash:lbytes hLen ->
	Tot (msgHash:lbytes hLen)
let hash_sha256 msgLen msg hash = Hash.hash256 msgLen msg

(* RSA *)
type modBits x = modBits:size_t{0 < modBits /\ modBits = pow2 x}

noeq type rsa_pubkey (x:size_t) (modBits:modBits x) =
	| Mk_rsa_pubkey: n:bignum{1 < bn_v n /\ bn_v n < pow2 modBits} -> e:elem n -> rsa_pubkey x modBits
	
noeq type rsa_privkey (x:size_t) (modBits:modBits x) =
	| Mk_rsa_privkey: pkey:rsa_pubkey x modBits -> d:elem (Mk_rsa_pubkey?.n pkey) -> rsa_privkey x modBits

val mgf_sha256_loop:
	mgfseedLen:size_t{mgfseedLen = hLen + 4 /\ mgfseedLen < max_input_len_sha256} ->
	mgfseed:lbytes mgfseedLen ->
    counter_max:size_t{counter_max * hLen < pow2 32}->
	accLen:size_t{accLen = counter_max * hLen} ->
	acc:lbytes accLen ->
	Tot (res:lbytes accLen)

#reset-options "--z3rlimit 30 --max_fuel 0 --max_ifuel 0"

let mgf_sha256_loop mgfseedLen mgfseed counter_max accLen acc =
    let mHash = create hLen (u8 0) in
    let next (i:size_t{i < counter_max}) (acc:lbytes accLen) : lbytes accLen =
		let counter = nat_to_bytes_be 4 i in
		let mgfseed = update_sub mgfseed hLen 4 counter in
		let mHash = hash_sha256 mgfseedLen mgfseed mHash in
		update_sub acc (hLen * i) hLen mHash in
    repeati #(lbytes accLen) counter_max next acc

(* We only allow U32.t masklen, this means that we always have the property
   that maskLen <= op_Multiply (pow2 32) (U32.v hLen) as required by the spec *)
val mgf_sha256:
	mgfseedLen:size_t{mgfseedLen = hLen + 4 /\ mgfseedLen < max_input_len_sha256} ->
	mgfseed:lbytes mgfseedLen ->
	maskLen:size_t{maskLen > 0 /\ (blocks maskLen hLen) * hLen < pow2 32} ->
	mask:lbytes maskLen ->
	Tot (mask':lbytes maskLen)

#reset-options "--z3rlimit 50 --max_fuel 0"

let mgf_sha256 mgfseedLen mgfseed maskLen mask =
	let counter_max = blocks maskLen hLen in
	let accLen : size_t = counter_max * hLen in
	let acc = create accLen (u8 0) in
	let acc = mgf_sha256_loop mgfseedLen mgfseed counter_max accLen acc in
	slice acc 0 maskLen

#reset-options "--z3rlimit 50 --max_fuel 0"

val pss_encode_:
	sLen:size_t{sLen + hLen + 8 < pow2 32 /\ sLen + hLen + 8 < max_input_len_sha256} ->
	salt:lbytes sLen ->
	msgLen:size_t{msgLen < max_input_len_sha256} ->
	msg:lbytes msgLen ->
	emLen:size_t{emLen - sLen - hLen - 2 >= 0} ->
	em:lbytes emLen ->
	Tot (em':lbytes emLen)

let pss_encode_ sLen salt msgLen msg emLen em =
	let mHash = create hLen (u8 0) in
	let mHash = hash_sha256 msgLen msg mHash in

	let m1_size : size_t = 8 + hLen + sLen in
	let m1 = create m1_size (u8 0) in
	let m1 = update_sub m1 8 hLen mHash in
	let m1 = update_sub m1 (8 + hLen) sLen salt in
	let m1Hash = create 36 (u8 0) in
	let m1Hash' = create hLen (u8 0) in (* ??? *)
	let m1Hash' = hash_sha256 m1_size m1 m1Hash' in
	let m1Hash = update_sub m1Hash 0 hLen m1Hash' in
	
	let db_size : size_t = emLen - hLen - 1 in
	let db = create db_size (u8 0) in
	let last_before_salt = db_size - sLen - 1 in
	let db = db.[last_before_salt] <- (u8 1) in
	let db = update_sub db (last_before_salt + 1) sLen salt in

    let dbMask = create db_size (u8 0) in
	let dbMask = mgf_sha256 (hLen + 4) m1Hash db_size dbMask in
	let maskedDB = xor_bytes db_size db dbMask in

	let em = update_sub em 0 db_size maskedDB in
	let em = update_sub em db_size hLen m1Hash' in
	em.[emLen - 1] <- (u8 188)

val pss_encode:
	msBits:size_t{msBits < 8} ->
	sLen:size_t{sLen + hLen + 8 < pow2 32 /\ sLen + hLen + 8 < max_input_len_sha256} ->
	salt:lbytes sLen ->
	msgLen:size_t{msgLen < max_input_len_sha256} ->
	msg:lbytes msgLen ->
	emLen:size_t{emLen - sLen - hLen - 3 >= 0} ->
	em:lbytes emLen ->
	Tot (res:lbytes emLen)

#reset-options "--z3rlimit 100 --max_fuel 0"

let pss_encode msBits sLen salt msgLen msg emLen em =
	if msBits = 0
	then begin
		let em' = sub em 1 (emLen - 1) in
		let em' = pss_encode_ sLen salt msgLen msg (emLen - 1) em' in
		update_sub em 1 (emLen - 1) em' end
	else begin
		let em = pss_encode_ sLen salt msgLen msg emLen em in
		em.[0] <- em.[0] &. ((u8 255) >>. u32 (8 - msBits)) end

#reset-options "--z3rlimit 100 --max_fuel 0"

val pss_verify_:
	sLen:size_t{sLen + hLen + 8 < pow2 32 /\ sLen + hLen + 8 < max_input_len_sha256} ->
	msBits:size_t{msBits < 8} ->
	emLen:size_t{emLen - sLen - hLen - 2 >= 0} ->
	em:lbytes emLen ->
	msgLen:size_t{msgLen < max_input_len_sha256} ->
	msg:lbytes msgLen -> Tot bool

let pss_verify_ sLen msBits emLen em msgLen msg =
	let mHash = create hLen (u8 0) in
	let mHash = hash_sha256 msgLen msg mHash in

	let pad_size : size_t = emLen - sLen - hLen - 1 in
	let pad2 = create pad_size (u8 0) in
	let pad2 = pad2.[pad_size - 1] <- (u8 1) in

	let (db_size:size_t{db_size > 0}) = emLen - hLen - 1 in
	let maskedDB = slice em 0 db_size in
	let m1Hash0 = slice em db_size (db_size + hLen) in
	let m1Hash = create 36 (u8 0) in
	let m1Hash = update_sub m1Hash 0 hLen m1Hash0 in
	let dbMask = create db_size (u8 0) in
	let dbMask = mgf_sha256 (hLen + 4) m1Hash db_size dbMask in
	let db = xor_bytes db_size maskedDB dbMask in
	let db =
		if msBits > 0
		then db.[0] <- db.[0] &. (u8 255 >>. u32 (8 - msBits))
		else db in
	
	let pad = slice db 0 pad_size in
	let salt = slice db pad_size (pad_size + sLen) in

	let m1_size : size_t = 8 + hLen + sLen in
	let m1 = create m1_size (u8 0) in
	if not (eq_bytes pad_size pad pad2) then false
	else begin
		(* first 8 elements should be 0x00 *)
		let m1 = update_sub m1 8 hLen mHash in
		let m1 = update_sub m1 (8 + hLen) sLen salt in
		let m1Hash' = create hLen (u8 0) in
		let m1Hash' = hash_sha256 m1_size m1 m1Hash' in
		eq_bytes hLen m1Hash0 m1Hash'
	end

#reset-options "--z3rlimit 50 --max_fuel 0"

val pss_verify:
	sLen:size_t{sLen + hLen + 8 < pow2 32 /\ sLen + hLen + 8 < max_input_len_sha256} ->
	msBits:size_t{msBits < 8} ->
	emLen:size_t{emLen > 0} ->
	em:lbytes emLen ->
	msgLen:size_t{msgLen < max_input_len_sha256} ->
	msg:lbytes msgLen -> Tot bool

let pss_verify sLen msBits emLen em msgLen msg =
	let em_0 = em.[0] &. (u8 255 <<. u32 msBits) in
	let em_last = em.[emLen - 1] in

	if not ((uint_to_nat #U8 em_0 = 0) && (uint_to_nat #U8 em_last = 188))
	then false
	else begin
		let emLen' = if msBits = 0 then emLen - 1 else emLen in
		let em' : lbytes emLen' = if msBits = 0 then sub em 1 (emLen - 1) else em in
		if (emLen' < sLen + hLen + 2)
		then false
		else pss_verify_ sLen msBits emLen' em' msgLen msg
		end

#reset-options "--z3rlimit 300 --max_fuel 0"

val rsa_sign:
	x:size_t ->
	modBits:modBits x ->
	skey:rsa_privkey x modBits ->
	rBlind:elem (Mk_rsa_pubkey?.n (Mk_rsa_privkey?.pkey skey)) ->
	sLen:size_t{sLen + hLen + 8 < pow2 32 /\ (blocks modBits 8) - sLen - hLen - 3 >= 0 /\ 
				sLen + hLen + 8 < max_input_len_sha256} ->
	salt:lbytes sLen ->
	msgLen:size_t{msgLen < max_input_len_sha256} ->
	msg:lbytes msgLen ->
	Tot (sgnt:lbytes (blocks modBits 8))

let rsa_sign x modBits skey rBlind sLen salt msgLen msg =
	let k = blocks modBits 8 in
	let d = Mk_rsa_privkey?.d skey in
	let pkey = Mk_rsa_privkey?.pkey skey in
	let n = Mk_rsa_pubkey?.n pkey in
	let e = Mk_rsa_pubkey?.e pkey in
	assert (modBits <= 8 * k);
	pow2_le_compat (8 * k) modBits;
	assert (pow2 modBits <= pow2 (8 * k));
	assert (bn_v n < pow2 (8 * k));

	let msBits = (modBits - 1) % 8 in
	let em = create k (u8 0) in
	let em = pss_encode msBits sLen salt msgLen msg k em in
	let m = os2ip k em in
	(* BLINDING *)
	let rBlind_inv, _ = extended_eucl rBlind n in
	let rBlind_e = mod_exp x n rBlind e in
	let m1 = bn_mul_mod m rBlind_e n in
	assert (bn_v m1 < bn_v n);
	let s1 = mod_exp x n m1 d in
	let s = bn_mul_mod s1 rBlind_inv n in
	let sgnt = create k (u8 0) in
	assert (bn_v s < bn_v n);
	i2osp s k sgnt

val rsa_verify:
	x:size_t ->
	modBits:modBits x ->
	pkey:rsa_pubkey x modBits ->
	sLen:size_t{sLen + hLen + 8 < pow2 32 /\ sLen + hLen + 8 < max_input_len_sha256} ->
	sgnt:lbytes (blocks modBits 8) ->
	msgLen:size_t{msgLen < max_input_len_sha256} ->
	msg:lbytes msgLen -> Tot bool

let rsa_verify x modBits pkey sLen sgnt msgLen msg =
	let k = blocks modBits 8 in
	let e = Mk_rsa_pubkey?.e pkey in
	let n = Mk_rsa_pubkey?.n pkey in
	assert (modBits <= 8 * k);
	pow2_le_compat (8 * k) modBits;
	assert (pow2 modBits <= pow2 (8 * k));
	assert (n < pow2 (8 * k));

	let s = os2ip k sgnt in
	if bn_is_less s n then begin
		assert (bn_v s < bn_v n);
		let m = mod_exp x n s e in
		let em = create k (u8 0) in
		let em = i2osp m k em in
		let msBits = (modBits - 1) % 8 in
		pss_verify sLen msBits k em msgLen msg end
	else false