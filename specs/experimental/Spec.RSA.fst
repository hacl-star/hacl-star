module Spec.RSA

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Spec.Lib.RawIntTypes

open FStar.Math.Lemmas
open Spec.RSA.Lemmas

module Hash = Spec.SHA2

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
let bn_div x y = x / y
let bn_mod x y = x % y

type elem (n:nat) = e:nat{e < n}

#reset-options "--z3rlimit 50 --max_fuel 2"

val mont_inverse_: 
	a:bignum -> exp_2:nat -> y:bignum -> i:nat{1 < i /\ i <= exp_2} -> Tot bignum
	(decreases (exp_2 - i))
let rec mont_inverse_ a exp_2 y i =
	if i < exp_2 then begin
		let pow2_i1 = pow2 (i - 1) in
		let pow2_i = pow2_i1 * 2 in
		let y = if (pow2_i1 < (a * y) % pow2_i) then y + pow2_i1 else y in
		mont_inverse_ a exp_2 y (i + 1) end
	else y

#reset-options "--z3rlimit 50 --max_fuel 0"

//res = a^(-1) % 2^(exp_2)
val mont_inverse: a:bignum -> exp_2:nat{exp_2 > 1} -> Tot bignum
let mont_inverse a exp_2 = mont_inverse_ a (exp_2 + 1) 1 2

#reset-options "--z3rlimit 300 --max_fuel 0"

val mont_reduction:
	modBits:size_t{modBits > 1} ->
	r:nat{r = pow2 (modBits + 2) /\ r > 0} ->
	n:nat{1 < n /\ 4 * n < r} -> n':int ->
	c:nat{c < 4 * n * n} -> Pure (elem (n + n))
	(requires (True))
	(ensures (fun res -> res % n == (c / r) % n))
let mont_reduction modBits r n n' c =
	let m = (c * n') % r in
	assert (m < r);
	let res = (c + m * n) / r in
	assert (c + m * n < 4 * n * n + r * n);
	assert (c + m * n < r * n + r * n);
	lemma_div_lt_ab (c + m * n) (r * n + r * n) r;
	distributivity_add_right r n n;
	multiple_division_lemma (n + n) r;
	assert (res < n + n);
	lemma_mont_reduction res r c n m;
	res

#reset-options "--z3rlimit 50 --max_fuel 0"

val karatsuba_mont_mod:
	modBits:size_t{modBits > 1} ->
	r:nat{r = pow2 (modBits + 2) /\ r > 0} ->
	n:nat{1 < n /\ 4 * n < r} -> n':int ->
	a:elem (n + n) -> b:elem (n + n) -> Pure (elem (n + n))
	(requires (True))
	(ensures (fun res -> res % n == (a * b / r) % n))
let karatsuba_mont_mod modBits r n n' a b =
	//let c = karatsuba x a b in
	let c = a * b in
	assert (c < 4 * n * n);
 	mont_reduction modBits r n n' c

#reset-options "--z3rlimit 150 --max_fuel 0"

val to_mont:
	modBits:size_t{modBits > 1} ->
	r:nat{r = pow2 (modBits + 2) /\ r > 0} ->
	n:nat{1 < n /\ 4 * n < r} -> n':int ->
	a:elem n -> Pure (elem (n + n))
	(requires (True))
	(ensures (fun res -> res % n == (a * r) % n))
let to_mont modBits r n n' a =
	let r2 = (r * r) % n in
	assert (r2 < n);
	let c = a * r2 in
	assert (c < n * n);
	let res = mont_reduction modBits r n n' c in
	assert (res % n == (c / r) % n);
	lemma_mod_div_simplify a r n;
	res

#reset-options "--z3rlimit 300 --max_fuel 0"

val from_mont:
	modBits:size_t{modBits > 1} ->
	r:nat{r = pow2 (modBits + 2) /\ r > 0} ->
	n:nat{1 < n /\ 4 * n < r} -> n':int ->
	a_r:elem (n + n) -> Pure (elem n)
	(requires (True))
	(ensures (fun res -> res == (a_r / r) % n))
let from_mont modBits r n n' a_r =
	let m = (a_r * n') % r in
	assert (m < r);
	let res = (a_r + m * n) / r in
	assert (a_r + m * n < n + n + r * n);
	lemma_div_lt_ab (a_r + m * n) (n + n + r * n) r;
	assert ((a_r + m * n) / r < (n + n + r * n) / r);
	division_addition_lemma (n + n) r n;
	assert (res < (n + n) / r + n); // !! assert (res < 1 + n)
	assert (n + n < 4 * n);
	assert (n + n < r);
	small_division_lemma_1 (n + n) r;
	assert ((n + n) / r = 0);
	assert (res < n);
	lemma_mont_reduction_1 res r a_r n m;
	res

#reset-options "--z3rlimit 300 --max_fuel 2"

val mod_exp_:
	modBits:size_t{modBits > 1} ->
	r:nat{r = pow2 (modBits + 2) /\ r > 0} ->
	n:nat{1 < n /\ 4 * n < r} -> n':int ->
	a:elem (n + n) -> b:nat -> acc:elem (n + n) -> Pure (elem (n + n))
	(requires True)
	(ensures (fun res -> res % n == ((pow a b) * acc / pow r b) % n))
	(decreases b)
let rec mod_exp_ modBits r n n' a b acc =
	if b = 0
	then acc
	else begin
		let a2 = karatsuba_mont_mod modBits r n n' a a in
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
			let acc' = karatsuba_mont_mod modBits r n n' a acc in
			assert (acc' % n == (a * acc / r) % n);
		    let res = mod_exp_ modBits r n n' a2 b2 acc' in
			assert (res % n == ((pow a2 b2) * acc' / pow r b2) % n); //from ind hypo
			lemma_mod_exp_1 n a a2 b b2 acc acc' r res;
			res end
		end

#reset-options "--z3rlimit 150 --max_fuel 0"

val mod_exp:
	modBits:size_t{modBits > 1} ->
	n:bignum{1 < n /\ n < pow2 modBits} ->
	a:elem n -> b:bignum -> Pure (elem n)
	(requires True)
	(ensures (fun res -> res == (pow a b) % n))
let mod_exp modBits n a b =
	let r = pow2 (2 + modBits) in
	lemma_r_n modBits r n;
	assert (4 * n < r);
	let n'= mont_inverse n (2 + modBits) in
	let n' = -1 * n' in
	let a_r = to_mont modBits r n n' a in
	assert (a_r % n == (a * r) % n);
	let acc_r = to_mont modBits r n n' 1 in
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
	bLen:size_t{bLen > 0} -> b:lbytes bLen -> Tot (res:bignum{bn_v res < pow2 (8 * bLen)})
let os2ip bLen b = nat_from_intseq_be #U8 #bLen b

val i2osp:
	n:bignum -> bLen:size_t{bn_v n < pow2 (8 * bLen)} -> b:lbytes bLen -> Tot (lbytes bLen)
let i2osp n bLen b = nat_to_bytes_be bLen n

#reset-options "--z3rlimit 50 --max_fuel 0"

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

(* Mask Generation Function *)
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

(* RSA *)
type modBits = modBits:size_t{modBits > 1}

noeq type rsa_pubkey (modBits:modBits) =
	| Mk_rsa_pubkey: n:bignum{1 < n /\ pow2 (modBits - 1) <= bn_v n /\ bn_v n < pow2 modBits} ->
					 e:elem n{bn_v e > 1} -> rsa_pubkey modBits
	
noeq type rsa_privkey (modBits:modBits) =
	| Mk_rsa_privkey: pkey:rsa_pubkey modBits ->
					  d:elem (Mk_rsa_pubkey?.n pkey){bn_v d > 1} ->
					  p:elem (Mk_rsa_pubkey?.n pkey){bn_v p > 1} ->
					  q:elem (Mk_rsa_pubkey?.n pkey){bn_v q > 1 /\ bn_v (Mk_rsa_pubkey?.n pkey) = bn_v p * bn_v q} -> rsa_privkey modBits

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
	let m1Hash' = sub m1Hash 0 hLen in
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
	Tot (lbytes emLen)

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
	modBits:modBits ->
	skey:rsa_privkey modBits ->
	rBlind:bignum{rBlind > 0} ->
	sLen:size_t{sLen + hLen + 8 < pow2 32 /\ (blocks modBits 8) - sLen - hLen - 3 >= 0 /\
				sLen + hLen + 8 < max_input_len_sha256} ->
	salt:lbytes sLen ->
	msgLen:size_t{msgLen < max_input_len_sha256} ->
	msg:lbytes msgLen ->
	Tot (sgnt:lbytes (blocks modBits 8))

let rsa_sign modBits skey rBlind sLen salt msgLen msg =
	let pkey = Mk_rsa_privkey?.pkey skey in
	let n = Mk_rsa_pubkey?.n pkey in
	let e = Mk_rsa_pubkey?.e pkey in
	let d = Mk_rsa_privkey?.d skey in
	let p = Mk_rsa_privkey?.p skey in
	let q = Mk_rsa_privkey?.q skey in
	let k = blocks modBits 8 in
	assert (modBits <= 8 * k);
	pow2_le_compat (8 * k) modBits;
	assert (pow2 modBits <= pow2 (8 * k));
	assert (bn_v n < pow2 (8 * k));

	let msBits = (modBits - 1) % 8 in
	let em = create k (u8 0) in
	let em = pss_encode msBits sLen salt msgLen msg k em in
	let m = os2ip k em in
	assume (bn_v m < bn_v n);
	(* BLINDING *)
	let phi_n = (p - 1) * (q - 1) in
	let d' = d + rBlind * phi_n in
	assert (d' > 0);
	let s = mod_exp modBits n m d' in
	assert (s == (pow m d') % n);
	lemma_exp_blinding n phi_n p q d m rBlind;
	assert (s == (pow m d) % n);

	let sgnt = create k (u8 0) in
	assert (bn_v s < bn_v n);
	i2osp s k sgnt

val rsa_verify:
	modBits:modBits ->
	pkey:rsa_pubkey modBits ->
	sLen:size_t{sLen + hLen + 8 < pow2 32 /\ sLen + hLen + 8 < max_input_len_sha256} ->
	sgnt:lbytes (blocks modBits 8) ->
	msgLen:size_t{msgLen < max_input_len_sha256} ->
	msg:lbytes msgLen -> Tot bool

let rsa_verify modBits pkey sLen sgnt msgLen msg =
	let n = Mk_rsa_pubkey?.n pkey in
	let e = Mk_rsa_pubkey?.e pkey in
	let k = blocks modBits 8 in
	assert (modBits <= 8 * k);
	pow2_le_compat (8 * k) modBits;
	assert (pow2 modBits <= pow2 (8 * k));
	assert (n < pow2 (8 * k));

	let s = os2ip k sgnt in
	if bn_is_less s n then begin
		assert (bn_v s < bn_v n);
		let m = mod_exp modBits n s e in
		let em = create k (u8 0) in
		let em = i2osp m k em in
		let msBits = (modBits - 1) % 8 in
		pss_verify sLen msBits k em msgLen msg end
	else false