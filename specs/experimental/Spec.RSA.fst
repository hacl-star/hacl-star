module Spec.RSA

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Spec.Lib.RawIntTypes

module Hash = Spec.SHA2

(* BIGNUM *)
type bignum = nat
let bn_v n = n
let bn n = n
let bn_add a b = a + b
let bn_mul a b = a `op_Multiply` b
let bn_sub a b = a - b
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
		| (x, y) -> (y, bn_sub x (bn_mul (bn_div a b) y))

#reset-options "--z3rlimit 50"

val mod_exp_loop: n:bignum{bn_v n > 1} -> a:bignum -> b:bignum -> acc:elem n -> Tot (res:elem n) (decreases b)
let rec mod_exp_loop n a b acc =
	match b with
	| 0 -> acc
	| 1 -> bn_mul_mod a acc n
	| e ->
		let a2 = bn_mul_mod a a n in
		let acc =
			if (bn_is_even e) then acc
			else bn_mul_mod a acc n in
		mod_exp_loop n a2 (bn_div2 b) acc

val mod_exp: n:bignum{bn_v n > 1} -> a:elem n -> b:bignum -> Tot (res:elem n)
let mod_exp n a b =
	mod_exp_loop n a b (bn 1)

(*
val pow: a:bignum -> n:bignum -> Tot bignum (decreases n)
let rec pow a n =
	match n with
	| 0 -> 1
	| _ -> 
		let b = pow a (n/2) in
		op_Multiply b (op_Multiply b (if n % 2 = 0 then 1 else a))

val fexp: n:pos -> a:elem n -> b:elem n -> Tot (res:elem n) 
let fexp n a b = (pow a b) % n
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

(* LEMMAS from FStar.Math.Lemmas *)
#reset-options "--z3rlimit 30 --initial_fuel 1 --max_fuel 1"

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
type modBits = modBits:size_t{modBits > 0}

noeq type rsa_pubkey (modBits:modBits) =
	| Mk_rsa_pubkey: n:bignum{1 < bn_v n /\ bn_v n < pow2 modBits} -> e:elem n -> rsa_pubkey modBits
	
noeq type rsa_privkey (modBits:modBits) =
	| Mk_rsa_privkey: pkey:rsa_pubkey modBits -> d:elem (Mk_rsa_pubkey?.n pkey) -> p:elem (Mk_rsa_pubkey?.n pkey) -> q:elem (Mk_rsa_pubkey?.n pkey) -> rsa_privkey modBits

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
	modBits:modBits ->
	skey:rsa_privkey modBits ->
	rBlind:elem (Mk_rsa_pubkey?.n (Mk_rsa_privkey?.pkey skey)) ->
	sLen:size_t{sLen + hLen + 8 < pow2 32 /\ (blocks modBits 8) - sLen - hLen - 3 >= 0 /\ 
				sLen + hLen + 8 < max_input_len_sha256} ->
	salt:lbytes sLen ->
	msgLen:size_t{msgLen < max_input_len_sha256} ->
	msg:lbytes msgLen ->
	Tot (sgnt:lbytes (blocks modBits 8))

let rsa_sign modBits skey rBlind sLen salt msgLen msg =
	let k = blocks modBits 8 in
	let d = Mk_rsa_privkey?.d skey in
	let pkey = Mk_rsa_privkey?.pkey skey in
	let n = Mk_rsa_pubkey?.n pkey in
	let e = Mk_rsa_pubkey?.e pkey in
	let p = Mk_rsa_privkey?.p skey in
	let q = Mk_rsa_privkey?.q skey in
	assert (modBits <= 8 * k);
	pow2_le_compat (8 * k) modBits;
	assert (pow2 modBits <= pow2 (8 * k));
	assert (bn_v n < pow2 (8 * k));

	let msBits = (modBits - 1) % 8 in
	let em = create k (u8 0) in
	let em = pss_encode msBits sLen salt msgLen msg k em in
	let m = os2ip k em in
	(* BLINDING *)
	let phi_n = (p - 1) * (q - 1) in
	let d' = d + rBlind * phi_n in
	let s = mod_exp n m d' in

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
		let m = mod_exp n s e in
		let em = create k (u8 0) in
		let em = i2osp m k em in
		let msBits = (modBits - 1) % 8 in
		pss_verify sLen msBits k em msgLen msg end
	else false