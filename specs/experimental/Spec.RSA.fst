module Spec.RSA

open FStar.Seq
open FStar.Mul
open FStar.UInt
open Spec.SHA2_256

module U8 = FStar.UInt8
module U32 = FStar.UInt32

let max_input_len_sha256 = pow2 61
let hLen = 32

type byte = UInt8.t
type bytes = seq byte

type elem (n:pos) = e:int{e >= 0 /\ e < n}

type rsa_pubkey =
	| Mk_rsa_pubkey: n:pos -> e:elem n -> rsa_pubkey
	
type rsa_privkey =
	| Mk_rsa_privkey: pkey:rsa_pubkey -> d:elem (Mk_rsa_pubkey?.n pkey) -> rsa_privkey

val nat_to_uint8: x:nat -> Tot UInt8.t
let nat_to_uint8 x = U8.uint_to_t (to_uint_t 8 x)

val nat_to_uint32: x:nat -> Tot UInt32.t
let nat_to_uint32 x = U32.uint_to_t (to_uint_t 32 x)

(* a*x + b*y = gcd(a,b) *)
val extended_eucl: a:nat -> b:nat -> Tot (tuple2 int int) (decreases b)
let rec extended_eucl a b =
	if b = 0 then (1, 0)
	else
		match (extended_eucl b (a % b)) with
		| (x, y) -> (y, x - (op_Multiply (a/b) y))

#set-options "--z3rlimit 50 --max_fuel 2"

val mod_exp_loop: n:pos -> a:nat -> b:nat -> acc:elem n -> Tot (res:elem n) (decreases b)
let rec mod_exp_loop n a b acc =
	match b with
	| 0 -> acc
	| 1 -> (op_Multiply a acc) % n
	| e ->
		let a2 = (op_Multiply a a) % n in
		if (e % 2 = 0) then mod_exp_loop n a2 (b/2) acc
		else
			let acc = (op_Multiply a acc) % n in
			mod_exp_loop n a2 ((b - 1)/2) acc

val mod_exp: n:pos -> a:elem n -> b:elem n -> Tot (res:elem n)
let mod_exp n a b =
	let one_n = 1 % n in
	mod_exp_loop n a b one_n

val os2ip: b:bytes -> Tot nat (decreases (Seq.length b))
let rec os2ip b =
	let bLen = Seq.length b in
	if bLen = 0 then 0
	else op_Multiply (U8.v (head b)) (pow2 (op_Multiply 8 (bLen - 1))) + (os2ip (tail b))

val i2osp:
	n:nat -> bLen:nat{n < pow2 (op_Multiply 8 bLen)} -> 
	Tot (b:bytes{length b = bLen}) (decreases bLen)
let rec i2osp n bLen =
	if bLen = 0 then createEmpty #UInt8.t
	else
		let len = bLen - 1 in
		let t = pow2 (op_Multiply 8 len) in
		let x = nat_to_uint8 (n / t) in
		let n = n % t in
		append (create 1 x) (i2osp n len)

#reset-options

val get_octets: modBits:pos -> Tot nat
let get_octets modBits = (modBits - 1)/8 + 1

val get_length_em: modBits:pos -> Tot nat
let get_length_em modBits =
	 let k = get_octets modBits in
	 if ((modBits - 1) % 8 = 0)
	 then k - 1 else k

val hash_sha256:
	msg:bytes{length msg < max_input_len_sha256} ->
	Tot (msgHash:bytes{length msgHash = hLen})
let hash_sha256 msg = SHA2_256.hash msg

#reset-options "--lax"

val mgf_sha256_loop:
	mgfseed:bytes{length mgfseed = hLen} ->
	counter_max:nat{counter_max <= pow2 32} -> counter:nat{counter <= counter_max} ->
	acc:bytes{length acc = op_Multiply counter hLen} ->
	Tot (res:bytes{length res = op_Multiply counter_max hLen}) (decreases (counter_max - counter))

let rec mgf_sha256_loop mgfseed counter_max counter acc =
	if (counter < counter_max) then begin
		(**) assert(counter < pow2 (op_Multiply 8 4));
		let c = i2osp counter 4 in
		let mgfseed_c = append mgfseed c in
		(**) assert(length mgfseed_c = hLen + 4);
		(**) assert(length mgfseed_c < max_input_len_sha256);
		(**) assert(length acc = op_Multiply counter hLen);
		let acc = append acc (hash_sha256 mgfseed_c) in
		(**) assert(length acc = op_Multiply counter hLen + hLen);
		mgf_sha256_loop mgfseed counter_max (counter + 1) acc end
	else acc

val mgf_sha256:
	mgfseed:bytes{length mgfseed = hLen} ->
	maskLen:nat{maskLen > 0 /\ maskLen <= op_Multiply (pow2 32) hLen} ->
	Tot (mask:bytes{length mask = maskLen})

let mgf_sha256 mgfseed maskLen =
	(**) assert(maskLen - 1 < op_Multiply (pow2 32) hLen);
	(**) assert((maskLen - 1) / hLen < pow2 32);
	let counter_max = (maskLen - 1) / hLen + 1 in
	(**) assert(counter_max <= pow2 32);
	let acc = mgf_sha256_loop mgfseed counter_max 0 (createEmpty #UInt8.t) in
	slice acc 0 maskLen

val xorDB: b1:bytes -> b2:bytes{length b2 = length b1} -> Tot (res:bytes{length res = length b1})
let xorDB b1 b2 = Spec.Lib.map2 (fun x y -> U8.(x ^^ y)) b1 b2

val pss_encode:
	sLen:nat ->
	modBits:pos{get_length_em modBits >= sLen + hLen + 2} ->
	msg:bytes{length msg < max_input_len_sha256} ->
	salt:bytes{length salt = sLen} -> Tot (em:bytes{length em = get_length_em modBits})

let pss_encode sLen modBits msg salt =
	let mHash = hash_sha256 msg in
	let emLen = get_length_em modBits in
	let emBits = modBits - 1 in
	let m1 = append (create 8 0x00uy) (append mHash salt) in
	(**) assert(length m1 = 8 + hLen + sLen);
	(**) assume(length m1 < max_input_len_sha256);
	let m1Hash = hash_sha256 m1 in
	let ps = create (emLen - sLen - hLen - 2) 0x00uy in
	let one_salt = append (create 1 0x01uy) salt in
	let db = append ps one_salt in
	(**) assert(length db = length ps + length one_salt);
	(**) assert(length ps = emLen - sLen - hLen - 2);
	(**) assert(length one_salt = 1 + sLen);
	(**) assert(length db = (emLen - sLen - hLen - 2) + (1 + sLen));
	(**) assert((emLen - sLen - hLen - 2) + (1 + sLen) = emLen - hLen - 1);
	(**) assert(length db = emLen - hLen - 1);
	(**) assume(emLen - hLen - 1 <= op_Multiply (pow2 32) hLen);
	let dbMask = mgf_sha256 m1Hash (emLen - hLen - 1) in
	let maskedDB = xorDB db dbMask in
	(**) assert(length maskedDB = emLen - hLen - 1);
	let zeroL = 8 - emBits % 8 in
	(**) assert(0 <= emBits % 8 /\ emBits % 8 < 8);
	(**) assert(zeroL < 8);
	(**) assert(U8.v 0xffuy < pow2 8);
	let zeroL = nat_to_uint32 zeroL in
	(**) assert(U32.v zeroL < 8);
	let maskedDB_0 = U8.((index maskedDB 0) &^ (0xffuy >>^ zeroL)) in
	let maskedDB = upd maskedDB 0 maskedDB_0 in
	let m1Hash_bc = append m1Hash (create 1 0xbcuy) in
	let res = append maskedDB m1Hash_bc in
	(**) assert(length res = length maskedDB + length m1Hash_bc);
	(**) assert(length m1Hash_bc = hLen + 1);
	(**) assert(length res = (emLen - hLen - 1) + (hLen + 1));
	(**) assert(length res = emLen);
	(**) assert(length res = get_length_em modBits);
	res

val pss_verify:
	sLen:nat ->
	modBits:pos{get_length_em modBits >= sLen + hLen + 2} ->
	em:bytes{length em = get_length_em modBits} ->
	msg:bytes{length msg < max_input_len_sha256} -> Tot bool

let pss_verify sLen modBits em msg =
	let mHash = hash_sha256 msg in
	let emLen = get_length_em modBits in
	let emBits = modBits - 1 in
	if not (U8.(index em (emLen - 1) =^ 0xbcuy)) then false
	else begin
		let maskedDB, m1Hash_bc = split em (emLen - hLen - 1) in
		let m1Hash, bc = split m1Hash_bc hLen in
		let zeroL = 8 - emBits % 8 in
		(**) assert(0 <= emBits % 8 /\ emBits % 8 < 8);
		(**) assert(zeroL < 8);
		(**) assert(U8.v 0xffuy < pow2 8);
		let tmp = U8.((index maskedDB 0) &^ (0xffuy <<^ (nat_to_uint32 (8 - zeroL)))) in
		if not (U8.(tmp =^ 0x00uy)) then false
		else begin
			(**) assume(emLen - hLen - 1 <= op_Multiply (pow2 32) hLen);
			let dbMask = mgf_sha256 m1Hash (emLen - hLen - 1) in
			(**) assert(length maskedDB = emLen - hLen - 1);
			(**) assert(length dbMask = emLen - hLen - 1);
			let db = xorDB maskedDB dbMask in
			(**) assert(U8.v 0xffuy < pow2 8);
			let db_0 = U8.((index db 0) &^ (0xffuy >>^ (nat_to_uint32 zeroL))) in
			let db = upd db 0 db_0 in
			let pad2 = create (emLen - sLen - hLen - 2) 0x00uy in
			let pad2 = append pad2 (create 1 0x01uy) in
			let pad, salt = split db (emLen - sLen - hLen - 1) in
			(**) assert(length db = emLen - hLen - 1);
			(**) assert(length pad = emLen - sLen - hLen - 1);
			(**) assert(length salt = length db - length pad);
			(**) assert(length salt = (emLen - hLen - 1) - (emLen - sLen - hLen - 1));
			(**) assert((emLen - hLen - 1) - (emLen - sLen - hLen - 1) = emLen - hLen - 1 - emLen + sLen + hLen + 1);
			(**) assume(emLen - hLen - 1 - emLen + sLen + hLen + 1 = sLen);
			(**) assert(length salt = sLen);
			if not (pad = pad2) then false
			else begin
				let pad1 = create 8 0x00uy in
				let mHash_salt = append mHash salt in
				(**) assert(length mHash_salt = length mHash + length salt);
				(**) assert(length mHash_salt = hLen + sLen);
				let m1 = append pad1 mHash_salt in
				(**) assert(length m1 = 8 + length mHash_salt);
				(**) assert(length m1 = 8 + hLen + sLen);
				(**) assume(length m1 < max_input_len_sha256);
				let m1Hash' = hash_sha256 m1 in
				m1Hash = m1Hash'
			end
		end 
	end

#reset-options "--z3rlimit 15"

(* msg -> em *)
(* |n| = modBits = k;
   |em| = get_length_em modBits = k or k-1;
   |sgnt| = get_octets modBits = k *)
val rsa_sign:
	sLen:nat ->
	modBits:pos{get_length_em modBits >= sLen + hLen + 2} ->
	msg:bytes{length msg < max_input_len_sha256} ->
	skey:rsa_privkey ->
	salt:bytes{length salt = sLen} ->
	rBlind:elem (Mk_rsa_pubkey?.n (Mk_rsa_privkey?.pkey skey)) ->
	Tot (sgnt:bytes{length sgnt = get_octets modBits})

let rsa_sign sLen modBits msg skey salt rBlind =
	let k = get_octets modBits in
	let d = Mk_rsa_privkey?.d skey in
	let pkey = Mk_rsa_privkey?.pkey skey in
	let n = Mk_rsa_pubkey?.n pkey in
	let e = Mk_rsa_pubkey?.e pkey in

	let em = pss_encode sLen modBits msg salt in
	let m = os2ip em in
	(* BLINDING *)
	(* let m1 = (op_Multiply m (pow r e)) % n in *)
	let rBlind_inv, _ = extended_eucl rBlind n in
	let rBlind_e = mod_exp n rBlind e in
	let m1 = (op_Multiply m rBlind_e) % n in
	let s1 = mod_exp n m1 d in
	let s = (op_Multiply s1 rBlind_inv) % n in
	(**) assume(s < pow2 (op_Multiply 8 k));
	i2osp s k

val rsa_verify:
	sLen:nat ->
	modBits:pos{get_length_em modBits >= sLen + hLen + 2} ->
	sgnt:bytes{length sgnt = get_octets modBits} ->
	pkey:rsa_pubkey ->
	msg:bytes{length msg < max_input_len_sha256} -> Tot bool

let rsa_verify sLen modBits sgnt pkey msg =
	let emLen = get_length_em modBits in
	let e = Mk_rsa_pubkey?.e pkey in
	let n = Mk_rsa_pubkey?.n pkey in
	
	let s = os2ip sgnt in
	let s = s % n in
	let m = mod_exp n s e in
	(**) assume(m < pow2 (op_Multiply 8 emLen));
	let em = i2osp m emLen in
	pss_verify sLen modBits em msg