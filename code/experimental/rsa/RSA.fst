module RSA

open FStar.HyperStack.All
open FStar.Buffer
open FStar.Int.Cast
open FStar.All
open FStar.Mul

open Convert
open Exponentiation

module U32 = FStar.UInt32
module U8 = FStar.UInt8

type uint8_p = buffer FStar.UInt8.t
type bignum = buffer FStar.UInt64.t

let zero_8 = 0uy
let hLen = 32ul
let sLen = 20ul

type rsa_pubkey = 
	| Mk_rsa_pubkey: n:bignum -> e:bignum -> rsa_pubkey

val get_n: x:rsa_pubkey -> Stack bignum
	(requires (fun h -> True))  (* live h x *)
	(ensures (fun h0 _ h1 -> True))  (* live h0 x /\ live h1 n *)
let get_n x = 
	match x with 
	| Mk_rsa_pubkey n e -> n
	
val get_e: x:rsa_pubkey -> Stack bignum
	(requires (fun h -> True))  (* live h x *)
	(ensures (fun h0 _ h1 -> True))  (* live h0 x /\ live h1 e *)
let get_e x =
	match x with
	| Mk_rsa_pubkey n e -> e

type rsa_privkey =
	| Mk_rsa_privkey: pkey:rsa_pubkey -> d:bignum -> rsa_privkey
	
val get_pkey: x:rsa_privkey -> Stack rsa_pubkey
	(requires (fun h -> True))  (* live h x *)
	(ensures (fun h0 _ h1 -> True))  (* live h0 x /\ live h1 rsa_pubkey *)
let get_pkey x =
	match x with
	| Mk_rsa_privkey pkey d -> pkey

val get_d: x:rsa_privkey -> Stack bignum
	(requires (fun h -> True))  (* live h x *)
	(ensures (fun h0 _ h1 -> True))  (* live h0 x /\ live h1 d *)
let get_d x =
	match x with
	| Mk_rsa_privkey pkey d -> d
	
val get_octets: modBits:U32.t -> Tot U32.t
let get_octets modBits = U32.((modBits +^ 7ul) /^ 8ul)

val get_length_em: modBits:U32.t -> Tot U32.t
let get_length_em modBits =
	let k = get_octets modBits in
	if U32.((modBits -^ 1ul) %^ 8ul =^ 0ul)
	then U32.(k -^ 1ul) else k

val hash_sha256: 
	mHash:uint8_p{length mHash = U32.v hLen} -> m:uint8_p -> len:U32.t{U32.v len = length m} -> Stack unit
	(requires (fun h -> live h m /\ live h mHash))
	(ensures (fun h0 _ h1 -> live h0 m /\ live h0 mHash /\ live h1 mHash /\ modifies_1 mHash h0 h1))
let hash_sha256 mHash m len = SHA2_256.hash mHash m len

val mgf: 
	mgfseed_len:U32.t -> mgfseed:uint8_p{length mgfseed = U32.v mgfseed_len} ->  
	len:U32.t -> counter:U32.t -> acc:uint8_p{length acc = U32.(v (hLen *^ counter))} -> 
	res:uint8_p{length res = U32.v len} -> Stack unit
	(requires (fun h -> live h res /\ live h mgfseed /\ live h acc))
	(ensures (fun h0 _ h1 -> live h0 res /\ live h0 mgfseed /\ live h0 acc /\ live h1 res /\ modifies_1 res h0 h1)) 
let rec mgf mgfseed_len mgfseed len counter acc res =
	(* if len > op_Multiply (pow2 32) hLen then failwith "mask too long" *)
	push_frame();
	let c = create zero_8 4ul in
	c.(0ul) <- uint32_to_uint8 (U32.(counter >>^ 24ul));
	c.(1ul) <- uint32_to_uint8 (U32.(counter >>^ 16ul));
	c.(2ul) <- uint32_to_uint8 (U32.(counter >>^ 8ul));
	c.(3ul) <- uint32_to_uint8 counter;
	let tmp = create zero_8 U32.(mgfseed_len +^ 4ul) in
	blit mgfseed 0ul tmp 0ul mgfseed_len;
	blit c 0ul tmp mgfseed_len 4ul;
	let hash_tmp = create zero_8 hLen in
	hash_sha256 hash_tmp tmp U32.(mgfseed_len +^ 4ul);
	let counter = U32.(counter +^ 1ul) in
	let acc_size = U32.(counter *^ hLen) in
	let acc_tmp = create zero_8 acc_size in
	blit acc 0ul acc_tmp 0ul U32.(acc_size -^ hLen);
	blit hash_tmp 0ul acc_tmp U32.(acc_size -^ hLen) hLen;
	if U32.(acc_size <^ len)
	then mgf mgfseed_len mgfseed len counter acc_tmp res
	else blit acc_tmp 0ul res 0ul len;
	pop_frame()

val xordb:
	b1:uint8_p ->
	b2:uint8_p{length b2 = length b1} -> 
	len:U32.t{U32.v len <= length b1} -> Stack unit
	(requires (fun h -> live h b1 /\ live h b2))
	(ensures (fun h0 _ h1 -> live h0 b1 /\ live h0 b2 /\ live h1 b1 /\ modifies_1 b1 h0 h1))
	(decreases len)
let rec xordb b1 b2 len =
	push_frame();
	if U32.(len >^ 0ul) then
		let len = U32.(len -^ 1ul) in
		b1.(len) <- U8.(b1.(len) ^^ b2.(len));
		xordb b1 b2 len
	else ();
	pop_frame()

val pss_encode: 
	modBits:U32.t{U32.v (get_length_em modBits) >= U32.(v (sLen +^ hLen +^ 2ul))} ->
	msg:uint8_p -> len:U32.t{U32.v len = length msg} ->
	salt:uint8_p{length salt = U32.v sLen} ->
	em:uint8_p{length em = U32.v (get_length_em modBits)} -> Stack unit
	(requires (fun h -> live h msg /\ live h em /\ live h salt))
	(ensures (fun h0 _ h1 -> live h0 msg /\ live h0 em /\  live h0 salt /\ live h1 em /\ modifies_1 em h0 h1))
let pss_encode modBits msg len salt em =
	push_frame();
	let mHash = create zero_8 hLen in
	hash_sha256 mHash msg len;
	let emBits = U32.(modBits -^ 1ul) in
	let emLen = get_length_em modBits in
	let m1_size = U32.(8ul +^ hLen +^ sLen) in
	let m1 = create zero_8 m1_size in
	(* first 8 elements should be 0x00 *)
	blit mHash 0ul m1 8ul hLen;
	blit salt 0ul m1 U32.(8ul +^ hLen) sLen;
	let m1Hash = create zero_8 hLen in
	hash_sha256 m1Hash m1 m1_size;
	
	let db_size = U32.(emLen -^ hLen -^ 1ul) in
	let db = create zero_8 db_size in
	let ind_1 = U32.(emLen -^ sLen -^ hLen -^ 2ul) in
	db.(ind_1) <- 1uy;
	blit salt 0ul db U32.(ind_1 +^ 1ul) sLen;
	
	let dbMask = create zero_8 db_size in
	let acc = create zero_8 0ul in
	mgf hLen m1Hash db_size 0ul acc dbMask;

	xordb db dbMask db_size;
	let zeroL = U32.(8ul *^ emLen -^ emBits) in
	db.(0ul) <- U8.(db.(0ul) &^ (0xffuy >>^ zeroL));

	blit db 0ul em 0ul db_size;
	blit m1Hash 0ul em db_size hLen;
	upd em U32.(emLen -^ 1ul) 0xbcuy;
	pop_frame()

val pss_verify:
	modBits:U32.t{U32.v (get_length_em modBits) >= U32.(v (sLen +^ hLen +^ 2ul))} ->
	em:uint8_p{length em = U32.v (get_length_em modBits)} ->
	msg:uint8_p -> len:U32.t{U32.v len = length msg} -> Stack bool
	(requires (fun h -> live h msg /\ live h em))
	(ensures (fun h0 _ h1 -> live h0 msg /\ live h0 em /\ live h1 msg /\ live h1 em))
let pss_verify modBits em msg len =
	push_frame();
	let emLen = get_length_em modBits in
	let m1_size = U32.(8ul +^ hLen +^ sLen) in
	let pad_size = U32.(emLen -^ sLen -^ hLen -^ 1ul) in
	let db_size = U32.(emLen -^ hLen -^ 1ul) in

	let mHash = create zero_8 hLen in
	let m1Hash' = create zero_8 hLen in
	let m1 = create zero_8 m1_size in
	let pad2 = create zero_8 pad_size in
	let dbMask = create zero_8 db_size in

	hash_sha256 mHash msg len;
	let res = 
	if not (U8.(em.(U32.(emLen -^ 1ul)) =^ 0xbcuy)) then false else (
	let maskedDB = sub em 0ul db_size in
	let m1Hash = sub em db_size hLen in
	let zeroL = U32.(8ul *^ emLen -^ (modBits -^ 1ul)) in
	let tmp = U8.(maskedDB.(0ul) &^ (0xffuy <<^ U32.(8ul -^ zeroL))) in
	if not (U8.(tmp =^ 0x00uy)) then false else (
	let acc = create zero_8 0ul in
	mgf hLen m1Hash db_size 0ul acc dbMask;
	xordb maskedDB dbMask db_size;
	maskedDB.(0ul) <- U8.(maskedDB.(0ul) &^ (0xffuy >>^ zeroL));
	upd pad2 U32.(pad_size -^ 1ul) 0x01uy;

	let pad = sub maskedDB 0ul pad_size in
	if not (eqb pad pad2 pad_size) then false else (
	let salt = sub maskedDB pad_size sLen in
	(* first 8 elements should be 0x00 *)
	blit mHash 0ul m1 8ul hLen;
	blit salt 0ul m1 U32.(8ul +^ hLen) sLen;
	hash_sha256 m1Hash' m1 m1_size;
	eqb m1Hash m1Hash' hLen))) in
	pop_frame();
	res

val rsa_sign:
	modBits:U32.t{U32.v (get_length_em modBits) >= U32.(v (sLen +^ hLen +^ 2ul))} ->
	skeyBits:U32.t -> msgLen:U32.t ->
	msg:uint8_p{length msg = U32.v msgLen} ->
	skey:rsa_privkey ->
	salt:uint8_p{length salt = U32.v sLen} ->
	sgnt:uint8_p{length sgnt = U32.v (get_octets modBits)} -> Stack unit
	(requires (fun h -> live h msg /\ live h salt /\ live h sgnt))
	(ensures (fun h0 _ h1 -> live h0 msg /\ live h0 salt /\ live h0 sgnt /\ live h1 sgnt /\ modifies_1 sgnt h0 h1))
let rsa_sign modBits skeyBits msgLen msg skey salt sgnt =
	push_frame();
	let k = get_octets modBits in
	let d = get_d skey in
	let n = get_n (get_pkey skey) in
	
	let emLen = get_length_em modBits in
	let em = create zero_8 emLen in
	pss_encode modBits msg msgLen salt em;
	let mLen = get_size_nat emLen in
	let m = create 0uL mLen in
	text_to_nat em emLen m;
	
	(* todo: m % n *)
	let sLen = get_size_nat k in
	let s = create 0uL sLen in
    mod_exp modBits mLen skeyBits sLen n m d s;

	nat_to_text s k sgnt;
	pop_frame()
	
val rsa_verify:
	modBits:U32.t{U32.v (get_length_em modBits) >= U32.(v (sLen +^ hLen +^ 2ul))} ->
	msgLen:U32.t -> pkeyBits:U32.t ->
	sgnt:uint8_p{length sgnt = U32.v (get_octets modBits)} ->
	pkey:rsa_pubkey ->
	msg:uint8_p{length msg = U32.v msgLen} -> Stack bool
	(requires (fun h -> live h msg /\ live h sgnt))
	(ensures (fun h0 _ h1 -> live h0 msg /\ live h0 sgnt /\ live h1 msg /\ live h1 sgnt))
let rsa_verify modBits msgLen pkeyBits sgnt pkey msg =
	push_frame();
	let e = get_e pkey in
	let n = get_n pkey in
	
	(* the length of the signature in octets *)
	let k = get_octets modBits in
	let sLen = get_size_nat k in
	let s = create 0uL sLen in
	text_to_nat sgnt k s;
	
	(* todo: s % n *)
	let emLen = get_length_em modBits in
	let mLen = get_size_nat emLen in
	let m = create 0uL mLen in
	mod_exp modBits sLen pkeyBits mLen n s e m;
	
	let em = create zero_8 emLen in
	nat_to_text m emLen em;
	let res = pss_verify modBits em msg msgLen in
	pop_frame();
	res