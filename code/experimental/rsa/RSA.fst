module RSA

open FStar.HyperStack.All
open FStar.Buffer
open FStar.Mul
open C.Loops

open Lib
open MGF
open Comparison
open Convert
open Exponentiation

module U8 = FStar.UInt8
module U32 = FStar.UInt32
open U32

inline_for_extraction let hLen = 32ul

(* RSA *)
noeq type rsa_pubkey =
	| Mk_rsa_pubkey: n:bignum -> e:bignum -> rsa_pubkey

noeq type rsa_privkey =
	| Mk_rsa_privkey: pkey:rsa_pubkey -> d:bignum -> rsa_privkey

val blocks: 
	x:U32.t{U32.v x > 0} -> m:U32.t{U32.v m > 0} -> r:U32.t{U32.v r > 0 /\ U32.v x <= (U32.v m) * (U32.v r)}
let blocks x m = (x -^ 1ul) /^ m +^ 1ul

val xor_bytes:
	len:U32.t ->
	b1:lbytes len ->
	b2:lbytes len{disjoint b1 b2} -> Stack unit
	(requires (fun h -> live h b1 /\ live h b2))
	(ensures (fun h0 _ h1 -> live h0 b1 /\ live h0 b2 /\ 
							 live h1 b1 /\ live h1 b2 /\ 
							 modifies_1 b1 h0 h1))

let xor_bytes len b1 b2 =
	C.Loops.in_place_map2 b1 b2 len (fun x y -> U8.(x ^^ y))

val pss_encode_:
	sLen:U32.t{U32.v sLen + U32.v hLen + 8 < pow2 32} ->
	salt:lbytes sLen ->
	msgLen:U32.t ->
	msg:uint8_p{length msg = U32.v msgLen /\ disjoint msg salt} ->
	emLen:U32.t{U32.v emLen - U32.v sLen - U32.v hLen - 2 >= 0} ->
	em:lbytes emLen{disjoint em salt /\ disjoint em msg} -> Stack unit
	(requires (fun h -> live h salt /\ live h msg /\ live h em))
	(ensures (fun h0 _ h1 -> live h0 salt /\ live h0 msg /\ live h0 em /\
							 live h1 salt /\ live h1 msg /\ live h1 em /\
							 modifies_1 em h0 h1))

let pss_encode_ sLen salt msgLen msg emLen em =
	push_frame();
	let mHash = create 0uy hLen in
	hash_sha256 mHash msgLen msg;
	
	let m1_size = 8ul +^ hLen +^ sLen in
	let m1 = create 0uy m1_size in
	blit mHash 0ul m1 8ul hLen;
	blit salt 0ul m1 (8ul +^ hLen) sLen;
	let m1Hash = create 0uy hLen in
	hash_sha256 m1Hash m1_size m1;
	
	let db_size = emLen -^ hLen -^ 1ul in
	let db = create 0uy db_size in
	let last_before_salt = db_size -^ sLen -^ 1ul in
	db.(last_before_salt) <- 1uy;
	blit salt 0ul db (last_before_salt +^ 1ul) sLen;
	
	let dbMask = create 0uy db_size in
	mgf_sha256 m1Hash db_size dbMask;
	xor_bytes db_size db dbMask;
	
	blit db 0ul em 0ul db_size;
	blit m1Hash 0ul em db_size hLen;
	em.(emLen -^ 1ul) <- 0xbcuy;
	pop_frame()
	
val pss_encode:
	msBits:U32.t{U32.v msBits < 8} ->
	sLen:U32.t{U32.v sLen + U32.v hLen + 8 < pow2 32} ->
	salt:lbytes sLen ->
	msgLen:U32.t{U32.v msgLen < pow2 61} ->
	msg:uint8_p{length msg = U32.v msgLen /\ disjoint msg salt} ->
	emLen:U32.t{U32.v emLen - U32.v sLen - U32.v hLen - 3 >= 0} ->
	em:lbytes emLen{disjoint em salt /\ disjoint em msg} -> Stack unit
	(requires (fun h -> live h salt /\ live h msg /\ live h em))
	(ensures (fun h0 _ h1 -> live h0 salt /\ live h0 msg /\ live h0 em /\
							 live h1 salt /\ live h1 msg /\ live h1 em /\
							 modifies_1 em h0 h1))

let pss_encode msBits sLen salt msgLen msg emLen em =
	if (msBits =^ 0ul)
	then begin
		let em' = Buffer.sub em 1ul (emLen -^ 1ul) in
		pss_encode_ sLen salt msgLen msg (emLen -^ 1ul) em';
		blit em' 0ul em 1ul (emLen -^ 1ul) end
	else 
		pss_encode_ sLen salt msgLen msg emLen em;
		em.(0ul) <- U8.(em.(0ul) &^ (0xffuy >>^ U32.(8ul -^ msBits)))

val pss_verify_:
	sLen:U32.t{U32.v sLen + U32.v hLen + 8 < pow2 32} ->
	msBits:U32.t{U32.v msBits < 8} ->
	emLen:U32.t{U32.v emLen - U32.v sLen - U32.v hLen - 2 >= 0} ->
	em:lbytes emLen ->
	msgLen:U32.t ->
	msg:uint8_p{length msg = U32.v msgLen /\ disjoint msg em} -> Stack bool
	(requires (fun h -> live h em /\ live h msg))
	(ensures (fun h0 _ h1 -> live h0 em /\ live h0 msg /\ 
						     live h1 em /\ live h1 msg /\
							 modifies_0 h0 h1))
	
let pss_verify_ sLen msBits emLen em msgLen msg =
	push_frame();
	let mHash = create 0uy hLen in
	hash_sha256 mHash msgLen msg;
	
	let pad_size = emLen -^ sLen -^ hLen -^ 1ul in
	let pad2 = create 0uy pad_size in
	pad2.(pad_size -^ 1ul) <- 0x01uy;
	
	let db_size = emLen -^ hLen -^ 1ul in
	let maskedDB = Buffer.sub em 0ul db_size in
	let m1Hash = Buffer.sub em db_size hLen in
	let dbMask = create 0uy db_size in
	mgf_sha256 m1Hash db_size dbMask;
	xor_bytes db_size maskedDB dbMask;
	(if (msBits >^ 0ul) then 
		maskedDB.(0ul) <- U8.(maskedDB.(0ul) &^ (0xffuy >>^ U32.(8ul -^ msBits))));
	
	let pad = Buffer.sub maskedDB 0ul pad_size in
	let salt = Buffer.sub maskedDB pad_size sLen in
	
	let m1_size = 8ul +^ hLen +^ sLen in
	let m1 = create 0uy m1_size in
	let m1Hash' = create 0uy 32ul in
	let res =
		if not (eqb pad pad2 pad_size) then false
		else begin
			(* first 8 elements should be 0x00 *)
			blit mHash 0ul m1 8ul hLen;
			blit salt 0ul m1 (8ul +^ hLen) sLen;
			hash_sha256 m1Hash' m1_size m1;
			eqb m1Hash m1Hash' hLen
		end in
	pop_frame();
	res
	
val pss_verify:
	sLen:U32.t{U32.v sLen + U32.v hLen + 8 < pow2 32} ->
	msBits:U32.t{U32.v msBits < 8} ->
	emLen:U32.t{U32.v emLen - U32.v sLen - U32.v hLen - 2 >= 0} ->
	em:lbytes emLen ->
	msgLen:U32.t ->
	msg:uint8_p{length msg = U32.v msgLen /\ disjoint msg em} -> Stack bool
	(requires (fun h -> live h em /\ live h msg))
	(ensures (fun h0 _ h1 -> live h0 em /\ live h0 msg /\ 
							 live h1 em /\ live h1 msg /\
							 modifies_0 h0 h1))

let pss_verify sLen msBits emLen em msgLen msg =
	let em_0 = U8.(em.(0ul) &^ (0xffuy <<^ msBits)) in
	let em_last = em.(emLen -^ 1ul) in

	if not (U8.(em_0 =^ 0x00uy) && U8.(em_last =^ 0xbcuy))
	then false
	else begin
		let em = if msBits =^ 0ul then Buffer.sub em 1ul (emLen -^ 1ul) else em in
		let emLen = if msBits =^ 0ul then (emLen -^ 1ul) else emLen in
		assert(length em = U32.v emLen);
		let em : lbytes emLen = em in
		if (emLen <^ sLen +^ hLen +^ 2ul)
		then false
		else pss_verify_ sLen msBits emLen em msgLen msg
		end

(* ADD disjointness for skey ? *)
val rsa_sign:
	modBits:U32.t{U32.v modBits > 0} ->
	skeyBits:U32.t{U32.v skeyBits <= U32.v modBits} ->
	skey:rsa_privkey ->
	sLen:U32.t{U32.v sLen + U32.v hLen + 8 < pow2 32 /\ U32.v (blocks modBits 8ul) - U32.v sLen - U32.v hLen - 3 >= 0 } ->
	salt:lbytes sLen ->
	msgLen:U32.t ->
	msg:uint8_p{length msg = U32.v msgLen /\ disjoint salt msg} ->
	sgnt:lbytes (blocks modBits 8ul){disjoint sgnt msg /\ disjoint sgnt salt} -> Stack unit
	(requires (fun h -> let pkey = Mk_rsa_privkey?.pkey skey in
			live h msg /\ live h salt /\ live h sgnt /\ 
			live h (Mk_rsa_privkey?.d skey) /\ live h (Mk_rsa_pubkey?.n pkey) /\ live h (Mk_rsa_pubkey?.e pkey)))
	(ensures (fun h0 _ h1 ->
			let pkey = Mk_rsa_privkey?.pkey skey in
			live h0 msg /\ live h0 salt /\ live h0 sgnt /\ live h1 msg /\ live h1 salt /\ live h1 sgnt /\
			live h0 (Mk_rsa_privkey?.d skey) /\ live h0 (Mk_rsa_pubkey?.n pkey) /\ live h0 (Mk_rsa_pubkey?.e pkey) /\
			live h1 (Mk_rsa_privkey?.d skey) /\ live h1 (Mk_rsa_pubkey?.n pkey) /\ live h1 (Mk_rsa_pubkey?.e pkey) /\
			modifies_1 sgnt h0 h1))

let rsa_sign modBits skeyBits skey sLen salt msgLen msg sgnt =
	push_frame();
	let pkey = Mk_rsa_privkey?.pkey skey in
	let n = Mk_rsa_pubkey?.n pkey in
	let e = Mk_rsa_pubkey?.e pkey in
	let d = Mk_rsa_privkey?.d skey in
	let k = blocks modBits 8ul in
	let nLen = blocks k 8ul in

	let em = create 0uy k in
	let m = create 0uL nLen in
	let s = create 0uL nLen in

	let msBits = (modBits -^ 1ul) %^ 8ul in
	pss_encode msBits sLen salt msgLen msg k em;
	text_to_nat k em m;
	
	mod_exp modBits nLen n m skeyBits d s;
	nat_to_text k s sgnt;
	pop_frame()


val rsa_verify:
	modBits:U32.t{U32.v modBits > 0} ->
	pkeyBits:U32.t{U32.v pkeyBits <= U32.v modBits} ->
	pkey:rsa_pubkey ->
	sLen:U32.t{U32.v sLen + U32.v hLen + 8 < pow2 32} ->
	sgnt:lbytes (blocks modBits 8ul) ->
	msgLen:U32.t ->
	msg:uint8_p{length msg = U32.v msgLen /\ disjoint msg sgnt} -> Stack bool
	(requires (fun h -> live h msg /\ live h sgnt /\ live h (Mk_rsa_pubkey?.e pkey) /\ live h (Mk_rsa_pubkey?.n pkey)))
	(ensures (fun h0 _ h1 -> live h0 msg /\ live h0 sgnt /\ live h1 msg /\ live h1 sgnt /\
			live h0 (Mk_rsa_pubkey?.e pkey) /\ live h0 (Mk_rsa_pubkey?.n pkey) /\
			live h1 (Mk_rsa_pubkey?.e pkey) /\ live h1 (Mk_rsa_pubkey?.n pkey) /\ 
			modifies_0 h0 h1))

let rsa_verify modBits pkeyBits pkey sLen sgnt msgLen msg =
	push_frame();
	let n = Mk_rsa_pubkey?.n pkey in
	let e = Mk_rsa_pubkey?.e pkey in
	let k = blocks modBits 8ul in
	let nLen = blocks k 8ul in

	let em = create 0uy k in
	let m = create 0uL nLen in	
	let s = create 0uL nLen in

	text_to_nat k sgnt s;
	let res =
		if (bn_is_less nLen s n) then begin
			mod_exp modBits nLen n s pkeyBits e m;
			nat_to_text k m em;
			let msBits = (modBits -^ 1ul) %^ 8ul in
			pss_verify sLen msBits k em msgLen msg end
		else false in
	pop_frame();
	res