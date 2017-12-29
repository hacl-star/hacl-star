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
noeq type rsa_pubkey modBits pkeyBits =
	| Mk_rsa_pubkey: n:lbignum (bits_to_bn modBits) -> e:lbignum (bits_to_bn pkeyBits) -> rsa_pubkey modBits pkeyBits

noeq type rsa_privkey modBits pkeyBits skeyBits =
	| Mk_rsa_privkey: pkey:rsa_pubkey modBits pkeyBits -> d:lbignum (bits_to_bn skeyBits) -> rsa_privkey modBits pkeyBits skeyBits

val blocks: x:U32.t{v x > 0} -> m:U32.t{v m > 0} -> r:U32.t{v r > 0 /\ v x <= v m * v r}
let blocks x m = (x -^ 1ul) /^ m +^ 1ul

val xor_bytes:
	len:U32.t ->
	b1:lbytes len ->
	b2:lbytes len -> Stack unit
	(requires (fun h -> True))
	(ensures (fun h0 _ h1 -> True))

let xor_bytes len b1 b2 =
	C.Loops.in_place_map2 b1 b2 len (fun x y -> U8.(x ^^ y))

val pss_encode_:
	sLen:U32.t{v sLen + v hLen + 8 < pow2 32} ->
	salt:lbytes sLen ->
	msgLen:U32.t ->
	msg:lbytes msgLen ->
	emLen:U32.t{v emLen - v sLen - v hLen - 2 >= 0} ->
	em:lbytes emLen -> Stack unit
	(requires (fun h -> True))
	(ensures (fun h0 _ h1 -> True))

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
	msBits:U32.t{v msBits < 8} ->
	sLen:U32.t{v sLen + v hLen + 8 < pow2 32} ->
	salt:lbytes sLen ->
	msgLen:U32.t{v msgLen < pow2 61} ->
	msg:lbytes msgLen ->
	emLen:U32.t{v emLen - v sLen - v hLen - 3 >= 0} ->
	em:lbytes emLen -> Stack unit
	(requires (fun h -> True))
	(ensures (fun h0 _ h1 -> True))

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
	sLen:U32.t{v sLen + v hLen + 8 < pow2 32} ->
	msBits:U32.t{v msBits < 8} ->
	emLen:U32.t{v emLen - v sLen - v hLen - 2 >= 0} ->
	em:lbytes emLen ->
	msgLen:U32.t ->
	msg:lbytes msgLen -> Stack bool
	(requires (fun h -> True))
	(ensures (fun h0 _ h1 -> True))
	
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
	sLen:U32.t{v sLen + v hLen + 8 < pow2 32} ->
	msBits:U32.t{v msBits < 8} ->
	emLen:U32.t{v emLen - v sLen - v hLen - 2 >= 0} ->
	em:lbytes emLen ->
	msgLen:U32.t ->
	msg:lbytes msgLen -> Stack bool
	(requires (fun h -> True))
	(ensures (fun h0 _ h1 -> True))

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

val rsa_sign:
	modBits:U32.t{v modBits > 0} ->
	pkeyBits:U32.t{v pkeyBits <= v modBits} ->
	skeyBits:U32.t{v skeyBits <= v modBits} ->
	skey:rsa_privkey modBits pkeyBits skeyBits ->
	sLen:U32.t{v sLen + v hLen + 8 < pow2 32 /\ v (blocks modBits 8ul) - v sLen - v hLen - 3 >= 0 } ->
	salt:lbytes sLen ->
	msgLen:U32.t -> msg:lbytes msgLen ->
	sgnt:lbytes (blocks modBits 8ul) -> Stack unit
	(requires (fun h -> True))
	(ensures (fun h0 _ h1 -> True))

let rsa_sign modBits pkeyBits skeyBits skey sLen salt msgLen msg sgnt =
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
	modBits:U32.t{v modBits > 0} ->
	pkeyBits:U32.t{v pkeyBits <= v modBits} ->
	pkey:rsa_pubkey modBits pkeyBits ->
	sLen:U32.t{v sLen + v hLen + 8 < pow2 32} ->
	sgnt:lbytes (blocks modBits 8ul) ->
	msgLen:U32.t -> msg:lbytes msgLen -> Stack bool
	(requires (fun h -> True))
	(ensures (fun h0 _ h1 -> True))

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