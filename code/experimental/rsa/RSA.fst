module RSA

open FStar.HyperStack.All
open FStar.Buffer
open FStar.Int.Cast
open FStar.All
open FStar.Mul
open C.Loops

open Lib
open Convert
open Exponentiation
open MGF

module U32 = FStar.UInt32
module U8 = FStar.UInt8

#set-options "--lax"

inline_for_extraction let zero_8 = 0uy
inline_for_extraction let hLen = 32ul

noeq type rsa_pubkey =
	| Mk_rsa_pubkey: n:bignum -> e:bignum -> rsa_pubkey

noeq type rsa_privkey =
	| Mk_rsa_privkey: pkey:rsa_pubkey -> d:bignum -> rsa_privkey

val get_length_em: (* consider the case when modBits - 1 is divisible by 8 *)
	modBits:U32.t{U32.v modBits > 0} -> Tot (res:U32.t{U32.v res > 0})
let get_length_em modBits = bits_to_text modBits

val xordb:
	len:U32.t ->
	b1:lbytes len ->
	b2:lbytes len{disjoint b1 b2} -> Stack unit
	(requires (fun h -> live h b1 /\ live h b2))
	(ensures (fun h0 _ h1 -> live h0 b1 /\ live h0 b2 /\ 
		live h1 b1 /\ live h1 b2 /\ modifies_1 b1 h0 h1))

let xordb len b1 b2 =
	C.Loops.in_place_map2 b1 b2 len (fun x y -> U8.(x ^^ y))

val pss_encode:
	saltLen:blen ->
	modBits:U32.t{U32.v modBits > 0 /\ U32.v saltLen + 32 + 2 <= U32.v (get_length_em modBits)} ->
	len:U32.t ->
	salt:lbytes saltLen ->
	msg:uint8_p{length msg = U32.v len /\ length msg < pow2 61 /\ disjoint msg salt} ->
	em:lbytes (get_length_em modBits){disjoint salt em /\ disjoint salt msg} -> Stack unit
	(requires (fun h -> live h msg /\ live h em /\ live h salt))
	(ensures (fun h0 _ h1 -> live h0 msg /\ live h0 em /\  live h0 salt /\ 
		live h1 msg /\ live h1 salt /\ live h1 em /\ modifies_1 em h0 h1))

//#reset-options "--z3rlimit 15"

let pss_encode saltLen modBits len salt msg em =
	push_frame();
	let emLen = get_length_em modBits in
	(**) assert(length em = U32.v emLen);
	(**) assert(U32.v saltLen + 32 + 2 <= U32.v emLen);
	let m1_size = U32.(8ul +^ 32ul +^ saltLen) in
	(**) assert(0 < U32.v emLen - 32 - 1);
	let db_size = U32.(emLen -^ 32ul -^ 1ul) in

	let mHash = create 0uy 32ul in
	let m1 = create 0uy m1_size in
	let m1Hash = create 0uy 32ul in
	let db = create 0uy db_size in
	let dbMask = create 0uy db_size in
	
	hash_sha256 mHash len msg;
	(* first 8 elements should be 0x00 *)
	blit mHash 0ul m1 8ul 32ul;
	blit salt 0ul m1 U32.(8ul +^ 32ul) saltLen;
	hash_sha256 m1Hash m1_size m1;

	(**) assert(0 <= U32.v emLen - (U32.v saltLen) - 32 - 2); 
	let ind_1 = U32.(emLen -^ saltLen -^ 32ul -^ 2ul) in
	(**) assume(U32.v ind_1 < length db);
	db.(ind_1) <- 1uy;
	(**) assume(U32.v ind_1 + 1 < length db);
	(**) assume(U32.v ind_1 + 1 + U32.v saltLen < length db);
	blit salt 0ul db U32.(ind_1 +^ 1ul) saltLen;
	mgf_sha256 m1Hash db_size dbMask;
	
	xordb db_size db dbMask;
	(**) assume(0 < 8 * (U32.v emLen) - (U32.v modBits - 1) /\
		       8 * (U32.v emLen) - (U32.v modBits - 1) < pow2 32);
	let zeroL = U32.(8ul *^ emLen -^ (modBits -^ 1ul)) in
	let db_0 = db.(0ul) in
	(**) assume(U32.v zeroL < pow2 8);
	(**) assert(255 < pow2 8);
	let tmp = U8.(255uy >>^ zeroL) in
	db.(0ul) <- U8.(db_0 &^ tmp);
	blit db 0ul em 0ul db_size;
	blit m1Hash 0ul em db_size hLen;
	upd em U32.(emLen -^ 1ul) 0xbcuy;
	pop_frame()


val pss_verify:
	saltLen:U32.t ->
	modBits:U32.t{U32.v modBits > 0 /\ U32.v saltLen + 32 + 2 <= U32.v (get_length_em modBits)} ->
	len:U32.t ->
	em:lbytes (get_length_em modBits) ->
	msg:uint8_p{length msg = U32.v len /\ length msg < pow2 61 /\ disjoint msg em} -> Stack bool
	(requires (fun h -> live h msg /\ live h em))
	(ensures (fun h0 _ h1 -> live h0 msg /\ live h0 em /\ 
		live h1 msg /\ live h1 em /\ modifies_0 h0 h1))

#reset-options "--z3rlimit 15"

let pss_verify saltLen modBits len em msg =
	push_frame();
	let emLen = get_length_em modBits in
	let m1_size = U32.(8ul +^ 32ul +^ saltLen) in
	let pad_size = U32.(emLen -^ saltLen -^ 32ul -^ 1ul) in
	let db_size = U32.(emLen -^ 32ul -^ 1ul) in

	let mHash = create 0uy 32ul in
	let m1 = create 0uy m1_size in
	let m1Hash' = create 0uy 32ul in
	let pad2 = create 0uy pad_size in
	let dbMask = create 0uy db_size in

	hash_sha256 mHash len msg;
	let res =
		if not (U8.(em.(U32.(emLen -^ 1ul)) =^ 0xbcuy)) then false 
		else begin 
			let maskedDB = sub em 0ul db_size in
			let m1Hash = sub em db_size hLen in
			let zeroL = U32.(8ul *^ emLen -^ (modBits -^ 1ul)) in
			let tmp = U8.(maskedDB.(0ul) &^ (0xffuy <<^ U32.(8ul -^ zeroL))) in
			if not (U8.(tmp =^ 0x00uy)) then false 
			else begin
				mgf_sha256 m1Hash db_size dbMask;
				xordb db_size maskedDB dbMask;
				maskedDB.(0ul) <- U8.(maskedDB.(0ul) &^ (0xffuy >>^ zeroL));
				upd pad2 U32.(pad_size -^ 1ul) 0x01uy;

				let pad = sub maskedDB 0ul pad_size in
				if not (eqb pad pad2 pad_size) then false 
				else begin
					let salt = sub maskedDB pad_size saltLen in
					(* first 8 elements should be 0x00 *)
					blit mHash 0ul m1 8ul hLen;
					blit salt 0ul m1 U32.(8ul +^ hLen) saltLen;
					hash_sha256 m1Hash' m1_size m1;
					eqb m1Hash m1Hash' hLen
					end
				end 
			end in
	pop_frame();
	res

(* ADD disjointness for skey ? *)
val rsa_sign:
	saltLen:U32.t ->
	modBits:U32.t{U32.v saltLen + 32 + 2 <= U32.v (get_length_em modBits)} ->
	skeyBits:U32.t{U32.v skeyBits <= U32.v modBits} -> msgLen:U32.t ->
	msg:uint8_p{length msg = U32.v msgLen /\ length msg < pow2 61} ->
	skey:rsa_privkey ->
	salt:lbytes saltLen{disjoint salt msg} ->
	sgnt:lbytes (bits_to_text modBits){disjoint sgnt msg /\ disjoint sgnt salt} -> Stack unit
	(requires (fun h -> let pkey = Mk_rsa_privkey?.pkey skey in
			live h msg /\ live h salt /\ live h sgnt /\ 
			live h (Mk_rsa_privkey?.d skey) /\ live h (Mk_rsa_pubkey?.n pkey) /\ live h (Mk_rsa_pubkey?.e pkey)))
	(ensures (fun h0 _ h1 ->
			let pkey = Mk_rsa_privkey?.pkey skey in
			live h0 msg /\ live h0 salt /\ live h0 sgnt /\ live h1 msg /\ live h1 salt /\ live h1 sgnt /\
			live h0 (Mk_rsa_privkey?.d skey) /\ live h0 (Mk_rsa_pubkey?.n pkey) /\ live h0 (Mk_rsa_pubkey?.e pkey) /\
			live h1 (Mk_rsa_privkey?.d skey) /\ live h1 (Mk_rsa_pubkey?.n pkey) /\ live h1 (Mk_rsa_pubkey?.e pkey) /\
			modifies_1 sgnt h0 h1))

let rsa_sign saltLen modBits skeyBits msgLen msg skey salt sgnt =
	push_frame();
	let k = bits_to_text modBits in
	let d = Mk_rsa_privkey?.d skey in
	let pkey = Mk_rsa_privkey?.pkey skey in
	let n = Mk_rsa_pubkey?.n pkey in

	let emLen = get_length_em modBits in
	let em = create 0uy emLen in
	pss_encode saltLen modBits msgLen salt msg em;
	let mLen = get_size_nat emLen in
	let m = create 0uL mLen in
	text_to_nat emLen em m;

	(* todo: m % n *)
	let signLen = get_size_nat k in
	let s = create 0uL signLen in
    mod_exp modBits mLen skeyBits signLen n m d s;

	nat_to_text k s sgnt;
	pop_frame()


val rsa_verify:
	saltLen:U32.t ->
	modBits:U32.t{U32.v modBits > 0 /\ U32.v saltLen + 32 + 2 <= U32.v (get_length_em modBits)} ->
	msgLen:U32.t -> pkeyBits:U32.t{U32.v pkeyBits <= U32.v modBits} ->
	sgnt:lbytes (bits_to_text modBits) ->
	pkey:rsa_pubkey ->
	msg:uint8_p{length msg = U32.v msgLen /\ length msg < pow2 61 /\ disjoint msg sgnt} -> Stack bool
	(requires (fun h -> live h msg /\ live h sgnt /\ live h (Mk_rsa_pubkey?.e pkey) /\ live h (Mk_rsa_pubkey?.n pkey)))
	(ensures (fun h0 _ h1 -> live h0 msg /\ live h0 sgnt /\ live h1 msg /\ live h1 sgnt /\
			live h0 (Mk_rsa_pubkey?.e pkey) /\ live h0 (Mk_rsa_pubkey?.n pkey) /\
			live h1 (Mk_rsa_pubkey?.e pkey) /\ live h1 (Mk_rsa_pubkey?.n pkey) /\ 
			modifies_0 h0 h1))

let rsa_verify saltLen modBits msgLen pkeyBits sgnt pkey msg =
	push_frame();
	let e = Mk_rsa_pubkey?.e pkey in
	let n = Mk_rsa_pubkey?.n pkey in

	(* the length of the signature in octets *)
	let k = bits_to_text modBits in
	let signLen = get_size_nat k in
	let s = create 0uL signLen in
	text_to_nat k sgnt s;

	(* todo: s % n *)
	let emLen = get_length_em modBits in
	let mLen = get_size_nat emLen in
	let m = create 0uL mLen in
	mod_exp modBits signLen pkeyBits mLen n s e m;

	let em = create 0uy emLen in
	nat_to_text emLen m em;
	let res = pss_verify saltLen modBits msgLen em msg in
	pop_frame();
	res