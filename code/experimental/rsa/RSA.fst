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
	saltLen:U32.t ->
	modBits:U32.t{U32.v (get_length_em modBits) >= U32.(v (saltLen +^ hLen +^ 2ul))} ->
	msg:uint8_p -> len:U32.t{U32.v len = length msg} ->
	salt:uint8_p{length salt = U32.v saltLen} ->
	em:uint8_p{length em = U32.v (get_length_em modBits)} -> Stack unit
	(requires (fun h -> live h msg /\ live h em /\ live h salt))
	(ensures (fun h0 _ h1 -> live h0 msg /\ live h0 em /\  live h0 salt /\ live h1 em /\ modifies_1 em h0 h1))
let pss_encode saltLen modBits msg len salt em =
	push_frame();
	let mHash = create zero_8 hLen in
	hash_sha256 mHash len msg;
	let emBits = U32.(modBits -^ 1ul) in
	let emLen = get_length_em modBits in
	let m1_size = U32.(8ul +^ hLen +^ saltLen) in
	let m1 = create zero_8 m1_size in
	(* first 8 elements should be 0x00 *)
	blit mHash 0ul m1 8ul hLen;
	blit salt 0ul m1 U32.(8ul +^ hLen) saltLen;
	let m1Hash = create zero_8 hLen in
	hash_sha256 m1Hash m1_size m1;

	let db_size = U32.(emLen -^ hLen -^ 1ul) in
	let db = create zero_8 db_size in
	let ind_1 = U32.(emLen -^ saltLen -^ hLen -^ 2ul) in
	db.(ind_1) <- 1uy;
	blit salt 0ul db U32.(ind_1 +^ 1ul) saltLen;

	let dbMask = create zero_8 db_size in
	mgf_sha256 m1Hash db_size dbMask;

	xordb db_size db dbMask;
	let zeroL = U32.(8ul *^ emLen -^ emBits) in
	db.(0ul) <- U8.(db.(0ul) &^ (0xffuy >>^ zeroL));

	blit db 0ul em 0ul db_size;
	blit m1Hash 0ul em db_size hLen;
	upd em U32.(emLen -^ 1ul) 0xbcuy;
	pop_frame()

val pss_verify:
	saltLen:U32.t ->
	modBits:U32.t{U32.v (get_length_em modBits) >= U32.(v (saltLen +^ hLen +^ 2ul))} ->
	em:uint8_p{length em = U32.v (get_length_em modBits)} ->
	msg:uint8_p -> len:U32.t{U32.v len = length msg} -> Stack bool
	(requires (fun h -> live h msg /\ live h em))
	(ensures (fun h0 _ h1 -> live h0 msg /\ live h0 em /\ live h1 msg /\ live h1 em))
let pss_verify saltLen modBits em msg len =
	push_frame();
	let emLen = get_length_em modBits in
	let m1_size = U32.(8ul +^ hLen +^ saltLen) in
	let pad_size = U32.(emLen -^ saltLen -^ hLen -^ 1ul) in
	let db_size = U32.(emLen -^ hLen -^ 1ul) in

	let mHash = create zero_8 hLen in
	let m1Hash' = create zero_8 hLen in
	let m1 = create zero_8 m1_size in
	let pad2 = create zero_8 pad_size in
	let dbMask = create zero_8 db_size in

	hash_sha256 mHash len msg;
	let res =
	if not (U8.(em.(U32.(emLen -^ 1ul)) =^ 0xbcuy)) then false else (
	let maskedDB = sub em 0ul db_size in
	let m1Hash = sub em db_size hLen in
	let zeroL = U32.(8ul *^ emLen -^ (modBits -^ 1ul)) in
	let tmp = U8.(maskedDB.(0ul) &^ (0xffuy <<^ U32.(8ul -^ zeroL))) in
	if not (U8.(tmp =^ 0x00uy)) then false else (
	mgf_sha256 m1Hash db_size dbMask;
	xordb db_size maskedDB dbMask;
	maskedDB.(0ul) <- U8.(maskedDB.(0ul) &^ (0xffuy >>^ zeroL));
	upd pad2 U32.(pad_size -^ 1ul) 0x01uy;

	let pad = sub maskedDB 0ul pad_size in
	if not (eqb pad pad2 pad_size) then false else (
	let salt = sub maskedDB pad_size saltLen in
	(* first 8 elements should be 0x00 *)
	blit mHash 0ul m1 8ul hLen;
	blit salt 0ul m1 U32.(8ul +^ hLen) saltLen;
	hash_sha256 m1Hash' m1_size m1;
	eqb m1Hash m1Hash' hLen))) in
	pop_frame();
	res

val rsa_sign:
	saltLen:U32.t ->
	modBits:U32.t{U32.v (get_length_em modBits) >= U32.(v (saltLen +^ hLen +^ 2ul))} ->
	skeyBits:U32.t -> msgLen:U32.t ->
	msg:uint8_p{length msg = U32.v msgLen} ->
	skey:rsa_privkey ->
	salt:uint8_p{length salt = U32.v saltLen} ->
	sgnt:uint8_p{length sgnt = U32.v (bits_to_text modBits)} -> Stack unit
	(requires (fun h -> live h msg /\ live h salt /\ live h sgnt))
	(ensures (fun h0 _ h1 -> live h0 msg /\ live h0 salt /\ live h0 sgnt /\ live h1 sgnt /\ modifies_1 sgnt h0 h1))
let rsa_sign saltLen modBits skeyBits msgLen msg skey salt sgnt =
	push_frame();
	let k = bits_to_text modBits in
	let d = Mk_rsa_privkey?.d skey in
	let pkey = Mk_rsa_privkey?.pkey skey in
	let n = Mk_rsa_pubkey?.n pkey in

	let emLen = get_length_em modBits in
	let em = create zero_8 emLen in
	pss_encode saltLen modBits msg msgLen salt em;
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
	modBits:U32.t{U32.v (get_length_em modBits) >= U32.(v (saltLen +^ hLen +^ 2ul))} ->
	msgLen:U32.t -> pkeyBits:U32.t ->
	sgnt:uint8_p{length sgnt = U32.v (bits_to_text modBits)} ->
	pkey:rsa_pubkey ->
	msg:uint8_p{length msg = U32.v msgLen} -> Stack bool
	(requires (fun h -> live h msg /\ live h sgnt))
	(ensures (fun h0 _ h1 -> live h0 msg /\ live h0 sgnt /\ live h1 msg /\ live h1 sgnt))
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

	let em = create zero_8 emLen in
	nat_to_text emLen m em;
	let res = pss_verify saltLen modBits em msg msgLen in
	pop_frame();
	res