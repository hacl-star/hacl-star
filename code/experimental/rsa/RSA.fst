module RSA

open FStar.HyperStack
open FStar.ST
open FStar.Buffer
open FStar.Int.Cast
open FStar.All

open BN.Convert

module U32 = FStar.UInt32
module U8 = FStar.UInt8

type uint8_p = buffer FStar.UInt8.t
type bignum = buffer FStar.UInt64.t

type rsa_pubkey = (n:bignum * e:bignum)
type rsa_privkey = (rsa_pubkey * d:bignum)

let zero_8 = 0uy
let zero_64 = 0uL
let hash_size_sha256 = 32ul
let bn_bytes = 8ul

assume val hash_sha256: m: uint8_p -> mHash: uint8_p {length mHash = 32} -> ST unit 
(requires (fun h -> live h m /\ live h mHash))
(ensures (fun h0 _ h1 -> live h0 m /\ live h0 mHash /\ live h1 m /\ live h1 mHash /\ modifies_1 mHash h0 h1))

assume val random_bytes: sLen:U32.t -> s:uint8_p {length s = U32.v sLen} -> ST unit
(requires (fun h -> live h s))
(ensures (fun h0 _ h1 -> live h0 s /\ live h1 s /\ modifies_1 s h0 h1))

val get_octets: (num_bits: U32.t) -> Tot U32.t
let get_octets num_bits = U32.((num_bits +^ 7ul) /^ 8ul)

val maskeddb:
salt: uint8_p ->
em: uint8_p ->
sLen: U32.t {U32.v sLen <= length salt /\ U32.v sLen <= length em} ->
i: U32.t {U32.v i + U32.v sLen <= length em} -> ST unit
(requires (fun h -> live h salt /\ live h em))
(ensures (fun h0 _ h1 -> live h0 salt /\ live h0 em /\ live h1 salt /\ live h1 em /\  modifies_1 em h0 h1))
let rec maskeddb salt em sLen i =
	if U32.(sLen >^ 0ul)
	then (let sLen = U32.(sLen -^ 1ul) in
		 let em_i = U32.(i +^ sLen) in
		 em.(em_i) <- U8.(em.(em_i) ^^ salt.(sLen));
		 maskeddb salt em sLen i)
	else ()

val mgf1: res: uint8_p -> len: U32.t -> seed: uint8_p -> seed_len: U32.t -> i: U32.t -> ST unit
(requires (fun h -> live h res /\ live h seed))
(ensures (fun h0 _ h1 -> live h1 res /\ live h1 seed /\  modifies_1 res h0 h1))
let rec mgf1 res len seed seed_len i =
	let mdLen = hash_size_sha256 in
	if U32.(len >^ 0ul)
	then
		let counter = create zero_8 4ul in
		counter.(0ul) <- uint32_to_uint8 (U32.(i >>^ 24ul));
		counter.(1ul) <- uint32_to_uint8 (U32.(i >>^ 16ul));
		counter.(2ul) <- uint32_to_uint8 (U32.(i >>^ 8ul));
		counter.(3ul) <- uint32_to_uint8 i;
		let ctx = create zero_8 U32.(seed_len +^ 4ul) in
		blit seed 0ul ctx 0ul seed_len;
		blit counter 0ul ctx seed_len 4ul;
		let hash_ctx = create zero_8 hash_size_sha256 in
		hash_sha256 ctx hash_ctx;
		if U32.(mdLen <=^ len)
		then (blit hash_ctx 0ul res U32.(i *^ mdLen) mdLen;
			 mgf1 res U32.(len -^ mdLen) seed seed_len U32.(i +^ 1ul))
		else blit hash_ctx 0ul res U32.(i *^ mdLen) len

val xordb:
db: uint8_p -> 
len: U32.t {U32.v len <= length db} -> 
em: uint8_p -> 
i: U32.t {U32.v i + U32.v len <= length db /\ U32.v i + U32.v len <= length em} -> ST unit
(requires (fun h -> live h db /\ live h em))
(ensures (fun h0 _ h1 -> live h0 db /\ live h0 em /\ live h1 db /\ live h1 em /\  modifies_1 db h0 h1))
let rec xordb db len em i =
	if U32.(len >^ 0ul)
	then
		let len = U32.(len -^ 1ul) in
		let db_i = U32.(i +^ len) in
		db.(db_i) <- U8.(db.(db_i) ^^ em.(db_i));
		xordb db len em i
	else ()

val get_index_01: db: uint8_p -> len: U32.t -> i: U32.t -> ST U32.t
(requires (fun h -> live h db))
(ensures (fun h0 _ h1 -> live h1 db /\ h1 == h0))
let rec get_index_01 db len i =
	if U32.(len >^ 0ul)
	then if U8.(db.(i) =^ zero_8)
		 then get_index_01 db U32.(len -^ 1ul) U32.(i +^ 1ul)
		 else i
	else i

val rsa_padding_add_PKSC1_PSS_mgf1: num_bits: U32.t -> skey: rsa_privkey -> em: uint8_p -> mHash: uint8_p -> ST unit
(requires (fun h -> live h em /\ live h mHash)) (* live h skey *)
(ensures (fun h0 _ h1 -> live h1 em /\ live h1 mHash /\  modifies_1 em h0 h1))
let rsa_padding_add_PKSC1_PSS_mgf1 num_bits skey em mHash =
	(* if n = 0 then error *)
	let hLen = hash_size_sha256 in
	let msBits = U32.((num_bits -^ 1ul) &^ 7ul) in
	let emLen = get_octets num_bits in
	let emLen = if U32.(msBits =^ 0ul) then U32.(emLen -^ 1ul) else emLen in
	let em = if U32.(msBits =^ 0ul) then offset em 1ul else em in
	(* if U32.(emLen <^ hLen +^ 2ul) then failwith "message too long"; *)
	let sLen = U32.(emLen -^ hLen -^ 2ul) in
	let salt = create zero_8 sLen in
	if U32.(sLen >^ 0ul) then random_bytes sLen salt;
	
	let size_m1 = U32.(8ul +^ hLen +^ sLen) in
	let m1 = create zero_8 size_m1 in
	(* first 8 elements should be 0x00 *)
	blit mHash 0ul m1 8ul hLen;
	if U32.(sLen >^ 0ul)
	then blit salt 0ul m1 U32.(8ul +^ hLen) sLen;
	let hash_m1 = create zero_8 hash_size_sha256 in
	hash_sha256 m1 hash_m1;
	
	let maskedDBLen = U32.(emLen -^ hLen -^ 1ul) in
	blit hash_m1 0ul em maskedDBLen hLen;
	mgf1 em maskedDBLen hash_m1 hLen 0ul;

	let i1 = U32.(emLen -^ sLen -^ hLen -^ 2ul) in
	em.(i1) <- U8.(em.(i1) ^^ 1uy);
	if U32.(sLen >^ 0ul) then maskeddb salt em sLen U32.(i1 +^ 1ul);

	if U32.(msBits >^ 0ul)
	then em.(0ul) <- U8.(em.(0ul) &^ (0xffuy >>^ U32.(8ul -^ msBits)));
	
	upd em U32.(emLen -^ 1ul) 0xbcuy

assume val rsa_sign_raw: num_bits:U32.t -> skey: rsa_privkey -> em: uint8_p -> result: uint8_p -> ST unit
(requires (fun h -> live h em /\ live h result)) (* live h skey *)
(ensures (fun h0 _ h1 -> live h1 em /\ live h1 result /\  modifies_1 result h0 h1))
(*
let rsa_sign_raw num_bits skey em result =
	(* not (is_zero mod) *)
	(* is_odd mod *)
	(* not (is_negative mod) *)
	let n = fst (fst skey) in
	let e = fst (snd skey) in
	let d = snd skey in
	let len = get_octets num_bits in
	
	let f_size = U32.((len -^ 1ul) /^ bn_bytes +^ 1ul) in
	let f = create zero_64 f_size in
	bn_bin2bn em len f;
	
	let n0 = bn_mont_n0 n in
	let lgBigR = U32.(num_bits +^ (bn_bits2 -^ 1ul)) /^ bn_bits2 *^ bn_bits2 in
	let rr = create zero_64 len in
	bn_mod_exp_base_2 num_bits rr (U32.(lgBigR *^ 2)) n;
	let mont = Mk_mont_n n rr n0 in
	
	let b_a = create zero_64 len in
	let b_ai = create zero_64 len in
	let b = Mk_blinding_t b_a b_ai in
	
	bn_blinding_create_param b e mont;
	bn_mod_mul_montgomery f b_a mont;
	let result = create zero_64 len in
	bn_mod_exp_mont_consttime result f d n mont;
	
	(* VERIFY the result to protect against fault attacks
	let vrfy = create zero_64 len in
	bn_mod_exp_mont vrfy result e n mont_n;
	if not (eqb vrfy result) then failwith "error" *)
	
	bn_blinding_invert result b mont;
	
	bn_bn2bin_padded len out result
*)

val rsa_sha256_sign: num_bits:U32.t -> result: uint8_p{length result = U32.v (get_octets num_bits)} -> skey: rsa_privkey -> msg: uint8_p -> ST unit
(requires (fun h -> live h result /\ live h msg))  (* live h skey *)
(ensures (fun h0 _ h1 -> live h1 result /\ live h1 msg /\  modifies_1 result h0 h1))
let rsa_sha256_sign num_bits result skey msg =
	let mHash = create zero_8 hash_size_sha256 in
	hash_sha256 msg mHash;
	let size = get_octets num_bits in
	let em = create zero_8 size in
	rsa_padding_add_PKSC1_PSS_mgf1 num_bits skey em mHash; (* mHash -> em, |em| = k \/ |em| = k - 1 *)
	rsa_sign_raw num_bits skey em result (* |result| = k *)

assume val rsa_verify_raw: num_bits:U32.t -> pkey: rsa_pubkey -> sig: uint8_p -> em: uint8_p -> ST unit
(requires (fun h -> live h sig /\ live h em))
(ensures (fun h0 _ h1 -> live h1 sig /\ live h1 em))
(*
let rsa_verify_raw num_bits pkey sig em = 
	let len = get_octets num_bits in
	let n = fst pkey in
	let e = snd pkey in
	
	(* let cond = check_modulus_and_exponent_sizes n in *)
	
	let f_size = U32.((len -^ 1ul) /^ bn_bytes +^ 1ul) in
	let f = create zero_64 f_size in
	bn_bin2bn sig len f;
	
	let n0 = bn_mont_n0 n in
	let lgBigR = U32.(num_bits +^ (bn_bits2 -^ 1ul)) /^ bn_bits2 *^ bn_bits2 in
	let rr = create zero_64 len in
	bn_mod_exp_base_2 num_bits rr (U32.(lgBigR *^ 2)) n;
	let mont = Mk_mont_n n rr n0 in
	
	let result = create zero_64 len in
	bn_mod_exp_mont result f e n mont;
	
	bn_bn2bin_padded len em result
*)

val rsa_verify_PKCS1_PSS_mgf1: num_bits:U32.t -> pkey: rsa_pubkey -> em: uint8_p -> mHash: uint8_p -> ST bool
(requires (fun h -> live h em /\ live h mHash))
(ensures (fun h0 _ h1 -> live h1 em /\ live h1 mHash))
let rsa_verify_PKCS1_PSS_mgf1 num_bits pkey em mHash =
	let hLen = hash_size_sha256 in
	let msBits = U32.((num_bits -^ 1ul) &^ 7ul) in
	let emLen = get_octets num_bits in
	if U8.((em.(0ul) &^ (0xffuy <<^ msBits)) >^ 0uy) then false else
	let emLen = if U32.(msBits =^ 0ul) then U32.(emLen -^ 1ul) else emLen in
	let em = if U32.(msBits =^ 0ul) then offset em 1ul else em in
	(* error if emLen < hLen *)
	let i = U32.(emLen -^ 1ul) in
	if not (U8.(em.(i) =^ 0xbcuy)) then false else
	let maskedDBLen = U32.(emLen -^ hLen -^ 1ul) in
	let h = sub em maskedDBLen hLen in
	let db = create zero_8 maskedDBLen in
	mgf1 db maskedDBLen h hLen 0ul;
	xordb db maskedDBLen em 0ul;
	if U32.(msBits >^0ul) then db.(0ul) <- U8.(db.(0ul) &^ (0xffuy >>^ U32.(8ul -^ msBits)));
	let i = get_index_01 db maskedDBLen 0ul in (* i <= maskedDBLen *)
	if not (U8.(db.(i) =^ 1uy)) then false else 
	let sLen = U32.(maskedDBLen -^ i) in
	let salt = sub db sLen U32.(i +^ 1ul) in
	let h_size = U32.(8ul +^ hLen +^ sLen) in
	let h_ = create zero_8 h_size in
	blit mHash 0ul h_ 8ul hLen;
	if U32.(sLen >^ 0ul) then blit salt 0ul h_ U32.(8ul +^ hLen) sLen;
	let h_hash = create zero_8 hash_size_sha256 in
	hash_sha256 h_ h_hash;
	eqb h_hash h hLen

val rsa_sha256_verify: num_bits:U32.t -> sig: uint8_p {length sig = U32.v (get_octets num_bits)} -> pkey: rsa_pubkey -> msg: uint8_p -> ST bool
(requires (fun h -> live h sig /\ live h msg))
(ensures (fun h0 _ h1 -> live h1 sig /\ live h1 msg))
let rsa_sha256_verify num_bits sig pkey msg =
	let size = get_octets num_bits in
	let em = create zero_8 size in
	rsa_verify_raw num_bits pkey sig em;
	let mHash = create zero_8 hash_size_sha256 in
	hash_sha256 msg mHash;
	rsa_verify_PKCS1_PSS_mgf1 num_bits pkey em mHash