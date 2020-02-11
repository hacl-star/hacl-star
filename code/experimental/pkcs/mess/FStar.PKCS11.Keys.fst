module FStar.PKCS11.Keys

open FStar.Seq
open FStar.PKCS11.Session
open FStar.PKCS11.Mechanism


let flagLength = 14

let _flag_hw = 0
let _flag_encrypt = 1
let _flag_decrypt = 2
let _flag_digest = 3
let _flag_sign = 4
let _flag_sign_recover = 5
let _flag_verify = 6
let _flag_verify_recover = 7
let _flag_generate =8 
let _flag_generate_key_pair =9 
let _flag_wrap = 10
let _flag_unwrap = 11
let _flag_derive = 12
let _flag_extension = 13

type key_t = |MakeKey: key: seq Fstar.UInt8.t -> flags: flags_t -> attributes: attributes_t -> key_t

val isFlagHW: flags: flags_t -> Tot bool
let isFlagHW flags = 
	(Seq.index flags _flag_hw) = true

val isFlagEncrypt: flags: flags_t -> Tot bool
let isFlagEncrypt flags = 
	(Seq.index flags _flag_encrypt) = true

val isFlagDecrypt: flags: flags_t -> Tot bool
let isFlagDecrypt flags = 
	(Seq.index flags _flag_decrypt) = true

val isFlagDigest: flags: flags_t -> Tot bool
let isFlagDigest flags = 
	(Seq.index flags _flag_digest) = true

val isFlagSign: flags: flags_t -> Tot bool
let isFlagSign flags = 
	(Seq.index flags _flag_sign) = true

val isFlagSignRecover: flags: flags_t -> Tot bool
let isFlagSignRecover flags = 
	(Seq.index flags _flag_sign_recover) = true

val isFlagVerify: flags: flags_t -> Tot bool
let isFlagVerify flags = 
	(Seq.index flags _flag_verify) = true

val isFlagVerifyRecover: flags: flags_t -> Tot bool
let isFlagVerifyRecover flags = 
	(Seq.index flags _flag_verify_recover) = true

val isFlagGenerate: flags: flags_t -> Tot bool
let isFlagGenerate flags = 
	(Seq.index flags _flag_generate) = true

val isFlagGenerateKeyPair: flags: flags_t -> Tot bool
let isFlagGenerateKeyPair flags = 
	(Seq.index flags _flag_generate_key_pair) = true

val isFlagWrap: flags: flags_t -> Tot bool
let isFlagWrap flags = 
	(Seq.index flags _flag_wrap) = true

val isFlagUnwrap: flags: flags_t -> Tot bool
let isFlagUnwrap flags = 
	(Seq.index flags _flag_unwrap) = true

val isFlagDerive: flags: flags_t -> Tot bool
let isFlagDerive flags = 
	(Seq.index flags _flag_derive) = true

val isFlagExtension: flags: flags_t -> Tot bool
let isFlagExtension flags = 
	(Seq.index flags _flag_extension) = true


val isKeyEncrypt: k: key_t -> Tot bool
let isKeyEncrypt k = 
	let (_, flags) = k in 
	isFlagEncrypt flags

val keyLength: k: key_t -> Tot nat
let keyLength k = 
	Seq.length (fst k)



	(* key type check*)
	(* key class check*)
