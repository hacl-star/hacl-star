module Hacl.PKCS11.Encryption

open FStar.Seq

open FStar.PKCS11.Keys
open FStar.PKCS11.Session
open FStar.PKCS11.Mechanism
open FStar.PKCS11.Exception

type encrypted_t = (enc: seq nat) & (lengthEnc: nat {Seq.length enc = lengthEnc})

assume val encryptInit: k: key_t{isKeyEncrypt k} -> s: session -> cipher: mechanism-> Tot unit


assume val encrypt: s: session ->
 			pData: seq nat ->
 			pDataLen: nat {pDataLen = Seq.length pData} -> 
 			Tot (tuple2 result (option encrypted_t))

assume val encryptUpd: s: session -> 
 			pData: seq nat ->
 			pDataLen: nat {pDataLen = Seq.length pData} -> 
 			Tot (tuple2 result (option encrypted_t))		

assume val encryptFin: nat -> Tot (tuple2  result (option encrypted_t))			

let testExc = Inr (TestExc)


val encryptMain: k: key_t -> s: session ->cipher: mechanism -> pData: seq nat -> pDataLen: nat {pDataLen = Seq.length pData} ->
					  Tot (tuple2 result (option encrypted_t))

let encryptMain k s cipher pData pDataLen =
	let a = isKeyEncrypt k && mechanismRequiredKeyLength cipher (keyLength k) in 
	if a then 
		(
			encryptInit k s cipher;

			let (result, encrypted) = encrypt s pData pDataLen in 
			if (resultIsOk result) 
				then 
					encryptFin 0
				else
					(result, None)
		)
	else (testExc,  None)

	
