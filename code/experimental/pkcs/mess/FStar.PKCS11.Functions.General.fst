module Hacl.PKCS11.Functions.General


open FStar.PKCS11.Exception
open FStar.PKCS11.Session
open FStar.PKCS11.Mechanism
open FStar.PKCS11.TypeDeclaration
open FStar.PKCS11.Attribute
open FStar.PKCS11.Parse

open FStar.Seq
open FStar.Option

let result = FStar.PKCS11.Exception.result

val createFunctionCheck: pTemplate: attributes_t ->pMechanism: mechanism ->  Tot (result bool)

let createFunctionCheck pTemplate pMechanism= 
	let a = atrributesAllValid pTemplate &&
		attributesForAllNotReadOnly pTemplate && 
		attributesSufficient pTemplate pMechanism  in 
	if a then 
		Inl true
	else
		Inr (O (CKR_ATTRIBUTE_TYPE_INVALID)) 

assume val generateKey: hSession: session -> pMechanism: mechanism -> 
		pTemplate: attributes_t -> ulCount: nat{Seq.length pTemplate = ulCount} -> 
		key: key_t -> Tot(result key_t)

val generateKeyRaw: hSession: session -> pMechanism: mechanism -> pTemplate: list (attribute_raw) ->
	ulCount: nat{Seq.length pTemplate = ulCount} -> key: key_t -> Tot(result key_t)

let generateKeyRaw hSession pMechanism pTemplate ulCount key = 
	let pTemplate = parseAttributes pTemplate in 
	if resultIsOk pTemplate then 
		let pTemplate = resultLeft pTemplate in 	
		generateKey hSession pMechanism pTemplate ulCount key
	else
		Inr TestExc	


(*)
let generateKey hSession pMechanism pTemplate ulCount key = 
	let a = createFunctionCheck pTemplate in 
		if not(resultIsOk a) then 
			Inr (resultRight a)
		else 
		(	





	let funcClass = (function | Class domain_parameters _ -> true | Class secret_key _ -> true | _ -> false) in 
	let classAttr = find_l funcClass pTemplate in 

	let k1 = attributesGetAttributeKey pTemplate in 
	let k2 = mechanismGetParametersKey pMechanism in 
	if isNone k1 then  Inl key else if (isNone k2 || (isSome k2 &&  k1 = k2)) then Inl key
		else Inl key	
	)



	