module PKCS11.Testing.KeyGeneration

open FStar.UInt32
open FStar.Seq
open FStar.Option

open FStar.Seq.Base
open FStar.Seq.Properties

open PKCS11.Spec3_12

(* Test1: 
	Checks: a device without any preconditions
	Expected result: fails 
	Result: fails

	Test2: 
	Checks: totally correct implementation - resulting key
	Expected result: passes
	Result: passes

	Test3: 
	Checks: mechanism is used for signature
	Expected result: fails
	Result: fails

	Test4: 
	Checks: the number of keys were increased by 1
	Expected result: passes
	Result: passes

	Test5: 
	Checks: local attribute for the creates key
	Expected result: passes
	Result: passes

 *)

val test1: d: device -> hSession: _CK_SESSION_HANDLE -> 
	pMechanism: _CK_MECHANISM_TYPE ->
	pTemplate: seq attributeSpecification ->
	Tot (handler: result _CK_OBJECT_HANDLE)


let test1 d hSession pMechanism pTemplate = 
	let x = _CKS_GenerateKey d hSession pMechanism pTemplate in 
	dfst x



val test2: d: device ->  
	hSession: _CK_SESSION_HANDLE -> 
	pMechanism: _CK_MECHANISM_TYPE{isPresentOnDevice d pMechanism /\ 
		(let flags = mechanismGetFlags d pMechanism in isFlagKeyGeneration flags)} ->
	pTemplate: seq attributeSpecification{checkedAttributes pTemplate} ->  
	Tot (handler: result _CK_OBJECT_HANDLE)
	
let test2 d hSession pMechanism pTemplate = 
	let x = _CKS_GenerateKey d hSession pMechanism pTemplate in 
	dfst x



val test3: d: device ->  
	hSession: _CK_SESSION_HANDLE -> 
	pMechanism: _CK_MECHANISM_TYPE{isPresentOnDevice d pMechanism /\ 
		(let flags = mechanismGetFlags d pMechanism in isFlagSign flags)} ->
	pTemplate: seq attributeSpecification{checkedAttributes pTemplate} ->  
	Tot (handler: result _CK_OBJECT_HANDLE)
	
let test3 d hSession pMechanism pTemplate = 
	let x = _CKS_GenerateKey d hSession pMechanism pTemplate in 
	dfst x



val test4: d:  device ->  
	hSession: _CK_SESSION_HANDLE -> 
	pMechanism: _CK_MECHANISM_TYPE{isPresentOnDevice d pMechanism /\ 
		(let flags = mechanismGetFlags d pMechanism in isFlagKeyGeneration flags)} ->
	pTemplate: seq attributeSpecification{checkedAttributes pTemplate} ->  
	Tot unit

let test4 d hSession pMechanism pTemplate = 
	let x = _CKS_GenerateKey d hSession pMechanism pTemplate in 
	let handler = dfst x in 
	let newDevice = dsnd x in 
	assert(Inl? handler ==>  Seq.length newDevice.keys = Seq.length d.keys + 1)



val test5: d:  device ->  
	hSession: _CK_SESSION_HANDLE -> 
	pMechanism: _CK_MECHANISM_TYPE{isPresentOnDevice d pMechanism /\ 
		(let flags = mechanismGetFlags d pMechanism in isFlagKeyGeneration flags)} ->
	pTemplate: seq attributeSpecification{checkedAttributes pTemplate} ->  
	Tot unit

let test5 d hSession pMechanism pTemplate = 
	let x = _CKS_GenerateKey d hSession pMechanism pTemplate in 
	let handler = dfst x in 
	let newDevice = dsnd x in 	
	assert(Inl? handler ==> (let keyCreated = Seq.index newDevice.keys 
		(match handler with Inl a -> a) in
		isAttributeLocal (keyCreated.element).attrs))
