module Hacl.Impl.PKCS11.KeyGeneration



(* a key generation function takes a device state
   a session identifier, a template to create attributes and 
   returns a handler and a state of the device
*)




(*
val _CKS_GenerateKey: d: device ->  
	hSession: nat -> 
	pMechanism: _CK_MECHANISM_TYPE{isPresentOnDevice d pMechanism /\ 
		(let flags = mechanismGetFlags d pMechanism in isFlagKeyGeneration flags)} ->
	pTemplate: seq attributeSpecification{checkedAttributes pTemplate} -> 
	Pure(
		(handler: result _CK_OBJECT_HANDLE) & 
		(resultDevice : device {
			if Inr? handler then 
				d = resultDevice else 
			let handler = (match handler with Inl a -> a) in 	
			Seq.length resultDevice.keys = Seq.length d.keys + 1 /\
			handler = Seq.length resultDevice.keys -1 /\
			(
				let newCreatedKey = Seq.index resultDevice.keys handler in 
				isAttributeLocal (newCreatedKey.element).attrs 
			)/\
			modifiesKeysM d resultDevice handler
			}
		) 
	)
	(requires (True))
	(ensures (fun h -> True))

let _CKS_GenerateKey d hSession pMechanism pTemplate = 
	let mechanism = mechanismGetFromDevice d pMechanism in 
	let newKey = keyGeneration mechanism pTemplate in 
	if Inr? newKey then 
		let keyGenerationException = match newKey with Inr a -> a in 
		let keyGenerationException = Inr keyGenerationException in 
		(|keyGenerationException, d|)
	else 
		let key = (match newKey with Inl a -> a) in 
		let (|d, h|) = deviceUpdateKey d key in 
		(|Inl h, d|)
*)
