module PKCS11.Testing.Signature

open FStar.UInt32
open FStar.Seq
open FStar.Option

open PKCS11.Spec3_12
open PKCS11.Spec.Lemmas

open FStar.Seq.Base
open FStar.Seq.Properties

module L = PKCS11.Spec.Lemmas

#set-options "--z3rlimit 300"


(* Test0
	Checks: correct 1-piecec sign
	Expected result: passes
	Result: passes

	Test1: 
	Checks: correct upd-fin sign
	Expected result: passes
	Result: passes

	Test2: 
	Checks: sign without init
	Expected result: fails
	Result: fails

 *)

val test0: d: device -> 
	hSession: _CK_SESSION_HANDLE -> 
	pMechanism: _CK_MECHANISM_TYPE{isPresentOnDevice d pMechanism /\ 
		(let flags = mechanismGetFlags d pMechanism in isFlagSign flags)} ->
	keyHandler: _CK_OBJECT_HANDLE{Seq.length d.keys > keyHandler /\ 
		(let key = Seq.index d.keys keyHandler in 
		let attrKey = (key.element).attrs in
		isAttributeSign attrKey)} -> 
	toSign: seq UInt8.t -> 
	lenToSign: _CK_ULONG{Seq.length toSign = lenToSign} -> 	
	Pure bool
	(requires
		(
			let f = predicateSessionSignature hSession in 
			let openedSessions = d.subSessions in L.count f openedSessions = 0
		)
	)
	(ensures (fun h -> True))

let test0 d hSession pMechanism keyHandler toSign lenToSign = 
	let len = 20 in 
	let signaturePlace = Seq.create len 0uy in 

	let (deviceAfterInit, successful) = signInit d hSession pMechanism keyHandler in 
	if Inr? successful then false
	else
		begin
		let successful = match successful with Inl a -> a in 
			if successful then 
				let r = 
					sign deviceAfterInit hSession toSign lenToSign (Some signaturePlace) len in 
				let deviceAfterSignature = dfst r in 
				let  signature = dsnd r in 
				match signature with 
				|Inr a -> false 
				|Inl v -> let (v, _) = v in 
					match v with 
					| None -> false
					| Some b -> true
		else false
	end	
		

val test1: d: device -> 
	hSession: _CK_SESSION_HANDLE -> 
	pMechanism: _CK_MECHANISM_TYPE{isPresentOnDevice d pMechanism /\ 
		(let flags = mechanismGetFlags d pMechanism in isFlagSign flags)} ->
	keyHandler: _CK_OBJECT_HANDLE{Seq.length d.keys > keyHandler /\ 
		(let key = Seq.index d.keys keyHandler in 
		let attrKey = (key.element).attrs in
		isAttributeSign attrKey)} -> 
	toSign: seq UInt8.t -> 
	lenToSign: _CK_ULONG{Seq.length toSign = lenToSign} -> 	
	Pure bool
	(requires
		(
			let f = predicateSessionSignature hSession in 
			let openedSessions = d.subSessions in L.count f openedSessions = 0
		)
	)
	(ensures (fun h -> True))

let test1 d hSession pMechanism keyHandler toSign lenToSign = 
	let len = 20 in 
	let signaturePlace = Seq.create len 0uy in 

	let (deviceAfterInit, successful) = signInit d hSession pMechanism keyHandler in 
	if Inr? successful then false
	else
		begin
		let successful = match successful with Inl a -> a in 
			if successful then 
				let r = signUpdate deviceAfterInit hSession signaturePlace len in 
				let resultDevice = dfst r in 
				let successful = dsnd r in 
				match successful with 
				|Inr a -> false
				|Inl a -> 
					begin 
						if a then 
							let r = signUpdate resultDevice hSession signaturePlace len in
							let resultDevice = dfst r in 
							let successful = dsnd r in 
							match successful with 
							|Inr a -> false
							|Inl a -> 
								begin
									if a then 
										let r = signFinal resultDevice hSession in true
									else false	
							end	
						else false
					end
			else false		
		end	



val test2: d: device -> 
	hSession: _CK_SESSION_HANDLE -> 
	pMechanism: _CK_MECHANISM_TYPE{isPresentOnDevice d pMechanism /\ 
		(let flags = mechanismGetFlags d pMechanism in isFlagSign flags)} ->
	keyHandler: _CK_OBJECT_HANDLE{Seq.length d.keys > keyHandler /\ 
		(let key = Seq.index d.keys keyHandler in 
		let attrKey = (key.element).attrs in
		isAttributeSign attrKey)} -> 
	toSign: seq UInt8.t -> 
	lenToSign: _CK_ULONG{Seq.length toSign = lenToSign} -> 	
	Pure bool
	(requires
		(
			let f = predicateSessionSignature hSession in 
			let openedSessions = d.subSessions in L.count f openedSessions = 0
		)
	)
	(ensures (fun h -> True))

let test2 d hSession pMechanism keyHandler toSign lenToSign = 
	let len = 20 in 
	let signaturePlace = Seq.create len 0uy in 
	let r = sign d hSession toSign lenToSign (Some signaturePlace) len in 
	let deviceAfterSignature = dfst r in 
	let  signature = dsnd r in 
	match signature with 
		|Inr a -> false 
		|Inl v -> let (v, _) = v in 
			match v with 
			| None -> false
			| Some b -> true
		

		(* upd after final *)
		(* sign after update *)