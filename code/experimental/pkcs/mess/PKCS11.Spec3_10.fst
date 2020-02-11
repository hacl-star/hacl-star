module PKCS11.Spec3_10

open FStar.UInt32
open FStar.Seq
open FStar.Option

open FStar.Seq.Base
open FStar.Seq.Properties

open PKCS11.Spec.Lemmas

(* #set-options "--z3rlimit 200 --lax"  *)

#set-options "--z3rlimit 300"

type _CK_MECHANISM_TYPE = nat

type _CK_ULONG = nat

type _CK_ATTRIBUTE_TYPE = FStar.UInt32.t

type _CK_OBJECT_CLASS = _CK_ULONG

type _CK_KEY_TYPE_T = _CK_ULONG

type _CK_OBJECT_HANDLE = _CK_ULONG

type _CK_EXCEPTION = _CK_ULONG

type _CK_FLAGS_T = _CK_ULONG
type _CK_SESSION_HANDLE = _CK_ULONG

type _CKS_MECHANISM_INFO = 
	| MecInfo: flags: seq _CK_ULONG -> _CKS_MECHANISM_INFO	

let _CKO_SECRET_KEY = 4


type attributeSpecification  = 
	| CKA_CLASS: typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x0ul} -> pValue: seq _CK_OBJECT_CLASS{length pValue = 1} ->  attributeSpecification
	| CKA_TOKEN: typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x1ul}->  pValue: seq bool-> attributeSpecification
	| CKA_PRIVATE: typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x2ul} ->  pValue: seq bool-> attributeSpecification
	| CKA_LABEL: typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x3ul} ->  pValue: seq _CK_ULONG->a: attributeSpecification
	| CKA_APPLICATION:typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x10ul} ->pValue: seq _CK_ULONG ->a: attributeSpecification
	| CKA_VALUE:typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x11ul} ->pValue: seq _CK_ULONG ->a: attributeSpecification
	| CKA_OBJECT_ID:typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x12ul} -> pValue: seq _CK_ULONG ->a: attributeSpecification
	| CKA_CERTIFICATE_TYPE:typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x80ul} -> pValue: seq _CK_ULONG ->a: attributeSpecification
	| CKA_ISSUER:typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x81ul} ->pValue: seq _CK_ULONG ->a: attributeSpecification
	| CKA_SERIAL_NUMBER: typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x82ul}-> pValue: seq _CK_ULONG ->a: attributeSpecification
	| CKA_KEY_TYPE: typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x100ul} -> pValue: seq _CK_KEY_TYPE_T-> attributeSpecification
	| CKA_ID: typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x102ul} -> pValue: seq _CK_ULONG->a: attributeSpecification
	| CKA_SENSITIVE: typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x103ul} ->pValue: seq bool -> attributeSpecification
	| CKA_ENCRYPT: typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x104ul} ->pValue: (seq bool) ->a: attributeSpecification
	| CKA_DECRYPT: typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x105ul}->pValue: seq bool ->a: attributeSpecification
	| CKA_WRAP: typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x106ul} -> pValue: seq _CK_ULONG ->a: attributeSpecification
	| CKA_UNWRAP: typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x107ul} -> pValue: seq _CK_ULONG->a: attributeSpecification
	| CKA_SIGN: typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x108ul} -> pValue: seq _CK_ULONG ->a: attributeSpecification
	| CKA_VERIFY: typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x10Aul} -> pValue: seq _CK_ULONG ->a: attributeSpecification
	| CKA_VALUE_LEN: typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x161ul} -> pValue: seq _CK_ULONG -> attributeSpecification
	| CKA_STUB: typeId: _CK_ATTRIBUTE_TYPE{typeId = 0x999ul} -> pValue: seq bool{length pValue = 1} -> attributeSpecification


type _object = 
	|O: 
		identifier: _CK_ULONG -> 
		dat: seq FStar.UInt8.t -> 
		attrs: seq attributeSpecification -> 
		_object

val classAttribute : a: _object -> Tot (a: option attributeSpecification{Some? a  ==> (let a = (match a with Some a -> a) in  CKA_CLASS? a)}) 		

let classAttribute a = 
	let attrs = a.attrs in 
	find_l (fun x -> CKA_CLASS? x) attrs

type keyEntity = 
	|Key: element: _object{
		(let attrs = classAttribute element in Some? attrs
			&& 
			(let a = (match attrs with Some a -> a) in 
				let value = Seq.index (CKA_CLASS?.pValue a) 0 in value = _CKO_SECRET_KEY
		)
	)} -> keyEntity


type temporalStorage = 
	|Element: dat: seq FStar.UInt8.t * _CK_ULONG -> temporalStorage



type mechanismSpecification = 
	| Mechanism: mechanismID: _CK_MECHANISM_TYPE -> 
		pParameters: seq FStar.UInt8.t -> 
		mechanismSpecification

let _SubSessionInit = 0
let _SubSessionUpd = 1

let _SubSessionVerifyInit = 0
let _SubSessionUpdInit = 1

type subSession (k: seq keyEntity) (m: seq mechanismSpecification) = 
	|Signature: id: _CK_SESSION_HANDLE -> 
		state: _CK_ULONG{state = _SubSessionInit \/ state = _SubSessionUpd} ->
		pMechanism: _CK_MECHANISM_TYPE(*{isPresentOnDevice d pMechanism}*) ->
		keyHandler: _CK_OBJECT_HANDLE-> 
		temp: option temporalStorage -> 
		subSession k m
	|Verify : 	id: _CK_SESSION_HANDLE -> 
		state: _CK_ULONG{state = _SubSessionVerifyInit \/ state = _SubSessionUpdInit} ->
		pMechanism: _CK_MECHANISM_TYPE(*{isPresentOnDevice d pMechanism}*) ->
		keyHandler: _CK_OBJECT_HANDLE-> 
		temp: option temporalStorage -> 
		subSession k m

val subSessionGetID: #ks: seq keyEntity -> #ms: seq mechanismSpecification -> s: subSession ks ms -> Tot _CK_SESSION_HANDLE

let subSessionGetID #ks #ms s = 
	match s with 
	|Signature a _ _ _ _ -> a 
	|Verify a _ _ _  _  -> a

val subSessionGetState: #ks: seq keyEntity -> #ms : seq mechanismSpecification -> s: subSession ks ms -> Tot _CK_ULONG

let subSessionGetState #ks #ms s = 
	match s with
	| Signature _ b _ _ _ -> b
	| Verify _ b _ _ _  -> b

val subSessionSetState: #ks: seq keyEntity -> #ms: seq mechanismSpecification -> s: subSession ks ms -> state : _CK_ULONG 
	{if Signature? s then state =  _SubSessionInit \/ state = _SubSessionUpd else 
		state = _SubSessionVerifyInit \/ state = _SubSessionUpdInit} -> 
		Tot (r: subSession ks ms{subSessionGetState r = state /\ 
			(if Signature? s then Signature? r else Verify? r ) /\
			(match s with 
				|Signature a _ c d e ->
					begin match r with 
						|Signature a1 _ c1 d1 e1 -> a = a1 /\ c = c1 /\ d = d1 /\ e = e1
					end	
				|Verify a _ c d e ->
					begin match r with 
						|Verify a1 _ c1 d1 e1 -> a = a1 /\ c = c1 /\ d = d1 /\ e = e1
					end	
			)
		})

let subSessionSetState #ks #ms s state = 
	match s with 
	|Signature a b c d e -> Signature a state c d e 
	|Verify a b c d e -> Verify a state c d e		

val subSessionGetStorage: #ks: seq keyEntity -> #ms : seq mechanismSpecification -> s: subSession ks ms -> Tot (option temporalStorage)

let subSessionGetStorage #ks #ms s = 
	match s with 
	|Signature _ _ _ _ e -> e 
	|Verify _ _ _ _ e -> e

val subSessionSetStorage: #ks: seq keyEntity -> #ms: seq mechanismSpecification -> s: subSession ks ms -> storage: option temporalStorage -> 
	Tot (r: subSession ks ms {subSessionGetStorage r = storage /\
		(if Signature? s then Signature? r else Verify? r) /\
		(match s with 
				|Signature a _ c d e ->
					begin match r with 
						|Signature a1 _ c1 d1 e1 -> a = a1 /\ c = c1 /\ d = d1 /\ e = e1
					end	
				|Verify a _ c d e ->
					begin match r with 
						|Verify a1 _ c1 d1 e1 -> a = a1 /\ c = c1 /\ d = d1 /\ e = e1
					end)
		}
	)

let subSessionSetStorage #ks #ms s storage = 
	match s with 
	|Signature a b c d e -> Signature a b c d storage
	|Verify a b c d e -> Verify a b c d storage

val subSessionGetMechanism: #ks: seq keyEntity -> #ms: seq mechanismSpecification -> s: subSession ks ms -> Tot _CK_MECHANISM_TYPE

let subSessionGetMechanism #ks #ms s = 
	match s with 
	|Signature _ b _ _ _ -> b 
	|Verify _ b _ _ _ -> b

val subSessionGetKeyHandler: #ks: seq keyEntity -> #ms: seq mechanismSpecification -> s: subSession ks ms -> Tot _CK_OBJECT_HANDLE

let subSessionGetKeyHandler #ks #ms s = 
	match s with 
	|Signature _ _ c _ _ -> c 
	|Verify _ _ c _ _ -> c


type device = 
	|Device: 
		keys: seq keyEntity ->
		mechanisms: seq mechanismSpecification -> 
		objects: seq _object -> 
		subSessions: seq (subSession keys mechanisms) -> 
	device
		

(* Internal data *)
assume val mechanismGetFlags: d: device -> mechanismID: _CK_MECHANISM_TYPE -> Tot _CK_FLAGS_T

assume val isFlagKeyGeneration: flags: _CK_FLAGS_T -> Tot bool

assume val isFlagSign: flags: _CK_FLAGS_T -> Tot bool

assume val isFlagVerify: flags: _CK_FLAGS_T -> Tot bool

assume val isAttributeLocal: attrs: seq attributeSpecification -> Tot bool

assume val isAttributeSecretKey: attrs: seq attributeSpecification -> Tot bool

assume val isAttributeSign: attrs : seq attributeSpecification -> Tot bool

assume val isAttributeVerify: attrs: seq attributeSpecification -> Tot bool


type exception_t = _CK_ULONG 

type result 'a = either 'a exception_t

val isPresentOnDevice: d: device ->  pMechanism: _CK_MECHANISM_TYPE -> Tot bool

let isPresentOnDevice d pMechanism = 
	let mechanisms = d.mechanisms in 
	Some? (find_l (fun x -> x.mechanismID = pMechanism) mechanisms)

val mechanismGetFromDevice: d: device -> pMechanism: _CK_MECHANISM_TYPE{isPresentOnDevice d pMechanism} -> 
	Tot (m: mechanismSpecification{m.mechanismID = pMechanism})

let mechanismGetFromDevice d pMechanism = 
	let mechanisms = d.mechanisms in 
	let m = find_l (fun x -> x.mechanismID = pMechanism) mechanisms in 
	match m with 
	Some m -> m

assume val checkedAttributes: pTemplate : seq attributeSpecification -> Tot bool

assume val keyGeneration: mechanismID: mechanismSpecification -> pTemplate: seq attributeSpecification ->
	Tot (either (k: keyEntity {let attrs = (k.element).attrs in isAttributeLocal attrs &&  
		isAttributeSecretKey attrs}) exception_t)


val sessionEqual: #ks: seq keyEntity -> #ms: seq mechanismSpecification -> #ks1: seq keyEntity -> #ms1 : seq mechanismSpecification -> 
	s: subSession ks ms -> s1 : subSession ks1 ms1 -> Tot bool

let sessionEqual #ks #ms #ks1 #ms1 s s1 = 
	match s with 
	|Signature a b c d e -> 
		begin match s1 with 
			|Signature a1 b1 c1 d1 e1 -> a = a1 && b = b1 && c = c1 && d = d1 && e = e1
			| _ -> false
		end
	|Verify a b c d e -> 	
		begin 
			match s1 with
			| Verify a1 b1 c1 d1 e1 -> a = a1 && b = b1 && c = c1 && d = d1 && e = e1
			| _ -> false
		end		




val sessionsEqual: #ks: seq keyEntity -> #ms: seq mechanismSpecification -> #ks1: seq keyEntity -> #ms1: seq mechanismSpecification -> 
	s: seq (subSession ks ms) -> s1: seq (subSession ks1 ms1){Seq.length s = Seq.length s1} -> Tot bool

let sessionsEqual #ks #ms #ks1 #ms1 s s1 = 
	for_all2 sessionEqual s s1  	

val lemma_for_all2: #ks:  seq keyEntity -> #ms: seq mechanismSpecification -> #ks1: seq keyEntity -> #ms1: seq mechanismSpecification -> 
	s: seq (subSession ks ms) -> s1: seq (subSession ks1 ms1){Seq.length s = Seq.length s1} ->
	Lemma (requires (forall (i: nat{i < Seq.length s}). sessionEqual (index s i) (index s1 i)))
	(ensures (for_all2 #(subSession ks ms) #(subSession ks1 ms1) sessionEqual s s1))
	(decreases (Seq.length s))

let rec lemma_for_all2 #ks #ms #ks1 #ms1 s s1 = 
	if length s = 0 then () else
	let el1 = head s in 
	let el2 = head s1 in 
		assert(sessionEqual el1 el2);
		lemma_for_all2 (tail s) (tail s1)	




val updateSession_: d: device -> s: subSession d.keys d.mechanisms -> ks: seq keyEntity -> 
	ms: seq mechanismSpecification -> Pure (r: subSession ks ms
		{Signature? s ==> Signature? r /\ Verify? s ==> Verify? r /\ sessionEqual s r}
	) 
	(requires True)
	(ensures (fun h -> True))

let updateSession_ d s ks ms = 
	match s with 
	| Signature a b c d e -> 
		let (a: subSession ks ms) = Signature a b c d e in a
	| Verify a b c d e -> 
		let (a: subSession ks ms) = Verify a b c d e in a

val updateSession: d: device ->  s: seq (subSession d.keys d.mechanisms) -> ks: seq keyEntity -> ms: seq mechanismSpecification -> 
	Pure (snew: seq (subSession ks ms){Seq.length s = Seq.length snew})
		(requires True)
		(ensures (fun h -> let snew = h in forall (i: nat{i < Seq.length s}) . sessionEqual (index s i) (index snew i) /\ sessionsEqual s snew ))

let updateSession d s ks ms = 
	let snew =  map (fun x -> updateSession_ d x ks ms) s in 
		assert(forall (i: nat{i < Seq.length snew}). sessionEqual (index s i) (index snew i));
		lemma_for_all2 s snew;
	snew

(* Modifies Section*)
val modifiesKeysM: dBefore: device -> dAfter: device{Seq.length dBefore.keys + 1 = Seq.length dAfter.keys /\ Seq.length dBefore.subSessions = Seq.length dAfter.subSessions} -> 
	i: _CK_OBJECT_HANDLE{i < Seq.length dAfter.keys} -> Tot bool

let modifiesKeysM dBefore dAfter i = 
	let mechanismsPrevious, keysPrevious, objectsPrevious = dBefore.mechanisms, dBefore.keys, dBefore.objects in 
	let mechanismsNew, keysNew, objectsNew = dAfter.mechanisms, dAfter.keys, dAfter.objects in 
	let keysBeforeA, keysBeforeB = Seq.split dBefore.keys i in 
	let keysAfterA, key_keysAfterB = Seq.split dAfter.keys i in 	
	let key, keysAfterB = Seq.split key_keysAfterB 1 in 
	mechanismsPrevious = mechanismsNew &&
	keysBeforeA = keysAfterA && keysBeforeB = keysAfterB &&
	objectsPrevious = objectsNew && sessionsEqual dBefore.subSessions dAfter.subSessions  



val modifiesSessionsM: dBefore: device -> dAfter : device{Seq.length dBefore.subSessions = Seq.length dAfter.subSessions + 1} -> 
	i: nat{i < Seq.length dBefore.subSessions} -> Tot bool

let modifiesSessionsM dBefore dAfter i = 
	let mechanismsPrevious, keysPrevious, objectsPrevious = dBefore.mechanisms, dBefore.keys, dBefore.objects in 
	let mechanismsNew, keysNew, objectsNew = dAfter.mechanisms, dAfter.keys, dAfter.objects in 
	let sessionsBeforeA, session_sessionBeforeB = Seq.split dBefore.subSessions i in 
	let _, sessionsBeforeB = Seq.split session_sessionBeforeB 1 in 
	let sessionsAfterA, sessionsAfterB = Seq.split dAfter.subSessions i in 
	mechanismsPrevious = mechanismsNew &&
	keysPrevious = keysNew && 
	objectsPrevious = objectsNew &&
	sessionsEqual sessionsBeforeA sessionsAfterA &&
	sessionsEqual sessionsBeforeB sessionsAfterB

val modifiesSessionsE: dBefore: device -> dAfter: device{Seq.length dBefore.subSessions = Seq.length dAfter.subSessions} ->
	i: nat {i < Seq.length dBefore.subSessions} -> Tot bool

let modifiesSessionsE dBefore dAfter i = 
	let mechanismsPrevious, keysPrevious, objectsPrevious = dBefore.mechanisms, dBefore.keys, dBefore.objects in 
	let mechanismsNew, keysNew, objectsNew = dAfter.mechanisms, dAfter.keys, dAfter.objects in 
	let sessionsBeforeA, session_sessionBeforeB = Seq.split dBefore.subSessions i in 
	let _, sessionsBeforeB = Seq.split session_sessionBeforeB 1 in 
	let sessionsAfterA, session_sessionAfterB = Seq.split dBefore.subSessions i in 
	let _, sessionsAfterB = Seq.split session_sessionBeforeB 1 in 
	mechanismsPrevious = mechanismsNew &&
	keysPrevious = keysNew && 
	objectsPrevious = objectsNew &&
	sessionsEqual sessionsBeforeA sessionsAfterA &&
	sessionsEqual sessionsBeforeB sessionsAfterB	

(* Predicate Section*)
let predicateSessionVerify hSession = (fun x -> Verify? x /\ subSessionGetID x = hSession)	

let predicateSessionSignature hSession = (fun x -> Signature? x && subSessionGetID x = hSession)



val deviceUpdateKey: d: device -> newKey: keyEntity -> Tot (resultDevice: device
	{
		Seq.length resultDevice.keys = Seq.length d.keys + 1 /\
		Seq.length d.subSessions = Seq.length resultDevice.subSessions
	} &
	(handler: _CK_OBJECT_HANDLE
		{
			handler < Seq.length resultDevice.keys/\ 
			Seq.index resultDevice.keys handler = newKey /\
			modifiesKeysM d resultDevice handler
		}
	))

let deviceUpdateKey d newKey = 
	let mechanismsPrevious = d.mechanisms in 
	let keysPrevious = d.keys in 
	let objectsPrevious = d.objects in 
	let keysNew = Seq.snoc keysPrevious newKey in
	let sessions = d.subSessions in 
	let sessions = updateSession d sessions keysNew mechanismsPrevious in 
	let handler = Seq.length keysNew -1 in 
	let deviceNew = Device keysNew mechanismsPrevious objectsPrevious sessions in 
	(|deviceNew, handler|)
	
val deviceRemoveSession: #ks: seq keyEntity -> #ms: seq mechanismSpecification ->  hSession : _CK_SESSION_HANDLE -> 
	f: (subSession ks ms -> bool) -> 
	d: device{count f d.subSessions = 1} ->
	Tot (resultDevice: device
		{
			None? (find_l f resultDevice.subSessions) /\
			(let indexOfSessionToDelete = find_l f d.subSessions in 
			let indexOfSessionToDelete = seq_getIndex d.subSessions (match indexOfSessionToDelete with Some a -> a) in 
			modifiesSessionsM d resultDevice indexOfSessionToDelete)
		}
	)	

let deviceRemoveSession #ks #ms hSession f d = 
	let mechanismsPrevious = d.mechanisms in 
	let keysPrevious = d.keys in 
	let objectsPrevious = d.objects in 
	let sessionsPrevious = d.subSessions in 
	let sessionsNew = seq_remove sessionsPrevious f in 
	let newDevice = Device keysPrevious mechanismsPrevious objectsPrevious sessionsNew
	in newDevice

(*U: this requires strongly that nothing changed in between *)
val deviceUpdateSessionChangeStatus: #ks: seq keyEntity -> #ms: seq mechanismSpecification -> hSession: _CK_SESSION_HANDLE -> 
	f: (subSession ks ms -> bool) ->   
	d: device{count f d.subSessions = 1} ->
	Tot (resultDevice: device
		{ 
			let session = find_l f resultDevice.subSessions in Some? session /\
			(let s = match session with Some a -> a in subSessionGetState s == _SubSessionUpd) /\
			(let sessionIndex = seq_getIndex d.subSessions (match session with Some a -> a) in 
			modifiesSessionsM d resultDevice sessionIndex)
		}
	)

let deviceUpdateSessionChangeStatus #ks #ms hSession f d = 
	let mechanismsPrevious = d.mechanisms in 
	let keysPrevious = d.keys in 
	let objectsPrevious = d.objects in 
	let sessionsPrevious = d.subSessions in 
	let sessionToChange = find_l f sessionsPrevious in 
	let sessionToChange = match sessionToChange with |Some a -> a in 
	let sessionChanged = subSessionSetState sessionToChange (match sessionToChange with |Signature _ _ _ _ _ ->_SubSessionUpd |Verify _ _ _ _ _  -> _SubSessionUpdInit) in 
	let sessionsNew = seq_remove sessionsPrevious f in 
		(* find_append_some (Seq.create 1 sessionChanged) sessionsNew f; *)
	let sessionsNew = Seq.append (Seq.create 1 sessionChanged) sessionsNew in 	
	let newDevice = Device keysPrevious mechanismsPrevious objectsPrevious sessionsNew in 
	newDevice

val deviceUpdateSessionChangeStorage: #ks: seq keyEntity -> #ms: seq mechanismSpecification -> hSession : _CK_SESSION_HANDLE ->
	f: (subSession ks ms -> Tot bool) ->
	d: device{count f d.subSessions = 1} ->
	storage : temporalStorage ->
	Tot (resultDevice: device
		{
			let session = find_l f resultDevice.subSessions in Some? session /\
			(let s = match session with Some a -> a in subSessionGetStorage s = Some storage) /\
			(let sessionIndex = seq_getIndex d.subSessions (match session with Some a -> a) in 
			modifiesSessionsE d resultDevice sessionIndex)
		}

	)

let deviceUpdateSessionChangeStorage #ks #ms hSession f d storage = 
	let mechanismsPrevious = d.mechanisms in 
	let keysPrevious = d.keys  in 
	let objectsPrevious = d.objects in 
	let sessionsPrevious = d.subSessions in 
	let sessionToChange = find_l f sessionsPrevious in 
	let sessionToChange = match sessionToChange with | Some a -> a in 
	let sessionChanged = subSessionSetStorage sessionToChange (Some storage) in 
	let sessionsNew = seq_remove sessionsPrevious f in 
	let sessionsNew = Seq.append (Seq.create 1 sessionChanged) sessionsNew in 
	let newDevice = Device keysPrevious mechanismsPrevious objectsPrevious sessionsNew in 
	newDevice


val deviceAddSession: #ks: seq keyEntity -> #ms: seq mechanismSpecification -> hSession:_CK_SESSION_HANDLE ->
	f: (subSession ks ms -> Tot bool) -> 
	d: device{count f d.subSessions = 0} -> 
	newSession: subSession d.keys d.mechanisms{subSessionGetID newSession = hSession} -> 
	Tot (resultDevice: device
		{
			count f resultDevice.subSessions = 1 /\
			(
				let session = find_l f resultDevice.subSessions in 
				let sessionIndex = seq_getIndex d.subSessions (match session with Some a -> a) in 
				modifiesSessionsM resultDevice d sessionIndex
			)
		}
	)


let deviceAddSession #ks #ms hSession f d newSession = 
	let mechanismsPrevious = d.mechanisms in 
	let keysPrevious = d.keys in 
	let objectsPrevious = d.objects in 
	let sessions = d.subSessions in 
	let sessions = updateSession d sessions keysPrevious mechanismsPrevious in 
	let newSessionUpd = updateSession_ d newSession d.keys d.mechanisms in 
	let newElement = Seq.create 1 newSessionUpd in 
	let sessions_upd = append sessions newElement in
	let updatedDevice = Device keysPrevious mechanismsPrevious objectsPrevious sessions_upd	in 
	updatedDevice

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




assume val _sign: pData: seq FStar.UInt8.t ->  pMechanism: _CK_MECHANISM_TYPE -> key: _CK_OBJECT_HANDLE -> 
	pSignature: option (seq UInt8.t) ->
	pSignatureLen : _CK_ULONG ->
	Tot (result (seq FStar.UInt8.t * _CK_ULONG))


assume val _signUpdate: pPart: seq FStar.UInt8.t -> ulPartLen: nat {Seq.length pPart = ulPartLen} -> pMechanism: _CK_MECHANISM_TYPE -> key: _CK_OBJECT_HANDLE ->
	previousSign: option temporalStorage -> 
	Tot (result temporalStorage)


val signInit: d: device -> 
	hSession: _CK_SESSION_HANDLE -> 
	pMechanism: _CK_MECHANISM_TYPE{isPresentOnDevice d pMechanism /\ 
		(let flags = mechanismGetFlags d pMechanism in isFlagSign flags)} ->
	keyHandler: _CK_OBJECT_HANDLE{Seq.length d.keys > keyHandler /\ 
		(let key = Seq.index d.keys keyHandler in 
		let attrKey = (key.element).attrs in
		isAttributeSign attrKey)} -> 
	Pure(
			(resultDevice: device)  * (r: result bool)
		)
	(requires
		(
			let f = predicateSessionSignature hSession in 
			let openedSessions = d.subSessions in count f openedSessions = 0
		)
	)
	(ensures (fun h -> 
		let (resultDevice, r) = h in 
		if Inr? r then 
			d = resultDevice 
		else
			let f = predicateSessionSignature hSession in 
			let openedSessions = resultDevice.subSessions in 
			count f openedSessions = 1 /\
			(
				let session = Seq.find_l (fun x -> true) openedSessions in 
				let s = (match session with Some a -> a) in 
				let sessionIndex = seq_getIndex openedSessions s in 
				let state = subSessionGetState s in 
				subSessionGetState s = _SubSessionInit /\  
				subSessionGetMechanism s = pMechanism /\
				subSessionGetKeyHandler	s = keyHandler /\
				modifiesSessionsM resultDevice d sessionIndex
			)	
		)
	)	


let signInit d hSession pMechanism keyHandler = 
	let newSession = Signature hSession _SubSessionInit pMechanism keyHandler None in 
	let resultDevice = deviceAddSession #d.keys #d.mechanisms hSession (predicateSessionSignature hSession) d newSession in 
	(resultDevice, Inl true)


val sign: d: device -> 
	hSession: _CK_SESSION_HANDLE -> 
	(* the data to sign *)
	pData: seq UInt8.t -> 
	(* count of bytes to sign *)
	ulDataLen: _CK_ULONG{Seq.length pData = ulDataLen} -> 
	(* in case of only request for the length*)
	pSignature: option (seq UInt8.t) -> 
	pSignatureLen: _CK_ULONG{if Some? pSignature then Seq.length (match pSignature with Some a -> a) = pSignatureLen else true} -> 
	Pure(
		(resultDevice: device) &
		r: result (o: option (seq FStar.UInt8.t){Some? pSignature ==> Some? o /\ None? pSignature ==> None? o} * _CK_ULONG)
		)
	(requires(
		let openedSessions = d.subSessions in 
		count (fun x -> subSessionGetID x = hSession) openedSessions = 1 /\
		(	
			let theSameSession = find_l (predicateSessionSignature hSession) openedSessions in 
			let session = (match theSameSession with Some a -> a) in 
			subSessionGetState session = _SubSessionInit
		)
	))
	(ensures (fun h -> 
		let (|resultDevice, r|) = h in 
			if None? pSignature then 
				d = resultDevice 
			else if Inr? r then 
				let openedSessions = resultDevice.subSessions in 
				count (fun x -> subSessionGetState x = hSession) openedSessions = 0 /\
				(
					let session = find_l (predicateSessionSignature hSession) d.subSessions in 
					let sessionIndex = seq_getIndex d.subSessions (match session with Some a -> a) in 
					modifiesSessionsM d resultDevice sessionIndex
				)
			else		
				let openedSessions = resultDevice.subSessions in 
				count (fun x -> subSessionGetState x = hSession) openedSessions = 0 /\
				(
					let session = find_l (predicateSessionSignature hSession) d.subSessions in 
					let sessionIndex = seq_getIndex d.subSessions (match session with Some a -> a) in 
					modifiesSessionsM d resultDevice sessionIndex
				)
	))

let sign d hSession pData ulDataLen pSignature pSignatureLen = 
	let currentSession = find_l (fun x -> subSessionGetID x = hSession) d.subSessions in 
	let currentSession = match currentSession with Some a -> a in 
	let m = subSessionGetMechanism	currentSession in 
	let k = subSessionGetKeyHandler	currentSession in 
	let signature = _sign pData m k pSignature pSignatureLen in 
	if Inr? signature then
		let session = find_l (fun x -> subSessionGetID x = hSession) d.subSessions in 
		let session = match session with Some a -> a in 
		let resultDevice = deviceRemoveSession #d.keys #d.mechanisms hSession (predicateSessionSignature hSession) d in 
		let exc = (match signature with Inr exc -> exc) in (|d, Inr exc|) else	
	let (pSig,  pLen) = (match signature with Inl a -> a) in
	if None? pSignature then 
		(|d, Inl (None, pLen)|)
	else
		let session = find_l (fun x -> subSessionGetID x = hSession) d.subSessions in 
		let session = match session with Some a -> a in 
		let resultDevice = deviceRemoveSession #d.keys #d.mechanisms hSession (predicateSessionSignature hSession) d in 
		(|resultDevice, Inl(Some pSig , pLen)|)


val signUpdate: d: device -> 
	hSession: _CK_SESSION_HANDLE -> 
	(* the data to sign *)
	pPart: seq FStar.UInt8.t -> //seq uint8
	(* count of bytes to sign *)
	ulPartLen : _CK_ULONG{Seq.length pPart = ulPartLen} -> 
	Pure(
		(resultDevice: device) &
		(r: result bool)
	)
	(requires(
		let openedSessions = d.subSessions in 
		let theSameSession = find_l (fun x -> subSessionGetID x = hSession) openedSessions in 
		count (fun x -> subSessionGetID x = hSession) openedSessions = 1 /\
		(let session = (match theSameSession with Some a -> a ) in 
			subSessionGetState session = _SubSessionInit || subSessionGetState session = _SubSessionUpd)
	))
	(ensures (fun h -> 
		let (|resultDevice, r|) = h in 
		if Inr? r then 
			let openedSessions = resultDevice.subSessions in 
				count (fun x -> subSessionGetState x = hSession) openedSessions = 0 /\
				(
					let session = find_l (predicateSessionSignature hSession) d.subSessions in 
					let sessionIndex = seq_getIndex d.subSessions (match session with Some a -> a) in 
					modifiesSessionsM d resultDevice sessionIndex
				)
		else
			let openedSessions = resultDevice.subSessions in 
			let theSameSession = find_l (fun x -> subSessionGetID x = hSession) openedSessions in 
			count (fun x -> subSessionGetID x = hSession) openedSessions = 1 /\
			(let session = match theSameSession with Some a -> a in 
				subSessionGetState session = _SubSessionUpd &&
				(let previousSession = find_l (fun x -> subSessionGetID x = hSession) d.subSessions in 
				let previousSession = match previousSession with Some a -> a in 
				subSessionGetMechanism previousSession = subSessionGetMechanism session &&
				subSessionGetKeyHandler previousSession = subSessionGetKeyHandler session &&
				Some? (subSessionGetStorage previousSession)) /\
				(
					let session = find_l (predicateSessionSignature hSession) d.subSessions in 
					let sessionIndex = seq_getIndex d.subSessions (match session with Some a -> a) in 
					modifiesSessionsM d resultDevice sessionIndex
				)
			)	
		)
	)


let signUpdate d hSession pPart ulPartLen = 
	let currentSession = find_l (fun x -> subSessionGetID x = hSession) d.subSessions in 
	let currentSession = match currentSession with Some a -> a in 
	let m = subSessionGetMechanism	currentSession in 
	let k = subSessionGetKeyHandler currentSession in 
	let previousSign = subSessionGetStorage	currentSession in 
	let signature = _signUpdate pPart ulPartLen m k previousSign in 
	if Inr? signature then 
		let session = find_l (fun x -> subSessionGetID x = hSession) d.subSessions in 
		let session = match session with Some a -> a in 
		let resultDevice = deviceRemoveSession #d.keys #d.mechanisms hSession (predicateSessionSignature hSession) d in 
		let exc = (match signature with Inr exc -> exc) in (|d, Inr exc|) 
	else 
		let signature = (match signature with Inl a -> a) in 
		let session = find_l (fun x -> subSessionGetID x = hSession) d.subSessions in 
		let session = match session with Some a -> a in 
		let resultDevice = deviceUpdateSessionChangeStatus #d.keys #d.mechanisms hSession (predicateSessionSignature hSession) d in 
		let resultDevice = deviceUpdateSessionChangeStorage #resultDevice.keys #resultDevice.mechanisms hSession (predicateSessionSignature hSession) resultDevice signature in 
		(|resultDevice, Inl true|)


val signFinal: d: device ->  
	hSession: _CK_SESSION_HANDLE ->
	Pure(
		(resultDevice: device) &
		(r: result (seq FStar.UInt8.t * _CK_ULONG))
	)
	(requires(
		let openedSessions = d.subSessions in 
		let theSameSession = find_l (fun x -> subSessionGetID x = hSession) openedSessions in 
		(let session = (match theSameSession with Some a -> a) in 
		subSessionGetState session = _SubSessionUpd))
	)
	(ensures (fun h -> 
		let (|resultDevice, r|) = h in 
			if Inr? r then 
				d = resultDevice 
			else
				let openedSessions = resultDevice.subSessions in 
				count (predicateSessionSignature hSession) openedSessions = 0 /\
				(
					let session = find_l (predicateSessionSignature hSession) d.subSessions in 
					let sessionIndex = seq_getIndex d.subSessions (match session with Some a -> a) in 
					modifiesSessionsM d resultDevice sessionIndex
				)
		)
	)


let signFinal d hSession = 
	let currentSession = find_l (fun x -> subSessionGetID x = hSession) d.subSessions in 
	let currentSession = match currentSession with Some a -> a in  
	let signature = subSessionGetStorage currentSession in 
	let signature = match signature with Some a -> a in 
	let signature = match signature with Element a -> a in 
	let (s, len) = signature in 
	let resultDevice = deviceRemoveSession #d.keys #d.mechanisms hSession (predicateSessionSignature hSession) d in 
	(|resultDevice, Inl (s, len)|)


(*)
val _CKS_Verify: d: device -> 
	hSession : nat -> 
	pMechanism: _CK_MECHANISM_TYPE{isPresentOnDevice d pMechanism /\
		(let flags = mechanismGetFlags d pMechanism in isFlagVerify flags)} -> 
	keyHandler: _CK_OBJECT_HANDLE{Seq.length d.keys > keyHandler /\
		(let key = Seq.index d.keys keyHandler in let attrKey = (key.element).attrs in 
		isAttributeVerify attrKey)} -> 
	data: seq FStar.UInt8.t -> 
	dataLen : nat {Seq.length data = dataLen} -> 	
	Pure(
			resultDevice: device & 
			(option (_CK_ULONG * _CK_ULONG))
		)
	(requires(True))
	(ensures (fun h -> True))

(*)
val verifyInit: d: device -> 
	hSession: _CK_SESSION_HANDLE -> 
	pMechanism: _CK_MECHANISM_TYPE{isPresentOnDevice d pMechanism /\ 
		(let flags = mechanismGetFlags d pMechanism in isFlagVerify flags)} ->
	keyHandler: _CK_OBJECT_HANDLE{Seq.length d.keys > keyHandler /\ 
		(let key = Seq.index d.keys keyHandler in 
		let attrKey = (key.element).attrs in
		isAttributeVerify attrKey)} -> 
	Pure(
			(resultDevice: device)  * 
			(r: result bool)
		)
	(requires(
			(* exists current session *)
		let openedSessions = d.subSessions in 
		let theSameSession = find_l (fun x -> x.id = hSession) openedSessions in 
		None? theSameSession
	))
	(ensures (fun h -> 
		let (resultDevice, r) = h in 
		if Inr? r then 
			d = resultDevice 
		else
			let openedSessions = resultDevice.subSessions in 
			let theSameSession = find_l (fun x -> x.id = hSession) openedSessions in 
			Some? theSameSession /\
			(let session = (match theSameSession with Some a  -> a) in 
			session.state = _SubSessionInit /\ 
			session.pMechanism = pMechanism /\
			session.keyHandler = keyHandler) /\
			count (fun x -> x.id = hSession) openedSessions = 1
		)
	)	
