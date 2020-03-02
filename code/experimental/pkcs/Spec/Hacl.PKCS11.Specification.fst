module Hacl.PKCS11.Specification


open FStar.UInt32
open FStar.Seq
open FStar.Option

open FStar.Seq.Base
open FStar.Seq.Properties

open PKCS11.Spec.Lemmas
open Hacl.PKCS.Specification.Constants


(* #set-options "--z3rlimit 200 --lax"  *)

#set-options "--z3rlimit 300 --ifuel 5 --fuel 5"


(* Zero-level types *)
type uint32_t = a: nat {a < pow2 32}

(* First-level types *)

(* 
/* an unsigned value, at least 32 bits long */
typedef unsigned long int CK_ULONG; 
*)

type _CK_ULONG = uint32_t


(* Second-level types"*)

(*
/* CK_MECHANISM_TYPE is a value that identifies a mechanism
 * type */
typedef CK_ULONG          CK_MECHANISM_TYPE;*)
type _CK_MECHANISM_TYPE = 
  |CKM_RSA_PKCS_KEY_PAIR_GEN
  |CKM_DSA
  |CKM_EC_KEY_PAIR_GEN
  |CKM_ECDSA
  |CKM_AES_KEY_GEN
  (* and traditionally much more *)


(* This is an example of the implementation *)
val isMechanismUsedForSignature: mechanism : _CK_MECHANISM_TYPE -> Tot bool

let isMechanismUsedForSignature mechanism = 
  match mechanism with 
  |CKM_DSA -> true
  |CKM_ECDSA -> true
  |_ -> false


(* This is an example of the implementation *)
val isMechanismUsedForVerification: mechanism: _CK_MECHANISM_TYPE -> Tot bool

let isMechanismUsedForVerification mechanism =
  match mechanism with
  |CKM_DSA -> true
  |CKM_ECDSA -> true
  |_ -> false


(*
/* CK_ATTRIBUTE_TYPE is a value that identifies an attribute
 * type */
typedef CK_ULONG          CK_ATTRIBUTE_TYPE;
*)
type _CK_ATTRIBUTE_TYPE = 
  |CKA_CLASS
  |CKA_PRIVATE
  |CKA_KEY_TYPE
  (* and much more *)

(*
/* CK_OBJECT_CLASS is a value that identifies the classes (or
 * types) of objects that Cryptoki recognizes.  It is defined
 * as follows: */
typedef CK_ULONG          CK_OBJECT_CLASS;
*)
type _CK_OBJECT_CLASS = 
  |CKO_DATA
  |CKO_CERTIFICATE
  |CKO_PUBLIC_KEY
  |CKO_PRIVATE_KEY
  |CKO_SECRET_KEY
  |CKO_HW_FEATURE
  |CKO_DOMAIN_PARAMETERS
  |CKO_MECHANISM
  |CKO_OTP_KEY
  |CKO_VENDOR_DEFINED


(* /* CK_KEY_TYPE is a value that identifies a key type */
typedef CK_ULONG          CK_KEY_TYPE;
*)
type _CK_KEY_TYPE = 
  |CKK_RSA
  |CKK_DSA
  |CKK_DH
  |CKK_EC 
  (*and much more *)


(* /* CK_OBJECT_CLASS is a value that identifies the classes (or
 * types) of objects that Cryptoki recognizes.  It is defined
 * as follows: */
typedef CK_ULONG          CK_OBJECT_CLASS; *) 
type _CK_OBJECT_HANDLE = _CK_ULONG

(*/* at least 32 bits; each bit is a Boolean flag */
typedef CK_ULONG          CK_FLAGS;
*)
type _CK_FLAGS = _CK_ULONG 

(*/* CK_SESSION_HANDLE is a Cryptoki-assigned value that
 * identifies a session */
typedef CK_ULONG          CK_SESSION_HANDLE;
*)
type _CK_SESSION_HANDLE = _CK_ULONG

(* 
/* CK_MECHANISM_INFO provides information about a particular
 * mechanism */
typedef struct CK_MECHANISM_INFO {
    CK_ULONG    ulMinKeySize;
    CK_ULONG    ulMaxKeySize;
    CK_FLAGS    flags;
} CK_MECHANISM_INFO; *)


type _CKS_MECHANISM_INFO = 
  | MecInfo: ulMinKeySize: _CK_ULONG -> ulMaxKeySize: _CK_ULONG -> flags: _CK_FLAGS -> _CKS_MECHANISM_INFO	


let _ck_attribute_get_type: _CK_ATTRIBUTE_TYPE -> Tot Type0 = function
  |CKA_CLASS -> _CK_OBJECT_CLASS
  |_ -> _CK_ULONG


(*/* CK_ATTRIBUTE is a structure that includes the type, length
 * and value of an attribute */
*)

type _CK_ATTRIBUTE  = 
  |A: 
    aType: _CK_ATTRIBUTE_TYPE -> pValue: seq (_ck_attribute_get_type aType) -> ulValue: nat{ulValue < pow2 32 /\ length pValue = ulValue} -> _CK_ATTRIBUTE


type _object = 
  |O: 
    identifier: _CK_ULONG -> 
    dat: seq FStar.UInt8.t -> 
    attrs: seq _CK_ATTRIBUTE-> 
    _object


(* The method takes an object and returns whether amongs its attributes there is one that is CKA_CLASS. If the attribute is found that the attribute is returned, otherwise the None is returned *)

val getObjectAttributeClass: obj: _object -> Tot (r: option _CK_ATTRIBUTE
  {Some? r  ==>
    (
      let a = (match r with Some a -> a) in  
      a.aType == CKA_CLASS
   )
  }  
)

let getObjectAttributeClass obj = 
  find_l (fun x -> x.aType = CKA_CLASS) obj.attrs


type keyEntity = 
  |Key: element: _object{
    (let attrs = getObjectAttributeClass element in Some? attrs && 
      (
	let a = (match attrs with Some a -> a) in 
	let value = Seq.index (CKA_CLASS?.pValue a) 0 in 
	value = CKO_OTP_KEY || value = CKO_PRIVATE_KEY  || value = CKO_PUBLIC_KEY || value = CKO_SECRET_KEY
      )
    )
  } -> keyEntity


type temporalStorage = 
  |Element: seq FStar.UInt8.t -> temporalStorage

(* ??? *)
type mechanismSpecification = 
	| Mechanism: mechanismID: _CK_MECHANISM_TYPE -> 
		pParameters: seq FStar.UInt8.t -> 
		mechanismSpecification


type _SessionState = 
  |SubsessionSignatureInit
  |SubsessionSignatureUpdate
  |SubsessionVerificationInit
  |SunsessionVerificationUpdate

(* A metadata element represention an ongoing function *)
type subSession (k: seq keyEntity) (m: seq mechanismSpecification) = 
  |Signature: 
    (* The session identifier that has caused the operation *)
    id: _CK_SESSION_HANDLE -> 
    (* The state of the ongoing session *)
    state: _SessionState {state = SubsessionSignatureInit \/ state = SubsessionSignatureUpdate} -> 
    (* The identifier of the mechanism used for the operation *)
    (* The mechanism requirements: present in the device and to be the signature algorithm *)
    pMechanism: _CK_MECHANISM_TYPE
      {exists (a: nat {a < Seq.length m}). let mechanism = Seq.index m a in mechanism.mechanismID = pMechanism /\ isMechanismUsedForSignature pMechanism} ->
    (* The identifier of the key used for the operation *)
    (* The key requirement: present in the device and to be a signature key *)
    keyHandler: _CK_OBJECT_HANDLE{Seq.length k > keyHandler} -> 
    (* Temporal space for the signature *)
    temp: option temporalStorage -> subSession k m
  |Verify : 	
    (* The session identifier that has caused the operation *)
    id: _CK_SESSION_HANDLE -> 
    (* The state of the ongoing session *)
    state: _SessionState {state = SubsessionVerificationInit \/ state = SunsessionVerificationUpdate} ->
    (* The identifier of the mechanism used for the operation *)
    (* The mechanism requirements: present in the device and to be the signature algorithm *)
    pMechanism: _CK_MECHANISM_TYPE
      {exists (a: nat {a < Seq.length m}). let mechanism = Seq.index m a in mechanism.mechanismID = pMechanism} ->
    (* The identifier of the key used for the operation *)
    (* The key requirement: present in the device and to be a signature key *)
    keyHandler: _CK_OBJECT_HANDLE {Seq.length k > keyHandler} -> 
    (* Temporal space for the signature *)
    temp: option temporalStorage -> subSession k m


















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
				|Signature a b c d e ->
					begin match r with 
						|Signature a1 b1 c1 d1 e1 -> a = a1 /\ b = b1/\ c = c1 /\ d = d1 
					end	
				|Verify a b c d e ->
					begin match r with 
						|Verify a1 b1 c1 d1 e1 -> a = a1 /\b = b1 /\ c = c1 /\ d = d1 
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
	|Signature _ _  c _ _ -> c
	|Verify _ _ c _ _ -> c

val subSessionGetKeyHandler: #ks: seq keyEntity -> #ms: seq mechanismSpecification -> s: subSession ks ms -> Tot _CK_OBJECT_HANDLE

let subSessionGetKeyHandler #ks #ms s = 
	match s with 
	|Signature _ _ _ d _ -> d 
	|Verify _ _ _ d _ -> d


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


val isPresentOnDevice_: d: device -> pMechanism: _CK_MECHANISM_TYPE -> counter: nat{counter < Seq.length d.mechanisms} -> 
	Tot (r: bool {r = true ==> (exists (a: nat{a < Seq.length d.mechanisms}). let m = Seq.index d.mechanisms a in m.mechanismID = pMechanism) /\ 
		(Some? (find_l (fun x -> x.mechanismID = pMechanism) d.mechanisms))
		}
	)
	(decreases(Seq.length d.mechanisms - counter))

let rec isPresentOnDevice_ d pMechanism counter =
	let m = Seq.index d.mechanisms counter in 
	if (m.mechanismID = pMechanism) then 
		(
			let f = (fun x -> x.mechanismID = pMechanism) in 
				assert(Some? (find_l f (Seq.create 1 m)));
			let a, b' = Seq.split d.mechanisms counter in 
			let elementCounter, b = Seq.split b' 1 in 
				assert(Some? (find_l f  elementCounter));
			find_append_some elementCounter b f; 
				assert(equal (Seq.append elementCounter b) b');
			find_append_some_s2 a b' f;
				assert(equal (Seq.append a b') d.mechanisms);
				admit();
			true
		)
	else if counter+1 = Seq.length d.mechanisms then false 
	else 
		isPresentOnDevice_ d pMechanism (counter +1) 

val isPresentOnDevice: d: device -> pMechanism: _CK_MECHANISM_TYPE -> 
	Tot (r: bool {r = true ==> (exists (a: nat{a < Seq.length d.mechanisms}). let m = Seq.index d.mechanisms a in m.mechanismID = pMechanism) /\ 
			(Some? (find_l (fun x -> x.mechanismID = pMechanism) d.mechanisms))
		}
	)

let isPresentOnDevice d pMechanism =
	if Seq.length d.mechanisms = 0 then false else
	isPresentOnDevice_ d pMechanism 0


val mechanismGetFromDevice: d: device -> pMechanism: _CK_MECHANISM_TYPE{isPresentOnDevice d pMechanism = true} -> 
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
	s: subSession ks ms -> s1 : subSession ks1 ms1 -> Tot Type0

let sessionEqual #ks #ms #ks1 #ms1 s s1 = 
	match s with 
	|Signature a b c d e -> 
		begin match s1 with 
			|Signature a1 b1 c1 d1 e1 -> a == a1 /\ b == b1 /\ c == c1 /\ d == d1 /\ e == e1
			| _ -> False
		end
	|Verify a b c d e -> 	
		begin 
			match s1 with
			| Verify a1 b1 c1 d1 e1 -> a == a1 /\ b == b1 /\ c == c1 /\ d == d1 /\ e == e1
			| _ -> False

		end	

val updateSession_: d: device -> 
	s: subSession d.keys d.mechanisms ->
 	ks: seq keyEntity{Seq.length ks >= Seq.length d.keys\/
 		subSessionGetKeyHandler s < Seq.length ks} ->
	ms: seq mechanismSpecification{ms == d.mechanisms} -> 
	Tot (r: subSession ks ms
		{Signature? s ==> Signature? r /\ Verify? s ==> Verify? r /\ sessionEqual s r})	

let updateSession_ d s ks ms = 
	match s with 
	| Signature a b c d e -> 
		let (a: subSession ks ms) = Signature a b c d e in a
	| Verify a b c d e -> 
		let (a: subSession ks ms) = Verify a b c d e in a		


val _updateSession: d: device ->  ks: seq keyEntity -> 
	ms: seq mechanismSpecification{ms == d.mechanisms} -> 
	s: seq (subSession d.keys d.mechanisms)
		{
			forall (i: nat {i < Seq.length s}). let elem = Seq.index s i in 
				Seq.length ks >= Seq.length d.keys \/ subSessionGetKeyHandler elem < Seq.length ks

		} ->
	counter: nat {counter < Seq.length s}->
	alreadySeq: seq (subSession ks ms) {Seq.length alreadySeq = counter /\
		(
			forall (i: nat {i < Seq.length alreadySeq}). 
				(sessionEqual (index s i) (index alreadySeq i))
		)
	} -> 
	Tot (snew: (seq (subSession ks ms))
		{Seq.length s = Seq.length snew /\
			(forall (i: nat{i < Seq.length s}). sessionEqual (index s i) (index snew i))
		}
	)
	(decreases (Seq.length s - Seq.length alreadySeq))

let rec _updateSession d ks ms s counter alreadySeq = 
	let element = Seq.index s counter in 
	let updatedElement = updateSession_ d element ks ms in 
	let updatedSeq = Seq.append alreadySeq (Seq.create 1 updatedElement) in 
	if Seq.length s = Seq.length updatedSeq	then 
		updatedSeq 
	else 
		_updateSession d ks ms s (counter + 1) updatedSeq	

val updateSession: d: device ->  ks: seq keyEntity -> 
	ms: seq mechanismSpecification{ms == d.mechanisms} -> 
	s: seq (subSession d.keys d.mechanisms)
	{
		forall (i: nat {i < Seq.length s}). let elem = Seq.index s i in 
			Seq.length ks >= Seq.length d.keys \/ subSessionGetKeyHandler elem < Seq.length ks
	} ->
	Tot (snew: (seq (subSession ks ms))
		{
			Seq.length s = Seq.length snew /\ 
			(forall (i: nat{i < Seq.length s}). sessionEqual (index s i) (index snew i))
		}
	)
 
let updateSession d ks ms s = 
	if Seq.length s = 0 then 
		Seq.createEmpty 
	else	
	_updateSession d ks ms s 0 (Seq.createEmpty)


(* Modifies Section*)
val modifiesKeysM: dBefore: device -> dAfter: device{Seq.length dBefore.keys + 1 = Seq.length dAfter.keys /\ Seq.length dBefore.subSessions = Seq.length dAfter.subSessions} -> 
	i: _CK_OBJECT_HANDLE{i < Seq.length dAfter.keys} -> Tot Type0

let modifiesKeysM dBefore dAfter i = 
	let mechanismsPrevious, keysPrevious, objectsPrevious = dBefore.mechanisms, dBefore.keys, dBefore.objects in 
	let mechanismsNew, keysNew, objectsNew = dAfter.mechanisms, dAfter.keys, dAfter.objects in 
	let keysBeforeA, keysBeforeB = Seq.split dBefore.keys i in 
	let keysAfterA, key_keysAfterB = Seq.split dAfter.keys i in 	
	let key, keysAfterB = Seq.split key_keysAfterB 1 in 
	mechanismsPrevious == mechanismsNew /\
	keysBeforeA == keysAfterA /\ keysBeforeB = keysAfterB /\
	objectsPrevious == objectsNew /\ 
	(forall (i: nat{i < Seq.length dBefore.subSessions}). sessionEqual (index dBefore.subSessions i) (index dAfter.subSessions i))



val modifiesSessionsM: dBefore: device -> dAfter : device{Seq.length dBefore.subSessions = Seq.length dAfter.subSessions +1} -> 
	i: nat{i < Seq.length dBefore.subSessions} -> Tot Type0

let modifiesSessionsM dBefore dAfter i = 
	let mechanismsPrevious, keysPrevious, objectsPrevious = dBefore.mechanisms, dBefore.keys, dBefore.objects in 
	let mechanismsNew, keysNew, objectsNew = dAfter.mechanisms, dAfter.keys, dAfter.objects in 
	let sessionsBeforeA, session_sessionBeforeB = Seq.split dBefore.subSessions i in 
	let _, sessionsBeforeB = Seq.split session_sessionBeforeB 1 in 
	let sessionsAfterA, sessionsAfterB = Seq.split dAfter.subSessions i in 
	mechanismsPrevious == mechanismsNew /\
	keysPrevious == keysNew /\ 
	objectsPrevious == objectsNew /\
	(forall (i: nat{i < Seq.length sessionsBeforeA}). sessionEqual (index sessionsBeforeA i) (index sessionsAfterA i))/\
	(forall (i: nat{i < Seq.length sessionsBeforeB}). sessionEqual (index sessionsBeforeB i) (index sessionsAfterB i))


val modifiesSessionsE: dBefore: device -> dAfter: device{Seq.length dBefore.subSessions = Seq.length dAfter.subSessions} ->
	i: nat {i < Seq.length dBefore.subSessions} -> Tot Type0

let modifiesSessionsE dBefore dAfter i = 
	let mechanismsPrevious, keysPrevious, objectsPrevious = dBefore.mechanisms, dBefore.keys, dBefore.objects in 
	let mechanismsNew, keysNew, objectsNew = dAfter.mechanisms, dAfter.keys, dAfter.objects in 
	let sessionsBeforeA, session_sessionBeforeB = Seq.split dBefore.subSessions i in 
	let _, sessionsBeforeB = Seq.split session_sessionBeforeB 1 in 
	let sessionsAfterA, session_sessionAfterB = Seq.split dBefore.subSessions i in 
	let _, sessionsAfterB = Seq.split session_sessionBeforeB 1 in 
	mechanismsPrevious == mechanismsNew /\
	keysPrevious == keysNew /\
	objectsPrevious == objectsNew /\
	(forall (i: nat{i < Seq.length sessionsBeforeA}). sessionEqual (index sessionsBeforeA i) (index sessionsAfterA i))/\
	(forall (i: nat{i < Seq.length sessionsBeforeB}). sessionEqual (index sessionsBeforeB i) (index sessionsAfterB i))


(* Predicate Section*)

let predicateSessionVerify hSession = (fun #p1 #p2 (x: subSession p1 p2) -> Verify? x && subSessionGetID x = hSession)
let predicateSessionSignature hSession = (fun #p1 #p2 (x:subSession p1 p2) -> Signature? x && subSessionGetID x = hSession)

val lemma_predicateSignatureForAll: hSession: _CK_SESSION_HANDLE -> Lemma 
	(ensures (
		let f = predicateSessionSignature hSession in 
		forall (ks1:seq keyEntity) (ms1: seq mechanismSpecification) 
		(ks2: seq keyEntity) (ms2: seq mechanismSpecification) 
		(s: subSession ks1 ms1) (s2: subSession ks2 ms2). 
		Signature? s == Signature? s2 /\ subSessionGetID s == subSessionGetID s2 ==> f s == f s2)
	)

let lemma_predicateSignatureForAll hSession = ()


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
	let newKey = Seq.create 1 newKey in 
	let keysNew = Seq.append keysPrevious newKey in
	let handler = Seq.length keysNew -1 in 
		lemma_append keysPrevious newKey;
	let s = d.subSessions in
	let sessionsUpdated = updateSession d keysNew mechanismsPrevious s in
	let resultDevice = Device keysNew mechanismsPrevious objectsPrevious sessionsUpdated in 
	(|resultDevice, handler|)


val deviceRemoveSession: #ks: seq keyEntity -> #ms: seq mechanismSpecification ->  hSession : _CK_SESSION_HANDLE -> 
	f: (#ks: seq keyEntity -> #ms: seq mechanismSpecification -> subSession ks ms -> bool) -> 
	d: device{count f d.subSessions = 1} ->
	Tot (resultDevice: device
		{
			count f resultDevice.subSessions  = 0 /\
			Seq.length d.subSessions = Seq.length resultDevice.subSessions + 1  /\
			(
				let indexOfSessionToDelete = seq_getIndex2 f d.subSessions in 
				modifiesSessionsM d resultDevice indexOfSessionToDelete
			)
		}
	)	

let deviceRemoveSession #ks #ms hSession f d = 
	let mechanismsPrevious = d.mechanisms in 
	let keysPrevious = d.keys in 
	let objectsPrevious = d.objects in 
	let sessionsPrevious = d.subSessions in 
	let sessionsNew = seq_remove sessionsPrevious f in 
		seq_remove_lemma_count_of_deleted sessionsPrevious f;
	let newDevice = Device keysPrevious mechanismsPrevious objectsPrevious sessionsNew in 
	let i = seq_getIndex2 f d.subSessions in 
	let sessionsBeforeA, session_sessionBeforeB = Seq.split d.subSessions i in 
	let _, sessionsBeforeB = Seq.split session_sessionBeforeB 1 in 
	let sessionsAfterA, sessionsAfterB = Seq.split newDevice.subSessions i in 
		seq_remove_unchanged sessionsPrevious f;	
	newDevice


val deviceUpdateSessionChangeStatus: #ks : seq keyEntity -> #ms : seq mechanismSpecification -> 
	f: (#ks: seq keyEntity -> #ms: seq mechanismSpecification -> subSession ks ms -> bool)
	{forall (ks1:seq keyEntity) (ms1: seq mechanismSpecification) 
		(ks2: seq keyEntity) (ms2: seq mechanismSpecification) 
		(s: subSession ks1 ms1) (s2: subSession ks2 ms2). 
		Signature? s == Signature? s2 /\ subSessionGetID s == subSessionGetID s2 ==> f s == f s2}->
	d: device {count (f #d.keys #d.mechanisms) d.subSessions = 1}  -> 
	Tot (resultDevice: device
		{ 
			let session = find_l (f #resultDevice.keys #resultDevice.mechanisms) resultDevice.subSessions in 
			count (f #resultDevice.keys #resultDevice.mechanisms) resultDevice.subSessions = 1 /\ 
			Seq.length resultDevice.subSessions = Seq.length d.subSessions /\
			(
				let sessionIndex = seq_getIndex2 (f #d.keys #d.mechanisms) d.subSessions  in 
					countMore0IsSome resultDevice.subSessions (f #resultDevice.keys #resultDevice.mechanisms);
				let s = match session with Some a -> a in 

				let previousSessions = d.subSessions in 
				let previousSession = find_l (f #d.keys #d.mechanisms) previousSessions in 
					countMore0IsSome previousSessions  (f #d.keys #d.mechanisms);
				let previousSession = match previousSession with Some a -> a in 

				subSessionGetState s == _SubSessionUpd /\
				subSessionGetStorage s == subSessionGetStorage previousSession /\
				subSessionGetMechanism s == subSessionGetMechanism previousSession /\
				subSessionGetKeyHandler s == subSessionGetKeyHandler previousSession /\
				modifiesSessionsE d resultDevice sessionIndex
			)
		}
	)	

let deviceUpdateSessionChangeStatus #ks #ms f d = 
	let mechanismsPrevious = d.mechanisms in 
	let keysPrevious = d.keys in 
	let objectsPrevious = d.objects in 
	let sessionsPrevious = d.subSessions in 
	let sessionsToChange = find_l (f #d.keys #d.mechanisms) sessionsPrevious in 
		countMore0IsSome sessionsPrevious (f #d.keys #d.mechanisms);
	let sessionToChange = match sessionsToChange with |Some a -> a in 
	let sessionChanged = subSessionSetState sessionToChange (match sessionToChange with |Signature _ _ _ _ _ ->_SubSessionUpd |Verify _ _ _ _ _  -> _SubSessionUpdInit) in 
		assert(Signature? sessionToChange == Signature? sessionChanged);
	let sessionChanged = Seq.create 1 sessionChanged in 
	let sessionsNew = seq_remove sessionsPrevious (f #keysPrevious #mechanismsPrevious) in 
		seq_remove_lemma_count_of_deleted sessionsPrevious (f #keysPrevious #mechanismsPrevious);
	let sessionsUpdated = Seq.append sessionChanged sessionsNew in 
		lemma_append_count_aux2 (f #keysPrevious #mechanismsPrevious) sessionChanged sessionsNew;
	let newDevice = Device keysPrevious mechanismsPrevious objectsPrevious sessionsUpdated in 
	newDevice



val deviceUpdateSessionChangeStorage: #ks : seq keyEntity -> #ms : seq mechanismSpecification -> 
	f: (#ks: seq keyEntity -> #ms: seq mechanismSpecification -> subSession ks ms -> bool)
	{forall (ks1:seq keyEntity) (ms1: seq mechanismSpecification) 
		(ks2: seq keyEntity) (ms2: seq mechanismSpecification) 
		(s: subSession ks1 ms1) (s2: subSession ks2 ms2). 
		Signature? s == Signature? s2 /\ subSessionGetID s == subSessionGetID s2 ==> f s == f s2}->
	d: device {count (f #d.keys #d.mechanisms) d.subSessions = 1}  -> 
	storage : temporalStorage ->
	Tot (resultDevice: device
		{
			let session = find_l (f #resultDevice.keys #resultDevice.mechanisms) resultDevice.subSessions in 
			count (f #resultDevice.keys #resultDevice.mechanisms) resultDevice.subSessions = 1 /\ 
			Seq.length resultDevice.subSessions = Seq.length d.subSessions /\
			(
				let sessionIndex = seq_getIndex2 (f #d.keys #d.mechanisms) d.subSessions  in 
					countMore0IsSome resultDevice.subSessions (f #resultDevice.keys #resultDevice.mechanisms);
				let s = match session with Some a -> a in 

				let previousSessions = d.subSessions in 
				let previousSession = find_l (f #d.keys #d.mechanisms) previousSessions in 
					countMore0IsSome previousSessions  (f #d.keys #d.mechanisms);
				let previousSession = match previousSession with Some a -> a in 

				subSessionGetStorage s == Some storage /\
				subSessionGetState s == subSessionGetState previousSession /\
				subSessionGetMechanism s == subSessionGetMechanism previousSession /\
				subSessionGetKeyHandler s == subSessionGetKeyHandler previousSession /\

				modifiesSessionsE d resultDevice sessionIndex
			)	
		}
	)

let deviceUpdateSessionChangeStorage #ks #ms f d storage = 
	let mechanismsPrevious = d.mechanisms in 
	let keysPrevious = d.keys  in 
	let objectsPrevious = d.objects in 
	let sessionsPrevious = d.subSessions in 
	let sessionToChange = find_l (f #d.keys #d.mechanisms) sessionsPrevious in 
		countMore0IsSome sessionsPrevious (f #d.keys #d.mechanisms);
	let sessionToChange = match sessionToChange with | Some a -> a in 
	let sessionChanged = subSessionSetStorage sessionToChange (Some storage) in 
		assert(Signature? sessionToChange == Signature? sessionChanged);
	let sessionChanged = Seq.create 1 sessionChanged in 
	let sessionsNew = seq_remove sessionsPrevious (f #keysPrevious #mechanismsPrevious) in 
		seq_remove_lemma_count_of_deleted sessionsPrevious (f #keysPrevious #mechanismsPrevious);
	let sessionsUpdated = Seq.append sessionChanged sessionsNew in 
		lemma_append_count_aux2 (f #keysPrevious #mechanismsPrevious) sessionChanged sessionsNew;
	let newDevice = Device keysPrevious mechanismsPrevious objectsPrevious sessionsUpdated in 
	newDevice


val lemma_count: #ks: seq keyEntity -> #ms: seq mechanismSpecification -> #ks1 : seq keyEntity -> #ms1 : seq mechanismSpecification -> 
	s: seq (subSession ks ms) -> s1: seq (subSession ks1 ms1){Seq.length s = Seq.length s1} -> f: (subSession ks ms -> bool) -> f1: (subSession ks1 ms1 -> bool) -> 
	Lemma (requires (forall (i: nat{i < Seq.length s}). sessionEqual (index s i) (index s1 i)))
	(ensures (count f s = count f1 s1))

let lemma_count #ks #ms #ks1 #ms1 s s1 f f1 = 
	if Seq.length s = 0 then () 
	else admit()


val deviceAddSession: hSession:_CK_SESSION_HANDLE ->
	f: (#ks: seq keyEntity -> #ms: seq mechanismSpecification -> subSession ks ms -> bool) -> 
	d: device{count f d.subSessions = 0} -> 
	newSession: subSession d.keys d.mechanisms{f newSession = true} -> 
	Tot (resultDevice: device
		{
			( 
				count f resultDevice.subSessions = 1 /\ Seq.length d.subSessions + 1 = Seq.length resultDevice.subSessions  /\ (
				let sessionIndex = seq_getIndex2 f resultDevice.subSessions in 
				modifiesSessionsM resultDevice d sessionIndex/\
				(
					let newSession = updateSession_ d newSession resultDevice.keys resultDevice.mechanisms in 
					Seq.count newSession resultDevice.subSessions = 1 /\
					seq_getIndex resultDevice.subSessions newSession == seq_getIndex2 f resultDevice.subSessions 
				))
			)	
		}
	)

let deviceAddSession hSession f d newSession = 
		countFCount f d.subSessions newSession;
	let mechanismsPrevious = d.mechanisms in 
	let keysPrevious = d.keys in 
	let objectsPrevious = d.objects in 
	let sessions = d.subSessions in 
	let sessions = updateSession d keysPrevious mechanismsPrevious sessions in 
		lemma_count #d.keys #d.mechanisms #keysPrevious #mechanismsPrevious d.subSessions sessions (f #d.keys #d.mechanisms) (f #keysPrevious #mechanismsPrevious);
	let newSessionUpd = updateSession_ d newSession d.keys d.mechanisms in 
	let newElement = Seq.create 1 newSessionUpd in 
	let sessions_upd = append sessions newElement in
		countFCount (f #keysPrevious #mechanismsPrevious) sessions newSessionUpd;
		lemma_append_count_aux newSessionUpd sessions newElement;
		lemma_append_count_aux2 (f #keysPrevious #mechanismsPrevious) sessions newElement;	
	let updatedDevice = Device keysPrevious mechanismsPrevious objectsPrevious sessions_upd	in 
		lemma_getIndex newSessionUpd sessions;
		lemma_getIndex2 f sessions newSessionUpd;
	updatedDevice


val _CKS_GenerateKey: d: device ->  
	hSession: _CK_SESSION_HANDLE -> 
	pMechanism: _CK_MECHANISM_TYPE{isPresentOnDevice d pMechanism = true /\ 
		(let flags = mechanismGetFlags d pMechanism in isFlagKeyGeneration flags)} ->
	pTemplate: seq attributeSpecification{checkedAttributes pTemplate} -> 
	Pure(
		(handler: result _CK_OBJECT_HANDLE) & 
		(resultDevice : device {
			if Inr? handler then 
				d = resultDevice else 
			let handler = (match handler with Inl a -> a) in 	
			Seq.length resultDevice.keys = Seq.length d.keys + 1 /\
			Seq.length resultDevice.subSessions = Seq.length d.subSessions /\
			handler = Seq.length resultDevice.keys -1 /\
			(
				let newCreatedKey = Seq.index resultDevice.keys handler in 
				isAttributeLocal (newCreatedKey.element).attrs 
			) /\
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
	pMechanism: _CK_MECHANISM_TYPE{isPresentOnDevice d pMechanism = true /\ 
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
				let sessionIndex = seq_getIndex2 f resultDevice.subSessions in 
				let s = Seq.index resultDevice.subSessions sessionIndex in 
				subSessionGetState s = _SubSessionInit  /\  
				subSessionGetMechanism s = pMechanism  /\
				subSessionGetKeyHandler	s = keyHandler /\
				Seq.length resultDevice.subSessions = Seq.length d.subSessions + 1 /\
				modifiesSessionsM resultDevice d sessionIndex 
			)	
		)
	)	

let signInit d hSession pMechanism keyHandler = 
	let newSession = Signature hSession _SubSessionInit pMechanism keyHandler None in 
	let f = predicateSessionSignature hSession in 
	let resultDevice = deviceAddSession hSession f d newSession in 
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
		let f = predicateSessionSignature hSession in 
		count (f #d.keys #d.mechanisms)  d.subSessions = 1 /\
		(
			let theSameSession = find_l f openedSessions in 
				countMore0IsSome openedSessions f;
			let session = (match theSameSession with Some a -> a) in 
			subSessionGetState session = _SubSessionInit
		)
	))
	(ensures (fun h -> 
		let (|resultDevice, r|) = h in 
		let f = predicateSessionSignature hSession in 
			if Inl? r && None? pSignature then 
				d = resultDevice 
			else 
				let openedSessions = resultDevice.subSessions in 
				count (f #d.keys #d.mechanisms) d.subSessions = 1 /\
				count f resultDevice.subSessions = 0 /\
				Seq.length d.subSessions = Seq.length resultDevice.subSessions + 1 /\
				(
					let sessionIndex = seq_getIndex2 f d.subSessions in 
					modifiesSessionsM d resultDevice sessionIndex
				)
	))

let sign d hSession pData ulDataLen pSignature pSignatureLen = 
	let f = predicateSessionSignature hSession in 
		countMore0IsSome d.subSessions f;
	let currentSession = find_l f d.subSessions in 
	let currentSession = match currentSession with Some a -> a in 
	let m = subSessionGetMechanism	currentSession in 
	let k = subSessionGetKeyHandler	currentSession in 
	let signature = _sign pData m k pSignature pSignatureLen in 
	if Inr? signature then
		let session = find_l f d.subSessions in 
		let session = match session with Some a -> a in 
		let exc = (match signature with Inr exc -> exc) in 
		let resultDevice = deviceRemoveSession #d.keys #d.mechanisms hSession f d in 
			begin
				(|resultDevice, Inr exc|) 
			end
	else	
		let (pSig,  pLen) = (match signature with Inl a -> a) in
		if None? pSignature then 
			(|d, Inl (None, pLen)|)
		else
			begin 
				let session = find_l f d.subSessions in 
				let session = match session with Some a -> a in 
				let f = predicateSessionSignature hSession in 
				let resultDevice = deviceRemoveSession #d.keys #d.mechanisms hSession f d in 
				(|resultDevice, Inl(Some pSig , pLen)|)
			end	


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
		let f = predicateSessionSignature hSession in 
		let sessions = d.subSessions in 
		let theSameSession = find_l f sessions in 
		count f sessions = 1 /\
		(
			countMore0IsSome sessions f;
			let session = (match theSameSession with Some a -> a ) in 
			subSessionGetState session = _SubSessionInit || subSessionGetState session = _SubSessionUpd
		)
	))
	(ensures (fun h -> 
		let (|resultDevice, r|) = h in 
		let f = predicateSessionSignature hSession in 
		if Inr? r then 
			count f resultDevice.subSessions = 0 /\
			count f d.subSessions = 1 /\
			Seq.length d.subSessions = Seq.length resultDevice.subSessions + 1 /\ 
			(
				let previousSession = find_l f d.subSessions in 
					countMore0IsSome d.subSessions f;
					assert(count f d.subSessions > 0);
				let sessionIndex = seq_getIndex2 f d.subSessions  in 
				modifiesSessionsM d resultDevice sessionIndex
			)
		else
			let sameSessions = resultDevice.subSessions in 
			let sameSession = find_l f sameSessions in 
			count f d.subSessions = 1 /\
			count f sameSessions = 1 /\
			(
					countMore0IsSome sameSessions f;
				let currentSession = match sameSession with Some a -> a in 
				let previousSessions = find_l f d.subSessions in 
					countMore0IsSome d.subSessions f;
				let previousSession = match previousSessions with Some a -> a in 
				let sessionIndex = seq_getIndex2 f d.subSessions in 

				Seq.length d.subSessions = Seq.length resultDevice.subSessions /\ 
				subSessionGetState currentSession = _SubSessionUpd /\
				subSessionGetMechanism previousSession = subSessionGetMechanism currentSession /\
				subSessionGetKeyHandler previousSession = subSessionGetKeyHandler currentSession /\
				Some? (subSessionGetStorage currentSession) /\
				modifiesSessionsE d resultDevice sessionIndex
			)
		)	
	)


let signUpdate d hSession pPart ulPartLen = 
	let f = predicateSessionSignature hSession in 
	let currentSession = find_l (f #d.keys #d.mechanisms) d.subSessions in 
	let currentSession = match currentSession with Some a -> a in 
	let m = subSessionGetMechanism	currentSession in 
	let k = subSessionGetKeyHandler currentSession in 
	let previousSign = subSessionGetStorage	currentSession in 
	let signature = _signUpdate pPart ulPartLen m k previousSign in 
	if Inr? signature then 
		let session = find_l (f #d.keys #d.mechanisms) d.subSessions in 
		let session = match session with Some a -> a in 
		let resultDevice = deviceRemoveSession #d.keys #d.mechanisms hSession f d in 
		let exc = (match signature with Inr exc -> exc) in 
		(|resultDevice, Inr exc|) 
	else 
		let signature = (match signature with Inl a -> a) in 
		let session = find_l f d.subSessions in 
		let session = match session with Some a -> a in 
		let resultDevice = deviceUpdateSessionChangeStatus #d.keys #d.mechanisms (predicateSessionSignature hSession) d in 
		let resultDevice = deviceUpdateSessionChangeStorage #resultDevice.keys #resultDevice.mechanisms (predicateSessionSignature hSession) resultDevice signature in 
		(|resultDevice, Inl true|)

val signFinal: d: device ->  
	hSession: _CK_SESSION_HANDLE ->
	Pure(
		(resultDevice: device) & (r: result (seq FStar.UInt8.t * _CK_ULONG))
	)
	(requires(
		let openedSessions = d.subSessions in 
		let f = predicateSessionSignature hSession in 
		count f openedSessions = 1 /\
		(
			countMore0IsSome openedSessions f;
			let theSameSession = find_l f openedSessions in 
			(	
				let session = match theSameSession with Some a -> a in 
				subSessionGetState session = _SubSessionUpd /\
				Some? (subSessionGetStorage session)
			)
		)
	))
	(ensures (fun h -> 
		let (|resultDevice, r|) = h in 
			if Inr? r then 
				d = resultDevice 
			else
				let openedSessions = resultDevice.subSessions in 
				let f = predicateSessionSignature hSession in 
				Seq.length d.subSessions = Seq.length resultDevice.subSessions + 1 /\ 
				count f openedSessions = 0 /\
				count f d.subSessions = 1 /\ 
				(
					let f1 = predicateSessionSignature hSession in 
					let session = find_l f d.subSessions in 
					let sessionIndex = seq_getIndex2 f d.subSessions in 
					modifiesSessionsM d resultDevice sessionIndex
				)
		)
	)

let signFinal d hSession = 
	let f = predicateSessionSignature hSession in 
	let currentSession = find_l f d.subSessions in 
		countMore0IsSome d.subSessions f;
	let currentSession = match currentSession with Some a -> a in  
	let signature = subSessionGetStorage currentSession in 
	let signature = match signature with Some a -> a in 
	let signature = match signature with Element a -> a in 
	let (s, len) = signature in 
	let resultDevice = deviceRemoveSession #d.keys #d.mechanisms hSession f d in 
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
