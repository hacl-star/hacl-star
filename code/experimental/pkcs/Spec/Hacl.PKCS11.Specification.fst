module Hacl.PKCS11.Specification


open FStar.UInt32
open FStar.UInt8

open FStar.Seq
open FStar.Option

open FStar.Seq.Base
open FStar.Seq.Properties

open PKCS11.Spec.Lemmas
open Hacl.PKCS11.Lib

open Hacl.PKCS11.Types
open Hacl.PKCS11.Lemmas

open Hacl.PKCS11.Attributes.API
open Hacl.PKCS11.Lemmas.ObjectTree


#set-options "--z3rlimit 300"


(* Second-level types*)


(*/* at least 32 bits; each bit is a Boolean flag */
typedef CK_ULONG          CK_FLAGS;
*)
type _CK_FLAGS_BITS = 
  |CKF_HW
  |CKF_SIGN
  |CKF_VERIFY
  |CKF_GENERATE
  |CKF_GENERATE_KEY_PAIR


(* Experemental implementation *)
let _ck_flags_bits_get_bit: _CK_FLAGS_BITS -> Tot nat = function
  |CKF_HW -> 0
  |CKF_SIGN -> 1
  |CKF_VERIFY -> 2
  |CKF_GENERATE -> 3
  |CKF_GENERATE_KEY_PAIR -> 4


type _CK_FLAGS = _CK_ULONG

(* Not to laugh, I forgot how to write it for nats *)
assume val logand: nat -> nat -> nat


val isBitFlagSet: _CK_FLAGS -> _CK_FLAGS_BITS -> Tot bool

let isBitFlagSet flag bit = 
  let bit = _ck_flags_bits_get_bit bit in 
  (logand flag bit) <> 0


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

(* Experemental implementation *)
let _map_cks_mechanism_info_to_mechanism: _CK_MECHANISM_TYPE -> _CKS_MECHANISM_INFO = function 
  |CKM_AES_KEY_GEN -> 
    MecInfo 0 0 0
  |_ -> MecInfo 0 0 0 


(* This is an example of the implementation *)
val isMechanismUsedForGenerateKey: mechanism : _CK_MECHANISM_TYPE -> supportedMechanisms: seq _CKS_MECHANISM_INFO -> Tot bool

let isMechanismUsedForGenerateKey mechanism supportedMechanisms = 
  let mechanismInfo = _map_cks_mechanism_info_to_mechanism mechanism in 
  isBitFlagSet mechanismInfo.flags CKF_GENERATE


(* This is an example of the implementation *)
val isMechanismUsedForGenerateKeyPair: mechanism : _CK_MECHANISM_TYPE -> supportedMechanisms: seq _CKS_MECHANISM_INFO -> Tot bool

let isMechanismUsedForGenerateKeyPair mechanism supportedMechanisms = 
  let mechanismInfo = _map_cks_mechanism_info_to_mechanism mechanism in 
  isBitFlagSet mechanismInfo.flags CKF_GENERATE_KEY_PAIR


(* This is an example of the implementation *)
val isMechanismUsedForSignaturePair: mechanism : _CK_MECHANISM_TYPE -> supportedMechanisms: seq _CKS_MECHANISM_INFO -> Tot bool

let isMechanismUsedForSignature mechanism supportedMechanisms = 
  let mechanismInfo = _map_cks_mechanism_info_to_mechanism mechanism in 
  isBitFlagSet mechanismInfo.flags CKF_SIGN


(* This is an example of the implementation *)
val isMechanismUsedForVerification: mechanism: _CK_MECHANISM_TYPE -> Tot bool

let isMechanismUsedForVerification mechanism =
  let mechanismInfo = _map_cks_mechanism_info_to_mechanism mechanism in 
  isBitFlagSet mechanismInfo.flags CKF_VERIFY



(* /* CK_OBJECT_CLASS is a value that identifies the classes (or
 * types) of objects that Cryptoki recognizes.  It is defined
 * as follows: */
typedef CK_ULONG          CK_OBJECT_CLASS; *) 
type _CK_OBJECT_HANDLE = _CK_ULONG


(*/* CK_SESSION_HANDLE is a Cryptoki-assigned value that
 * identifies a session */
typedef CK_ULONG          CK_SESSION_HANDLE;
*)
type _CK_SESSION_HANDLE = _CK_ULONG
	

(* by default all the attributes are read-only *)
let _ck_attribute_read_only: _CK_ATTRIBUTE_TYPE -> Tot bool = function
  |CKA_PRIVATE -> false
  |_ -> true




(* default attribute values *)
let defaultAttributes: seq _CK_ATTRIBUTE = Seq.empty


assume val attrributesConsistent: attrs: seq _CK_ATTRIBUTE -> Tot bool


val isContaining: #a: Type -> f: (a -> bool) -> s: seq a -> Tot (r: bool {r == true ==> 
  Hacl.PKCS11.Lib.contains f s})

let isContaining #a f s = 
  match find_l f s with 
  |Some _ -> lemmaFindLExistIfSome f s; true
  |_ -> false




(*  Takes one attribute and search for it in the attribute sequence. Returns true if found *)
(* Notion of being present: there exist an index n such that ... *)
(* Notion of not being present: forall elements not function*)



type _object = 
  |O: 
    attrs: seq _CK_ATTRIBUTE 
      {
	_attributesAllPresent attrs (getAttributesForTypeExtended CKO_OBJECT) 
	 (* /\
	attrributesConsistent attrs *)
      }  -> 
  _object


val getObjectAttributeClass: obj: _object -> Tot (r: _CK_ATTRIBUTE {r.aType == CKA_CLASS})

let getObjectAttributeClass obj = 
  let attributeClass = find_l (fun x -> x.aType = CKA_CLASS) obj.attrs in 
  lemma_index_0_elem #_CK_ATTRIBUTE_TYPE CKA_CLASS;
  lemmaFindLExistIfSomeOp (fun x -> x.aType = CKA_CLASS) obj.attrs; 
  match attributeClass with 
  Some a -> a


val getObjectAttributeLocal: obj: _object -> Tot (r: option _CK_ATTRIBUTE
  {
    Some? r ==>
      (
	let a = (match r with Some a -> a) in 
	a.aType == CKA_LOCAL
      )
  }
)

let getObjectAttributeLocal obj = 
  find_l (fun x -> x.aType = CKA_LOCAL) obj.attrs



type storage = 
  |Storage: sto: _object 
    {_attributesAllPresent sto.attrs (getAttributesForTypeExtended CKO_STORAGE)} -> storage


(* Key is an object such that the object has an attribute class such that the attribute value is OTP_KEY, PRIVATE KEY, PUBLIC KEY, or SECRET KEY *)
type key_object = 
  |Key: ko: storage{
    (
      let attrs = ko.sto.attrs in 
      _attributesAllPresent attrs (getAttributesForTypeExtended CKO_KEY)
    )
  } -> key_object


type _CKO_PUBLIC_KEY = 
  |PK: pko: key_object {
      (
	let attrs = pko.ko.sto.attrs in 
	_attributesAllPresent attrs (getAttributesForType CKO_PUBLIC_KEY)
      )
    } -> _CKO_PUBLIC_KEY


type _CKO_PRIVATE_KEY = 
  |PrK: prko : key_object {
    (
      let attrs = prko.ko.sto.attrs in 
      _attributesAllPresent attrs (getAttributesForType CKO_PRIVATE_KEY)
      ) 
   } -> _CKO_PRIVATE_KEY


type _CKO_SECRET_KEY = 
  |SK: sk: key_object {
    (
      let attrs = sk.ko.sto.attrs in 
      _attributesAllPresent attrs (getAttributesForType CKO_SECRET_KEY)
    )
  } -> _CKO_SECRET_KEY


type temporalStorage = 
  |Element: seq FStar.UInt8.t -> temporalStorage


(* This method takes a key and returns wther it's a secret key *)
val isKeySecretKey: k: key_object -> Tot bool

let isKeySecretKey k = 
  let attrs = k.ko.sto.attrs in 
  _attributesAllPresent attrs (getAttributesForType CKO_SECRET_KEY)


val isKeyPublicKey: k: key_object -> Tot bool

let isKeyPublicKey k = 
  let attrs = k.ko.sto.attrs in 
  _attributesAllPresent attrs (getAttributesForType CKO_PUBLIC_KEY)
  

val isKeyPrivateKey: k: key_object -> Tot bool

let isKeyPrivateKey k = 
  let attrs = k.ko.sto.attrs in 
  _attributesAllPresent attrs (getAttributesForType CKO_PRIVATE_KEY)


(* The method takes an object and returns whether it supports signing *)

val supportsSigning: key: key_object -> Tot Type0

let supportsSigning key = 
  let attrs = key.ko.sto.attrs in 
  (isKeySecretKey key \/ isKeyPrivateKey key) /\
  (
    let sign = find_l (fun x -> x.aType = CKA_SIGN) attrs in 
    assume (Some? sign);  
    match sign with |Some sign -> index sign.pValue 0 == true
  )


val supportsVerifying: key: key_object -> Tot Type0

let supportsVerifying key = 
  let attrs = key.ko.sto.attrs in 
  (isKeySecretKey key \/ isKeyPublicKey key) /\
  (
    let verify = find_l (fun x -> x.aType = CKA_VERIFY) attrs in 
    assume (Some? verify);  
    match verify with |Some verify -> index verify.pValue 0 == true
  )
  


(*  Takes one attribute and search for it in the attribute sequence. Returns true if found *)
(* Notion of being present: there exist an index n such that ... *)
(* Notion of not being present: forall elements not function*)

(* For being able to create a secret key, we need all the attributes to be given *)


val _CKO_SECRET_KEY_Constructor: attrs: seq _CK_ATTRIBUTE {
    let requiredAttributes = getAttributesForType CKO_SECRET_KEY in 
    _attributesAllPresent attrs requiredAttributes}
  -> Tot _CKO_SECRET_KEY

let _CKO_SECRET_KEY_Constructor attrs = 
  lemmaSecretKeyIsObject attrs;
  lemmaSecretKeyIsStorage attrs;
  lemmaSecretKeyIsKey attrs;
  SK (Key (Storage (O attrs)))


val castKeyToSecretKey: k: key_object {isKeySecretKey k} -> Tot _CKO_SECRET_KEY

let castKeyToSecretKey k = SK k


(*/* CK_MECHANISM is a structure that specifies a particular
 * mechanism  */
*)

type _CK_MECHANISM = 
  | Mechanism: mechanismID: _CK_MECHANISM_TYPE -> 
    pParameters: seq FStar.UInt8.t -> 
    _CK_MECHANISM


(* any attribute values contributed to the object by the object-creation function itself *)
let getAttributesByMechanism : _CK_MECHANISM_TYPE -> Tot (seq _CK_ATTRIBUTE_TYPE) = function
  |CKM_AES_KEY_GEN -> Seq.empty
  |_ -> Seq.empty

let getRequiredAttributesByMechanism: _CK_MECHANISM_TYPE 
  -> Tot (seq _CK_ATTRIBUTE_TYPE) = function
  |CKM_EC_KEY_PAIR_GEN -> seq_of_list [CKA_EC_PARAMS]
  |_ -> Seq.empty



type _SessionState = 
  |SubsessionSignatureInit
  |SubsessionSignatureUpdate
  |SubsessionVerificationInit
  |SubsessionVerificationUpdate


(* A metadata element represention an ongoing function *)
type subSession (k: seq key_object) (m: seq _CK_MECHANISM) (supMech: seq _CKS_MECHANISM_INFO) = 
  |Signature: 
    (* The session identifier that has caused the operation *)
    id: _CK_SESSION_HANDLE -> 
    (* The state of the ongoing session *)
    state: _SessionState {state = SubsessionSignatureInit \/ state = SubsessionSignatureUpdate} -> 
    (* The identifier of the mechanism used for the operation *)
    (* The mechanism requirements: present in the device and to be the signature algorithm *)
    pMechanism: _CK_MECHANISM_TYPE
      {exists (a: nat {a < Seq.length m}). let mechanism = Seq.index m a in mechanism.mechanismID = pMechanism /\ isMechanismUsedForSignature pMechanism supMech} ->
    (* The identifier of the key used for the operation *)
    (* The key requirement: present in the device and to be a signature key *)
    keyHandler: _CK_OBJECT_HANDLE{Seq.length k > keyHandler /\
      supportsSigning (index k keyHandler) 
    } -> 
    (* Temporal space for the signature *)
    temp: option temporalStorage -> subSession k m supMech
  |Verify : 	
    (* The session identifier that has caused the operation *)
    id: _CK_SESSION_HANDLE -> 
    (* The state of the ongoing session *)
    state: _SessionState {state = SubsessionVerificationInit \/ state = SubsessionVerificationUpdate} ->
    (* The identifier of the mechanism used for the operation *)
    (* The mechanism requirements: present in the device and to be the signature algorithm *)
    pMechanism: _CK_MECHANISM_TYPE
      {exists (a: nat {a < Seq.length m}). let mechanism = Seq.index m a in mechanism.mechanismID = pMechanism /\ isMechanismUsedForVerification pMechanism} ->
    (* The identifier of the key used for the operation *)
    (* The key requirement: present in the device and to be a signature key *)
    keyHandler: _CK_OBJECT_HANDLE {Seq.length k > keyHandler /\
	supportsVerifying (index k keyHandler)
    } -> 
    (* Temporal space for the verification *)
    temp: option temporalStorage -> subSession k m supMech


(* This method takes a subsession and returns the session identifier that created this session *)
val subSessionGetID: #ks: seq key_object -> #ms: seq _CK_MECHANISM -> #supMech: seq _CKS_MECHANISM_INFO -> s: subSession ks ms supMech -> Tot _CK_SESSION_HANDLE

let subSessionGetID #ks #ms #supMech  s = 
  match s with 
  |Signature a _ _ _ _ -> a 
  |Verify a _ _ _  _  -> a


(* This method takes a subsession and returns the session state *)
val subSessionGetState: #ks: seq key_object -> #ms : seq _CK_MECHANISM -> #supMech: seq _CKS_MECHANISM_INFO -> s: subSession ks ms supMech -> Tot _SessionState

let subSessionGetState #ks #ms #supMech s = 
  match s with
  | Signature _ b _ _ _ -> b
  | Verify _ b _ _ _  -> b


(* This method takes a subsession, a state to set and returns the subsession with updated state *)
val subSessionSetState: #ks: seq key_object-> #ms: seq _CK_MECHANISM -> #supMech: seq _CKS_MECHANISM_INFO -> s: subSession ks ms supMech -> state: _SessionState 
  {
    if Signature? s then state = SubsessionSignatureInit  \/ state = SubsessionSignatureUpdate 
    else 
      state = SubsessionVerificationInit \/ state = SubsessionVerificationUpdate} -> 
  Tot (r: subSession ks ms supMech
    (* The state is the one requested *)
    {
      subSessionGetState r = state /\ 
    (* The type did not change *)
      (if Signature? s then Signature? r else Verify? r) /\
    (* Nothing else got changed *)
      (match s with 
	|Signature a _ c d e ->
	  begin 
	    match r with 
	      |Signature a1 _ c1 d1 e1 -> a = a1 /\ c = c1 /\ d = d1 /\ e = e1
	  end	
	|Verify a _ c d e ->
	  begin match r with 
	    |Verify a1 _ c1 d1 e1 -> a = a1 /\ c = c1 /\ d = d1 /\ e = e1
	  end	
      )
    }
  )

let subSessionSetState #ks #ms #supMech s state = 
  match s with 
  |Signature a b c d e -> Signature a state c d e 
  |Verify a b c d e -> Verify a state c d e		


(* This method takes a subsession and returns its storage*)
val subSessionGetStorage: #ks: seq key_object-> #ms : seq _CK_MECHANISM -> #supMech: seq _CKS_MECHANISM_INFO -> s: subSession ks ms supMech ->  Tot (option temporalStorage)

let subSessionGetStorage #ks #ms #supMech s = 
  match s with 
  |Signature _ _ _ _ e -> e 
  |Verify _ _ _ _ e -> e


(* This method takes a subsession, a storage to set and returns *)
val subSessionSetStorage: #ks: seq key_object -> #ms: seq _CK_MECHANISM -> #supMech: seq _CKS_MECHANISM_INFO -> s: subSession ks ms supMech -> storage: option temporalStorage -> 
  Tot (r: subSession ks ms supMech
    {
      (* The storage is the one requested *)
      subSessionGetStorage r = storage /\
      (* The type did not change  *)
      (if Signature? s then Signature? r else Verify? r) /\
      (* Nothing else changed *)
      (match s with 
	|Signature a b c d _ ->
	  begin match r with 
	    |Signature a1 b1 c1 d1 _ -> a = a1 /\ b = b1 /\ c = c1 /\ d = d1 
	  end	
	|Verify a b c d _ ->
	  begin match r with 
	    |Verify a1 b1 c1 d1 _ -> a = a1 /\b = b1 /\ c = c1 /\ d = d1 
	  end
      )
    }
  )

let subSessionSetStorage #ks #ms #supMech s storage = 
  match s with 
  |Signature a b c d _ -> Signature a b c d storage
  |Verify a b c d _ -> Verify a b c d storage


(* This method takes a subsession and returns the mechanism used for this subsession *)
val subSessionGetMechanism: #ks: seq key_object -> #ms: seq _CK_MECHANISM -> #supMech: seq _CKS_MECHANISM_INFO -> s: subSession ks ms supMech -> Tot _CK_MECHANISM_TYPE

let subSessionGetMechanism #ks #ms #supMech s = 
  match s with 
  |Signature _ _  c _ _ -> c
  |Verify _ _ c _ _ -> c


(* This method takes a subsession and returns the key handler used for this subsession *)
val subSessionGetKeyHandler: #ks: seq key_object -> #ms: seq _CK_MECHANISM -> #supMech: seq _CKS_MECHANISM_INFO -> s: subSession ks ms supMech -> Tot _CK_OBJECT_HANDLE

let subSessionGetKeyHandler #ks #ms #supMech s = 
  match s with 
  |Signature _ _ _ d _ -> d 
  |Verify _ _ _ d _ -> d


type device = 
  |Device: 
    keys: seq key_object {Seq.length keys < pow2 32} ->
    mechanisms: seq _CK_MECHANISM  -> 
    supportedMechanisms: seq _CKS_MECHANISM_INFO -> 
    objects: seq _object -> 
    subSessions: seq (subSession keys mechanisms supportedMechanisms) -> 
  device

(*
/* CK_RV is a value that identifies the return value of a
 * Cryptoki function */
*)

(* The exception type represents all the results except CKR_OK*)

type exception_t = 
  | CKR_ARGUMENTS_BAD 
  | CKR_ATTRIBUTE_READ_ONLY 
  | CKR_ATTRIBUTE_TYPE_INVALID
  | CKR_ATTRIBUTE_VALUE_INVALID 
  | CKR_CRYPTOKI_NOT_INITIALIZED 
  | CKR_CURVE_NOT_SUPPORTED
  | CKR_DEVICE_ERROR 
  | CKR_DEVICE_MEMORY 
  | CKR_DEVICE_REMOVED 
  | CKR_FUNCTION_CANCELED 
  | CKR_FUNCTION_FAILED 
  | CKR_GENERAL_ERROR 
  | CKR_HOST_MEMORY 
  | CKR_MECHANISM_INVALID 
  | CKR_MECHANISM_PARAM_INVALID 
  | CKR_OPERATION_ACTIVE 
  | CKR_PIN_EXPIRED 
  | CKR_SESSION_CLOSED 
  | CKR_SESSION_HANDLE_INVALID 
  | CKR_SESSION_READ_ONLY 
  | CKR_TEMPLATE_INCOMPLETE 
  | CKR_TEMPLATE_INCONSISTENT 
  | CKR_TOKEN_WRITE_PROTECTED 
  | CKR_USER_NOT_LOGGED_IN


type result 'a = either 'a exception_t


val isPresentOnDevice_: d: device -> pMechanism: _CK_MECHANISM_TYPE -> counter: nat {counter < Seq.length d.mechanisms} -> 
  Tot (r: bool 
    {
      r ==> (exists (a: nat {a < Seq.length d.mechanisms}). 
	let m = Seq.index d.mechanisms a in 
	m.mechanismID = pMechanism)
    }
  )
  (decreases (length d.mechanisms - counter))

let rec isPresentOnDevice_ d pMechanism counter = 
  let m = index d.mechanisms counter in 
  if m.mechanismID = pMechanism then 
     true 
  else if counter = length d.mechanisms - 1 
    then false
  else 
    isPresentOnDevice_ d pMechanism (counter + 1)


val lemma_isPresentOnDevice_aux: s: seq _CK_MECHANISM -> f: (_CK_MECHANISM -> Tot bool) ->
  Lemma
    (requires 
      (exists (a: nat {a < length s}). f (index s a)) /\ not (f (head s)))
    (ensures 
      exists (a: nat {a < length (tail s)}). f (index (tail s) a))
  (decreases (length s))

let rec lemma_isPresentOnDevice_aux s f = 
  if length s = 0 then ()
  else 
    begin
      assert(not (f (head s)));
      admit();
      lemma_isPresentOnDevice_aux (tail s) f
    end


val lemma_isPresentOnDevice: s: seq _CK_MECHANISM -> f: (_CK_MECHANISM -> Tot bool) -> Lemma 
  (requires 
    (exists (a: nat {a < length s}). f (index s a)))
  (ensures
    (contains f s))
  (decreases (length s))

let rec lemma_isPresentOnDevice s f = 
  if Seq.length s = 0 then ()
  else
    if f (head s) then ()
    else 
      begin
	lemma_isPresentOnDevice_aux s f;
	lemma_isPresentOnDevice (tail s) f
      end

val isPresentOnDevice: d: device -> pMechanism: _CK_MECHANISM_TYPE -> 
  Tot (r: bool
    {r = true ==>
      (exists (a: nat{a < Seq.length d.mechanisms}). let m = Seq.index d.mechanisms a in m.mechanismID = pMechanism) /\ 
      (contains (fun x -> x.mechanismID = pMechanism) d.mechanisms)
    }
  )

let isPresentOnDevice d pMechanism =
  if Seq.length d.mechanisms = 0 
    then false 
  else
    let r = isPresentOnDevice_ d pMechanism 0 in 
    if r = true then begin
      lemma_isPresentOnDevice (d.mechanisms) (fun x -> x.mechanismID = pMechanism);
      true
      end
    else 
      false	  


val mechanismGetFromDevice: d: device -> 
  pMechanism: _CK_MECHANISM_TYPE{isPresentOnDevice d pMechanism = true} -> 
  Tot (m: _CK_MECHANISM {m.mechanismID = pMechanism})

let mechanismGetFromDevice d pMechanism = 
  let m = find_l (fun x -> x.mechanismID = pMechanism) d.mechanisms in 
  match m with 
  Some m -> m


assume val checkedAttributes: pTemplate : seq _CK_ATTRIBUTE -> Tot bool


(* compares two sessions -> The sessions are equal iff the elements are equal. 
Important, if the list of the key got changed, you can still assess whether the sessions are equal, i.e. it is NOT dependent on the keys, mechanisms, supportedMechanisms etc. At the same time, you can't update a session if the key is not in the key list anymore
*)
val sessionEqual: #ks: seq key_object -> #ms: seq _CK_MECHANISM -> #supM: seq _CKS_MECHANISM_INFO -> 
  #ks1: seq key_object -> #ms1 : seq _CK_MECHANISM -> #supM1: seq _CKS_MECHANISM_INFO -> 
  s: subSession ks ms supM -> s1 : subSession ks1 ms1 supM1 -> Tot Type0

let sessionEqual #ks #ms #supM  #ks1 #ms1 #supM1 s s1 = 
  match s with 
    |Signature a b c d e -> 
      begin 
	match s1 with 
	  |Signature a1 b1 c1 d1 e1 ->  ms == ms1 /\ supM == supM1 /\ a == a1 /\ b == b1 /\ c == c1 /\ d == d1 /\ e == e1
	  | _ -> False
      end
    |Verify a b c d e -> 	
      begin 
	match s1 with
	  | Verify a1 b1 c1 d1 e1 ->  ms == ms1 /\ supM == supM1 /\ a == a1 /\ b == b1 /\ c == c1 /\ d == d1 /\ e == e1
	  | _ -> False
      end	


(* This method recreated the session with the same parameters and dependecies, but with different list of the keys *)

val updateSession_: d: device -> 
  s: subSession d.keys d.mechanisms d.supportedMechanisms ->
  ks: seq key_object {Seq.length ks >= Seq.length d.keys /\
    (
      let keyReferenceUsedForOperation = subSessionGetKeyHandler s in 
      let keyUsedForOperation = index d.keys keyReferenceUsedForOperation in 
      let keyInNewKeySet = index ks keyReferenceUsedForOperation in 
      keyUsedForOperation == keyInNewKeySet
    )
   } ->
  ms: seq _CK_MECHANISM{ms == d.mechanisms} -> 
  supM: seq _CKS_MECHANISM_INFO {supM == d.supportedMechanisms} -> 
  Tot (r: subSession ks ms supM
    {Signature? s ==> Signature? r /\ Verify? s ==> Verify? r /\ sessionEqual s r })	

let updateSession_ d s ks ms supM = 
  match s with 
  | Signature a b c d e -> 
    let (a: subSession ks ms supM) = Signature a b c d e in a
  | Verify a b c d e -> 
    let (a: subSession ks ms supM) = Verify a b c d e in a	


(* This method takes all the sessions and updates key set for them *)
val _updateSession: d: device ->  ks: seq key_object -> 
  ms: seq _CK_MECHANISM{ms == d.mechanisms} -> 
  supM: seq _CKS_MECHANISM_INFO {supM == d.supportedMechanisms} -> 
  sessions: seq (subSession d.keys d.mechanisms d.supportedMechanisms)
  {
    Seq.length ks >= Seq.length d.keys /\ 
    (
      forall (i: nat {i < Seq.length sessions}). 
	let referencedSession = index sessions i in 
	let keyReferenceUsedForOperation = subSessionGetKeyHandler referencedSession in 
	let keyUsedForOperation = index d.keys keyReferenceUsedForOperation in 
	let keyInNewKeySet = index ks keyReferenceUsedForOperation in 
	keyUsedForOperation == keyInNewKeySet
    )
  } ->
  counter: nat {counter < Seq.length sessions}->
  updatedSessions: seq (subSession ks ms supM) 
  {
    Seq.length updatedSessions = counter /\
    (
      forall (i: nat {i < Seq.length updatedSessions}). (sessionEqual (index sessions i) (index updatedSessions i))
    )
  } -> 
  Tot (
    newSessions: seq (subSession ks ms supM)
    {
      Seq.length sessions = Seq.length newSessions /\
      (forall (i: nat{i < Seq.length sessions}). sessionEqual (index sessions i) (index newSessions i))
    }
  )
  (decreases (Seq.length sessions - Seq.length updatedSessions))

let rec _updateSession d ks ms supM sessions counter alreadySeq = 
  let element = Seq.index sessions counter in 
  let updatedElement = updateSession_ d element ks ms supM in 
  let updatedSeq = Seq.append alreadySeq (Seq.create 1 updatedElement) in 
  if Seq.length sessions = Seq.length updatedSeq	then 
    updatedSeq 
  else 
    _updateSession d ks ms supM sessions (counter + 1) updatedSeq	


val updateSession: d: device -> ks: seq key_object -> 
  ms: seq _CK_MECHANISM{ms == d.mechanisms} -> 
  supM: seq _CKS_MECHANISM_INFO {supM == d.supportedMechanisms} -> 
  sessions: seq (subSession d.keys d.mechanisms d.supportedMechanisms)
  {
    Seq.length ks >= Seq.length d.keys /\ 
    (
      forall (i: nat {i < Seq.length sessions}). 
	let referencedSession = index sessions i in 
	let keyReferenceUsedForOperation = subSessionGetKeyHandler referencedSession in 
	let keyUsedForOperation = index d.keys keyReferenceUsedForOperation in 
	let keyInNewKeySet = index ks keyReferenceUsedForOperation in 
	keyUsedForOperation == keyInNewKeySet
    )
  }  ->
  Tot (newSessions: (seq (subSession ks ms supM))
    {
      Seq.length sessions = Seq.length newSessions /\ 
      
      (forall (i: nat{i < Seq.length sessions}). sessionEqual (index sessions i) (index newSessions i))
    }
  )
 
let updateSession d ks ms supM sessions = 
  if Seq.length sessions = 0 then 
    Seq.empty
  else	
    _updateSession d ks ms supM sessions 0 Seq.empty


(** Modifies Section **)

(* There was only one key changed in the device, that the handler of the key is i. Nothing else changed. M stands for the number of keys increased*)
val modifiesKeysM: dBefore: device -> 
  dAfter: device
    {
      Seq.length dBefore.keys + 1 = Seq.length dAfter.keys /\ 
      Seq.length dBefore.subSessions = Seq.length dAfter.subSessions
    } -> 
  i: _CK_OBJECT_HANDLE{i < Seq.length dAfter.keys} -> Tot Type0

let modifiesKeysM dBefore dAfter i = 
  let mechanismsPrevious, keysPrevious, objectsPrevious, supportedMechanismsPrevious = dBefore.mechanisms, dBefore.keys, dBefore.objects, dBefore.supportedMechanisms in 
  let mechanismsNew, keysNew, objectsNew, supportedMechanismsNew = dAfter.mechanisms, dAfter.keys, dAfter.objects, dAfter.supportedMechanisms in 
  
  let keysBeforeA, keysBeforeB = Seq.split dBefore.keys i in 
  let keysAfterA, key_keysAfterB = Seq.split dAfter.keys i in 	
  let key, keysAfterB = Seq.split key_keysAfterB 1 in 

  mechanismsPrevious == mechanismsNew /\
  objectsPrevious == objectsNew /\
  supportedMechanismsPrevious == supportedMechanismsNew /\

  keysBeforeA == keysAfterA /\ keysBeforeB = keysAfterB /\
  
  (forall (i: nat{i < Seq.length dBefore.subSessions}). sessionEqual (index dBefore.subSessions i) (index dAfter.subSessions i))


(* 
   There was only one session changed in the device, the index of the session is i. Nothing else changed. 
*)

val modifiesSessionsM: dBefore: device -> 
  dAfter: device{Seq.length dBefore.subSessions = Seq.length dAfter.subSessions +1} -> 
  i: nat{i < Seq.length dBefore.subSessions} -> Tot Type0

let modifiesSessionsM dBefore dAfter i = 
  let mechanismsPrevious, keysPrevious, objectsPrevious, supportedMechanismsPrevious = dBefore.mechanisms, dBefore.keys, dBefore.objects, dBefore.supportedMechanisms in 
  let mechanismsNew, keysNew, objectsNew, supportedMechanismsNew = dAfter.mechanisms, dAfter.keys, dAfter.objects, dAfter.supportedMechanisms in 
  
  let sessionsBeforeA, session_sessionBeforeB = Seq.split dBefore.subSessions i in 
  let _, sessionsBeforeB = Seq.split session_sessionBeforeB 1 in 
  let sessionsAfterA, sessionsAfterB = Seq.split dAfter.subSessions i in 
	
  mechanismsPrevious == mechanismsNew /\
  keysPrevious == keysNew /\ 
  objectsPrevious == objectsNew /\
  supportedMechanismsPrevious == supportedMechanismsNew /\

  (forall (i: nat{i < Seq.length sessionsBeforeA}). sessionEqual (index sessionsBeforeA i) (index sessionsAfterA i))/\
  (forall (i: nat{i < Seq.length sessionsBeforeB}). sessionEqual (index sessionsBeforeB i) (index sessionsAfterB i))


(* There was only one session changed changed, the handler of the session is i *)
(*
   E stands for the same number of elements as it was before
*)

val modifiesSessionsE: dBefore: device -> 
  dAfter: device{Seq.length dBefore.subSessions = Seq.length dAfter.subSessions} ->
  i: nat {i < Seq.length dBefore.subSessions} -> Tot Type0

let modifiesSessionsE dBefore dAfter i = 
  let mechanismsPrevious, keysPrevious, objectsPrevious, supportedMechanismsPrevious = dBefore.mechanisms, dBefore.keys, dBefore.objects, dBefore.supportedMechanisms in 
  let mechanismsNew, keysNew, objectsNew, supportedMechanismsNew = dAfter.mechanisms, dAfter.keys, dAfter.objects, dAfter.supportedMechanisms in 
  
  let sessionsBeforeA, session_sessionBeforeB = Seq.split dBefore.subSessions i in 
  let _, sessionsBeforeB = Seq.split session_sessionBeforeB 1 in 
  let sessionsAfterA, session_sessionAfterB = Seq.split dBefore.subSessions i in 
  let _, sessionsAfterB = Seq.split session_sessionBeforeB 1 in 

  mechanismsPrevious == mechanismsNew /\
  keysPrevious == keysNew /\
  objectsPrevious == objectsNew /\
  supportedMechanismsPrevious == supportedMechanismsNew /\

  (forall (i: nat{i < Seq.length sessionsBeforeA}). sessionEqual (index sessionsBeforeA i) (index sessionsAfterA i))/\
  (forall (i: nat{i < Seq.length sessionsBeforeB}). sessionEqual (index sessionsBeforeB i) (index sessionsAfterB i))


(* This method takes a device, a new key to add and returns a new device with this key inside and the handler of the key.
   Postconditions: 
     the number of the keys increased by one;
     the handler is less than the length of the key storage
     the getter with the handler returns the same object as it was requested to add
     nothing except the key[handler] changed

NB: the key is added to the end of the list
*)
val deviceUpdateKey: d: device {Seq.length d.keys < pow2 32 - 1} -> newKey: key_object ->
  Tot (resultDevice: device
    {
      Seq.length resultDevice.keys = Seq.length d.keys + 1 /\
      Seq.length d.subSessions = Seq.length resultDevice.subSessions
    } &
    (handler: _CK_OBJECT_HANDLE
      {
	handler < Seq.length resultDevice.keys /\ 
	Seq.index resultDevice.keys handler = newKey /\
	modifiesKeysM d resultDevice handler
      }
    )
  )

let deviceUpdateKey d newKey = 
  let mechanismsPrevious, keysPrevious, objectsPrevious, supportedMechanismsPrevious = d.mechanisms, d.keys, d.objects, d.supportedMechanisms in 
  
  let newKey = Seq.create 1 newKey in 
  let keysNew = Seq.append keysPrevious newKey in
  let handler = Seq.length keysNew - 1 in 
    lemma_append keysPrevious newKey;
  let sessionsUpdated = updateSession d keysNew mechanismsPrevious supportedMechanismsPrevious d.subSessions in
  let resultDevice = Device keysNew mechanismsPrevious supportedMechanismsPrevious objectsPrevious sessionsUpdated in 
  admit();
  (|resultDevice, handler|)


(* This method takes a device, a function f and deletes all the elements that satisfy that function *)

(* I left the atomic delete, i.e. not to be able to delete several things at the same time *)

val deviceRemoveSession: #ks: seq key_object -> #ms: seq _CK_MECHANISM -> #supM: seq _CKS_MECHANISM_INFO -> 
  hSession : _CK_SESSION_HANDLE -> 
  f: (#ks: seq key_object -> #ms: seq _CK_MECHANISM -> #supM: seq _CKS_MECHANISM_INFO ->  subSession ks ms supM -> bool) -> 
  d: device{count f d.subSessions = 1} ->
  Tot (resultDevice: device
    {
      count f resultDevice.subSessions  = 0 /\
      Seq.length d.subSessions = Seq.length resultDevice.subSessions + 1 /\
      (
	let indexOfSessionToDelete = seq_getIndex2 f d.subSessions in 
	modifiesSessionsM d resultDevice indexOfSessionToDelete
      )
    }
  )	

let deviceRemoveSession #ks #ms #supM hSession f d = 
  let mechanismsPrevious, keysPrevious, objectsPrevious, supportedMechanismsPrevious = d.mechanisms, d.keys, d.objects, d.supportedMechanisms in 
  
  let previousSessions = d.subSessions in 
  let sessionsNew = seq_remove previousSessions f in 
    seq_remove_lemma_count_of_deleted previousSessions f;
    
  let newDevice = Device keysPrevious mechanismsPrevious supportedMechanismsPrevious objectsPrevious sessionsNew in 
    seq_remove_unchanged previousSessions f;	
  newDevice

(* This method takes a session satisfying the function f and change its status to updated, for both, signature and verification subsessions *)

val deviceUpdateSessionChangeStatusToUpdated: #ks : seq key_object -> #ms : seq _CK_MECHANISM -> #supM: seq _CKS_MECHANISM_INFO -> 
  f: (#ks: seq key_object -> #ms: seq _CK_MECHANISM -> #supM : seq _CKS_MECHANISM_INFO -> subSession ks ms supM -> bool)
    {
      forall (ks1:seq key_object) (ms1: seq _CK_MECHANISM) (ks2: seq key_object) (ms2: seq _CK_MECHANISM) (supM1: seq _CKS_MECHANISM_INFO) (supM2: seq _CKS_MECHANISM_INFO) (s: subSession ks1 ms1 supM1) (s2: subSession ks2 ms2 supM2). (Signature? s == Signature? s2 \/ Verify? s == Verify? s2) /\ subSessionGetID s == subSessionGetID s2 ==> f s == f s2
    } ->
  d: device {count (f #d.keys) d.subSessions = 1}  -> 
  Tot (resultDevice: device
   { 
      let session = find_l (f #resultDevice.keys) resultDevice.subSessions in 
      count (f #resultDevice.keys) resultDevice.subSessions = 1 /\ 
      Seq.length resultDevice.subSessions = Seq.length d.subSessions /\
      (
	let sessionIndex = seq_getIndex2 (f #d.keys) d.subSessions  in 
	countMore0IsSome resultDevice.subSessions (f #resultDevice.keys);
	let s = match session with Some a -> a in 
	let previousSessions = d.subSessions in 
	let previousSession = find_l (f #d.keys)  previousSessions in 
	countMore0IsSome previousSessions (f #d.keys);
	let previousSession = match previousSession with Some a -> a in 
	
	subSessionGetState s == 
	  (match s with 
	    |Signature _ _ _ _ _ -> SubsessionSignatureUpdate 
	    |Verify _ _ _ _ _ -> SubsessionVerificationUpdate
	  ) /\ 
	subSessionGetStorage s == subSessionGetStorage previousSession /\
	subSessionGetMechanism s == subSessionGetMechanism previousSession /\
	subSessionGetKeyHandler s == subSessionGetKeyHandler previousSession /\
	modifiesSessionsE d resultDevice sessionIndex
      ) 
    }
  )	

let deviceUpdateSessionChangeStatusToUpdated #ks #ms #supM f d = 
  let mechanismsPrevious, keysPrevious, objectsPrevious, supportedMechanismsPrevious = d.mechanisms, d.keys, d.objects, d.supportedMechanisms in 

  let sessionsPrevious = d.subSessions in 
  let sessionsToChange = find_l (f #d.keys) sessionsPrevious in 
    countMore0IsSome sessionsPrevious (f #d.keys);

  let sessionToChange = match sessionsToChange with |Some a -> a in 
  let sessionChanged = subSessionSetState sessionToChange 
    (match sessionToChange with 
      |Signature _ _ _ _ _ -> SubsessionSignatureUpdate 
      |Verify _ _ _ _ _  -> SubsessionVerificationUpdate
    ) in 

  assert(Signature? sessionToChange == Signature? sessionChanged);
  
  let sessionChanged = Seq.create 1 sessionChanged in  

  let sessionsNew = seq_remove sessionsPrevious (f #keysPrevious #mechanismsPrevious #supportedMechanismsPrevious) in 
    seq_remove_lemma_count_of_deleted sessionsPrevious (f #keysPrevious);
  let sessionsUpdated = Seq.append sessionChanged sessionsNew in 
    lemma_append_count_aux2 (f #keysPrevious) sessionChanged sessionsNew;
  
  let newDevice = Device keysPrevious mechanismsPrevious supportedMechanismsPrevious objectsPrevious sessionsUpdated in 
  newDevice


val deviceUpdateSessionChangeStorage: #ks : seq key_object -> #ms : seq _CK_MECHANISM -> #supM: seq _CKS_MECHANISM_INFO -> 
  f: (#ks: seq key_object -> #ms: seq _CK_MECHANISM -> #supM : seq _CKS_MECHANISM_INFO -> subSession ks ms supM -> bool)
    {
      forall (ks1:seq key_object) (ms1: seq _CK_MECHANISM) (ks2: seq key_object) (ms2: seq _CK_MECHANISM) (supM1: seq _CKS_MECHANISM_INFO) (supM2: seq _CKS_MECHANISM_INFO) (s: subSession ks1 ms1 supM1) (s2: subSession ks2 ms2 supM2). (Signature? s == Signature? s2 \/ Verify? s == Verify? s2) /\ subSessionGetID s == subSessionGetID s2 ==> f s == f s2
    } -> 
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

let deviceUpdateSessionChangeStorage #ks #ms #supM f d storage = 
  let mechanismsPrevious, keysPrevious, objectsPrevious, supportedMechanismsPrevious = d.mechanisms, d.keys, d.objects, d.supportedMechanisms in 

  let sessionsPrevious = d.subSessions in 
  
  let sessionToChange = find_l (f #d.keys) sessionsPrevious in 
    countMore0IsSome sessionsPrevious (f #d.keys #d.mechanisms);
  let sessionToChange = match sessionToChange with | Some a -> a in 
  let sessionChanged = subSessionSetStorage sessionToChange (Some storage) in 
    assert(Signature? sessionToChange == Signature? sessionChanged);

  let sessionChanged = Seq.create 1 sessionChanged in 
  let sessionsNew = seq_remove sessionsPrevious (f #keysPrevious #mechanismsPrevious #supportedMechanismsPrevious) in
    seq_remove_lemma_count_of_deleted sessionsPrevious (f #keysPrevious);
  let sessionsUpdated = Seq.append sessionChanged sessionsNew in 
    lemma_append_count_aux2 (f #keysPrevious #mechanismsPrevious) sessionChanged sessionsNew;
  let newDevice = Device keysPrevious mechanismsPrevious supportedMechanismsPrevious objectsPrevious  sessionsUpdated in 
    newDevice


assume val lemma_count: #ks: seq key_object -> #ms: seq _CK_MECHANISM -> #supM: seq _CKS_MECHANISM_INFO -> 
  #ks1 : seq key_object -> #ms1 : seq _CK_MECHANISM -> #supM1: seq _CKS_MECHANISM_INFO -> 
  s: seq (subSession ks ms supM) -> s1: seq (subSession ks1 ms1 supM1)
    {Seq.length s = Seq.length s1} -> 
  f: (subSession ks ms supM -> bool) -> f1: (subSession ks1 ms1 supM1 -> bool) -> 
  Lemma
    (requires (forall (i: nat{i < Seq.length s}). sessionEqual (index s i) (index s1 i)))
    (ensures (count f s = count f1 s1))

(* The size should be checked *)

val deviceAddKey: d: device -> key: key_object -> Tot ((resultDevice: device) & (handler: _CK_OBJECT_HANDLE))

let deviceAddKey d key = 
  let keysUpdated = snoc d.keys key in 
  let handler = length keysUpdated in 
  let updatedDevice = Device keysUpdated d.mechanisms d.supportedMechanisms d.objects d.subSessions in 
  (|updatedDevice,  handler|)


val deviceAddSession: f: (#ks: seq key_object -> #ms: seq _CK_MECHANISM -> #supM: seq _CKS_MECHANISM_INFO -> subSession ks ms supM -> bool) -> 
  d: device{count f d.subSessions = 0} -> 
  sessionToAdd: subSession d.keys d.mechanisms d.supportedMechanisms {f sessionToAdd = true} -> 
  Tot (resultDevice: device
    {
      ( 
	count f resultDevice.subSessions = 1 /\ 
	Seq.length d.subSessions + 1 = Seq.length resultDevice.subSessions  /\ 
	(
	  let sessionIndex = seq_getIndex2 f resultDevice.subSessions in 
	  modifiesSessionsM resultDevice d sessionIndex /\
	  (
	    let newSession = updateSession_ d sessionToAdd resultDevice.keys resultDevice.mechanisms in 
	    Seq.count sessionToAdd resultDevice.subSessions = 1 /\
	    seq_getIndex resultDevice.subSessions sessionToAdd == seq_getIndex2 f resultDevice.subSessions 
	  )
	)
      )	
    }
  )

let deviceAddSession  f d newSession = 
  countFCount f d.subSessions newSession;
   
  let mechanismsPrevious, keysPrevious, objectsPrevious, supportedMechanismsPrevious = d.mechanisms, d.keys, d.objects, d.supportedMechanisms in 
  
  let sessions = d.subSessions in 
  let sessions = updateSession d keysPrevious mechanismsPrevious supportedMechanismsPrevious sessions in 
  
  lemma_count #d.keys #d.mechanisms #d.supportedMechanisms #keysPrevious #mechanismsPrevious d.subSessions sessions (f #d.keys #d.mechanisms) (f #keysPrevious #mechanismsPrevious #supportedMechanismsPrevious);
  
  let newSessionUpd = updateSession_ d newSession d.keys d.mechanisms d.supportedMechanisms in 
  let newElement = Seq.create 1 newSessionUpd in 
  let sessions_upd = append sessions newElement in
    countFCount (f #keysPrevious) sessions newSessionUpd;
    lemma_append_count_aux newSessionUpd sessions newElement;
    lemma_append_count_aux2 (f #keysPrevious) sessions newElement;	
  
  let updatedDevice = Device keysPrevious mechanismsPrevious supportedMechanismsPrevious objectsPrevious sessions_upd in 
    lemma_getIndex newSessionUpd sessions;
    lemma_getIndex2 f sessions newSessionUpd;
  updatedDevice

(*
   Preconditions: the mechanism should be used for key generation.
   CheckedAttributes: (4.1.1):
     1) Not type invalid (parsing)
     2) Not value invalid (parsing)
     3) Not read only 
     4) Not incomplete -> fully specify object?
     5) Incosistent: 
       two difference values for the sae attribute
       attributes for public/private keys instead of secret keys
       one attribute - one value
*)


(* If the supplied template specifies a value for a read-only attribute, then the attempt should fail with the error code CKR_ATTRIBUTE_READ_ONLY.  Whether or not a given Cryptoki attribute is read-only is explicitly stated in the Cryptoki specification; however, a particular library and token may be even more restrictive than Cryptoki specifies *)

val attributeIsReadOnly: _CK_ATTRIBUTE -> Tot bool 

let attributeIsReadOnly a = 
    not (_ck_attribute_read_only a.aType)


val attributesNotReadOnly: seq _CK_ATTRIBUTE -> Tot bool

let attributesNotReadOnly s = 
  for_all (fun x -> attributeIsReadOnly x) s


(* If the attribute values in the supplied template, together with any default attribute values and any attribute values contributed to the object by the object-creation function itself, are insufficient to fully specify the object to create, then the attempt should fail with the error code CKR_TEMPLATE_INCOMPLETE. *)

(* Takes one attribute and search for it in the attribute sequence. Returns true if found *)

val __attributesTemplateComplete: toSearchSequence: seq _CK_ATTRIBUTE -> toFind: _CK_ATTRIBUTE_TYPE -> Tot bool

let __attributesTemplateComplete toSearchSequence toFind = 
  match find_l (fun x -> x.aType = toFind) toSearchSequence with 
  |None -> false
  |Some _ -> true

(* The function searches for all the attributes in the sequence  *)
val _attributesTemplateComplete: toSearchSequence: seq _CK_ATTRIBUTE -> toFinds: seq _CK_ATTRIBUTE_TYPE -> Tot bool

let _attributesTemplateComplete toSearchSequence toFinds = 
  for_all (__attributesTemplateComplete toSearchSequence) toFinds 


val combineAllProvidedAttributes: 
  mechanism: _CK_MECHANISM_TYPE 
  -> attrs: seq _CK_ATTRIBUTE 
  -> Tot (seq _CK_ATTRIBUTE)

let combineAllProvidedAttributes mechanism attrs  = 
  let defAttr = defaultAttributes in 
  let mechanismAttributes = getAttributesByMechanism mechanism in 
  append (append defaultAttributes mechanismAttributes) attrs


val combineAllRequiredAttributes: 
  mechanism: _CK_MECHANISM_TYPE 
  -> t: _CK_OBJECT_CLASS 
  -> Tot (seq _CK_ATTRIBUTE)

let combineAllRequiredAttributes mechanism t = 


val attributesTemplateComplete: 
  t: _CK_OBJECT_CLASS 
  ->  mechanism: _CK_MECHANISM 
  -> attrs: seq _CK_ATTRIBUTE 
  -> Tot bool

let attributesTemplateComplete t mechanism attrs = 
  let allAttributes = combineAllProvidedAttributes mechanism.mechanismID attrs in 
  let getRequiredAttributes = getAttributesForType t in 
  _attributesTemplateComplete allAttributes getRequiredAttributes

(* If the attribute values in the supplied template, together with any default attribute values and any attribute values contributed to the object by the object-creation function itself, are inconsistent, then the attempt should fail with the error code CKR_TEMPLATE_INCONSISTENT.   *)
  
(*One example of an inconsistent template would be using a template which specifies two different values for the same attribute.   *)

val _attributesTemplateConsistent0: attrs: seq _CK_ATTRIBUTE -> Tot bool
  (decreases (length attrs))

let rec _attributesTemplateConsistent0 attrs = 
  match length attrs with 
  | 0 -> true
  | 1 -> true
  | _ -> 
    let typeOfAttribute = (head attrs).aType in 
    let r = find_l (fun x -> x.aType = typeOfAttribute) (tail attrs) in 
    match r with 
      |Some _ -> false
      |None -> _attributesTemplateConsistent0 (tail attrs)
  
  
val attributesTemplateConsistent0: attrs: seq _CK_ATTRIBUTE -> Tot bool

let attributesTemplateConsistent0 attrs = 
  _attributesTemplateConsistent0 attrs


(* Mechanism Select *)

val getCurveFromEncoded: s: seq _CK_ULONG -> option _HACL_Curve_ID

let getCurveFromEncoded s = 
  let curve25519Representation = FStar.Seq.Properties.seq_of_list [0] in 
  let curveP256Represtantation = FStar.Seq.Properties.seq_of_list [1] in
  match s with 
  |curve25519Representation -> Some Curve25519
  |curveP256Representation -> Some CurveP256
  |_ -> None


val mechanismSelectECDSA: a: _CK_ATTRIBUTE {CKA_EC_PARAMS? a.aType} -> option (unit -> Tot (seq FStar.UInt8.t))

let mechanismSelectECDSA a = 
  let open Hacl.PKCS11.External in 
  let encodedCurve = a.pValue in 
  let curveIdentifier = getCurveFromEncoded encodedCurve in 
  match curveIdentifier with 
  |Some id -> 
    match id with 
    |Curve25519 -> Some keyGenerationTemplateCurve25519 
    |CurveP256 -> Some keyGenerationTemplateP256
  | _ -> None


val mechanismCreationSelect: d: device 
  -> pMechanism: _CK_MECHANISM 
  -> attrs: seq _CK_ATTRIBUTE {attributesTemplateComplete CKO_SECRET_KEY pMechanism attrs}
  ->  result (unit -> Tot (seq FStar.UInt8.t))


let mechanismCreationSelect d m attrs = 
  let mechanismType = m.mechanismID in
  match mechanismType with 
  |CKM_EC_KEY_PAIR_GEN -> 
    begin
      let requiredAttribute = find_l (fun x -> x.aType = CKA_EC_PARAMS) attrs in 
      assume (Some? requiredAttribute);
      let requiredAttribute = match requiredAttribute with Some a -> a in 
      let mechanism = mechanismSelectECDSA requiredAttribute in 
      match mechanism with 
      |None -> Inr CKR_DEVICE_ERROR
      |Some a -> Inl a 
    end
  | _ -> Inr CKR_MECHANISM_INVALID
    

(* This function takes all the provided attributes (the mechanism attributes, provided attributes and default one) and return the sequence of attributes that are required to construct the type *)

val _getRequiredAttributes: attrs: seq _CK_ATTRIBUTE -> typeToReturn: _CK_ATTRIBUTE_TYPE -> Tot (a: _CK_ATTRIBUTE {a.aType == typeToReturn})

let _getRequiredAttributes attrs typeToReturn = 
  match find_l (fun x -> x.aType = typeToReturn) attrs with Some a -> a


val getRequiredAttributes: t: _CK_OBJECT_CLASS -> attrs: seq _CK_ATTRIBUTE-> Tot (seq _CK_ATTRIBUTE)

let getRequiredAttributes t attrs  = 
  let requiredAttributes = getAttributesForType t in 
  map (_getRequiredAttributes attrs) requiredAttributes


(* CK_PKCS11_FUNCTION_INFO(C_GenerateKey)
#ifdef CK_NEED_ARG_LIST
(
  CK_SESSION_HANDLE    hSession,    /* the session's handle */
  CK_MECHANISM_PTR     pMechanism,  /* key generation mech. */
  CK_ATTRIBUTE_PTR     pTemplate,   /* template for new key */
  CK_ULONG             ulCount,     /* # of attrs in template */
  CK_OBJECT_HANDLE_PTR phKey        /* gets handle of new key */
);
#endif *)

(* if all the preconditions are satisfied, we run this function *)


val __CKS_GenerateKey: d: device ->  
  hSession: _CK_SESSION_HANDLE -> 
  pMechanism: _CK_MECHANISM ->
  pTemplate: seq _CK_ATTRIBUTE {attributesTemplateComplete CKO_SECRET_KEY pMechanism pTemplate} -> 
  Tot(
    (handler: result _CK_OBJECT_HANDLE) & 
    (resultDevice : device (*
      {
	if Inr? handler then 
	  d = resultDevice else 
	let handler : nat = (match handler with Inl a -> a) in 
	Seq.length resultDevice.keys = Seq.length d.keys + 1 /\
	Seq.length resultDevice.subSessions = Seq.length d.subSessions /\
	handler = Seq.length resultDevice.keys -1 /\
	(
	  let newCreatedKey = Seq.index resultDevice.keys handler in 
	  isKeySecretKey newCreatedKey /\
	  (
	    let attributeLocal = getObjectAttributeLocal newCreatedKey.ko.sto  in 
	    index (match attributeLocal with Some a -> a).pValue 0 == true
	  )
	) /\
	modifiesKeysM d resultDevice handler 
      }*)
    ) 
  )


let __CKS_GenerateKey d hSession pMechanism pTemplate = 
  let mechanism = mechanismCreationSelect d pMechanism pTemplate in 
  admit();
  match mechanism with 
  |Inl mechanism -> 
    let rawKey = mechanism () in 
    let allExistingAttributes = combineAllAttributes pMechanism.mechanismID pTemplate in 
    let requiredAttributes = getRequiredAttributes CKO_SECRET_KEY allExistingAttributes in 
    let valueAttribute = A CKA_VALUE rawKey in 
    let key = _CKO_SECRET_KEY_Constructor (snoc requiredAttributes valueAttribute) in 
    let (|updatedDevice, handler|) = deviceAddKey d key.sk in 
    (|Inl handler, updatedDevice|)
  |Inr exp -> (|Inr exp, d|)


val _CKS_GenerateKey: d: device -> 
  hSession: _CK_SESSION_HANDLE -> 
  pMechanism: _CK_MECHANISM -> 
  pTemplate: seq _CK_ATTRIBUTE -> 
    Tot(
    (handler: result _CK_OBJECT_HANDLE) & 
    (resultDevice : device)
  )


let _CKS_GenerateKey d hSession pMechanism pTemplate = 
  admit();
  __CKS_GenerateKey d hSession pMechanism pTemplate

(*
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
