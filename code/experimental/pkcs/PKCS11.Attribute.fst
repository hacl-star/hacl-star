module PKCS11.Attribute

module ST = FStar.HyperStack.ST

open FStar.UInt32
open FStar.HyperStack.All
open FStar.Mul
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer

open PKCS11.TypeDeclaration 
open PKCS11.Mechanism
open FStar.Option

open FStar.Seq
open PKCS11.Lib
open FStar.Buffer


#reset-options "--max_fuel 0 --z3rlimit 200"
(* Getters*)

val attributeGetTypeID: a: attribute_t -> Tot _CK_ATTRIBUTE_TYPE

let attributeGetTypeID a = 
	match a with 
	| CKA_CLASS identifier _ _ _ -> identifier
	| CKA_TOKEN identifier _ _ _ -> identifier	
	| CKA_PRIVATE  identifier _ _ _ -> identifier	
	| CKA_LABEL  identifier _ _ _ -> identifier	
	| CKA_APPLICATION identifier _ _ _ -> identifier	
	| CKA_VALUE identifier _ _ _ -> identifier	
	| CKA_OBJECT_ID identifier _ _ _ -> identifier	
	| CKA_CERTIFICATE_TYPE identifier _ _ _ -> identifier	
	| CKA_ISSUER identifier _ _ _ -> identifier	
	| CKA_SERIAL_NUMBER identifier _ _ _ -> identifier	
	| CKA_KEY_TYPE identifier _ _ _ -> identifier	
	| CKA_ID identifier _ _ _ -> identifier	
	| CKA_SENSITIVE identifier _ _ _ -> identifier	
	| CKA_ENCRYPT identifier _ _ _ -> identifier	
	| CKA_DECRYPT identifier _ _ _ -> identifier	
	| CKA_WRAP identifier _ _ _ -> identifier	
	| CKA_UNWRAP identifier _ _ _ -> identifier	
	| CKA_SIGN identifier _ _ _ -> identifier	
	| CKA_VERIFY identifier _ _ _ -> identifier	
	| CKA_STUB identifier _ _ _ -> identifier


val attributeGetLength: a: attribute_t -> Tot _CK_ULONG

let attributeGetLength a = 
	match a with 
	| CKA_CLASS _ _ length  _ -> length
	| CKA_TOKEN _ _ length  _ -> length	
	| CKA_PRIVATE _ _ length  _ -> length	
	| CKA_LABEL  _ _ length  _ -> length	
	| CKA_APPLICATION _ _ length  _ -> length	
	| CKA_VALUE _ _ length  _ -> length	
	| CKA_OBJECT_ID _ _ length  _ -> length	
	| CKA_CERTIFICATE_TYPE _ _ length  _ -> length	
	| CKA_ISSUER _ _ length  _ -> length	
	| CKA_SERIAL_NUMBER _ _ length  _ -> length	
	| CKA_KEY_TYPE _ _ length _ -> length	
	| CKA_ID _ _ length  _ -> length	
	| CKA_SENSITIVE _ _ length _ -> length	
	| CKA_ENCRYPT _ _ length _ -> length	
	| CKA_DECRYPT _ _ length _ -> length	
	| CKA_WRAP _ _ length _ -> length	
	| CKA_UNWRAP _ _ length _ -> length	
	| CKA_SIGN _ _ length _ -> length	
	| CKA_VERIFY _ _ length _ -> length	
	| CKA_STUB _ _ length _ -> length

val attributeGetReadOnly: a: attribute_t -> Tot bool

let attributeGetReadOnly a = 
	match a with 
	| CKA_CLASS _ _  _ readOnly-> readOnly
	| CKA_TOKEN _ _  _ readOnly -> readOnly	
	| CKA_PRIVATE  _ _  _ readOnly -> readOnly	
	| CKA_LABEL  _ _  _ readOnly -> readOnly	
	| CKA_APPLICATION _ _  _ readOnly -> readOnly	
	| CKA_VALUE _ _  _ readOnly -> readOnly	
	| CKA_OBJECT_ID _ _  _ readOnly -> readOnly	
	| CKA_CERTIFICATE_TYPE _ _  _ readOnly -> readOnly	
	| CKA_ISSUER _ _  _ readOnly -> readOnly	
	| CKA_SERIAL_NUMBER _ _  _ readOnly -> readOnly	
	| CKA_KEY_TYPE _ _  _ readOnly -> readOnly	
	| CKA_ID _ _  _ readOnly -> readOnly	
	| CKA_SENSITIVE _ _ _ readOnly -> readOnly	
	| CKA_ENCRYPT _ _ _ readOnly -> readOnly	
	| CKA_DECRYPT _ _ _ readOnly -> readOnly	
	| CKA_WRAP _ _  _ readOnly -> readOnly	
	| CKA_UNWRAP _ _ _ readOnly -> readOnly	
	| CKA_SIGN _ _ _ readOnly -> readOnly	
	| CKA_VERIFY _ _  _ readOnly -> readOnly
	| CKA_STUB _ _ _ readOnly -> readOnly

val attributeRawGetTypeID: a: _CK_ATTRIBUTE -> Tot _CK_ATTRIBUTE_TYPE

let attributeRawGetTypeID a = 
	match a with 
	|AttributeRaw typ _ _ -> typ

val attributeRawGetData: a: _CK_ATTRIBUTE -> Tot _CK_VOID_PTR

let attributeRawGetData a  = 
	match a with
	| AttributeRaw _ pValue _ -> pValue

val attributeRawGetLength: a: _CK_ATTRIBUTE -> Tot _CK_ULONG

let attributeRawGetLength a = 
	match a with 
	| AttributeRaw _ _ length -> length


(* Either to return as an attribute or exactly the value *)

let cryptoKiAttributeDefault = []

(*4.3.4.2 *)

val attributesIsReadOnlyParsing: a: _CK_ATTRIBUTE_TYPE -> Tot bool

let attributesIsReadOnlyParsing a = 
	if UInt32.v a = 1 then 
		false
	else 
		false	


val attributesIsReadOnlyPredicate: a: attribute_t -> Tot bool

let attributesIsReadOnlyPredicate a = 
	attributeGetReadOnly a 



val attributesForAll: b: buffer attribute_t ->l: FStar.UInt32.t{length b == v l} ->  
	f: (attribute_t -> Tot bool) -> 
		Stack bool
		(requires (fun h -> live h b))
		(ensures (fun h0 _ h1 -> live h1 b)) (*)
	(ensures (fun b -> b == true <==> 
		(forall (i: nat { i< length s}). f (index s i) == true)))*)

let attributesForAll b l f = buffer_for_all b l f


(* Check I *)

val attributesForAllNotReadOnly: b: buffer attribute_t ->l: FStar.UInt32.t{length b == v l} -> Stack bool
			(requires (fun h -> live h b))
			(ensures (fun h0 _ h1 -> live h1 b))

let attributesForAllNotReadOnly b l  = 
	not (attributesForAll b l attributesIsReadOnlyPredicate)

(* Check I *)



(*)

val attributesForAllSeveralFunctions: b: buffer attribute_t ->l: FStar.UInt32.t{length b == v l} -> 
		fs: buffer (attribute_t -> Tot bool)(*{List.length fs = 2}*) -> Stack bool
			(requires (fun h -> live h b))
			(ensures (fun h0 _ h1 -> live h1 b))

let attributesForAllSeveralFunctions b l fs = 
	let f0 = index fs 0ul in 
	let f1 = index fs 1ul in 
	//let fBig = (fun a -> f0 a || f1 a) in 
	//attributesForAll s fBig
	attributesForAll b l f0 || attributesForAll b l f1



(* Given the list of attributes, it checks whether all the attributes are valid.
	It's using the list of allowed attributes defined in Type Declaration*)

val attributesForAllNotReadOnly: b: buffer attribute_t ->l: FStar.UInt32.t{length b == v l} -> Stack bool
			(requires (fun h -> live h b))
			(ensures (fun h0 _ h1 -> live h1 b))

let attributesForAllNotReadOnly b l  = 
	not (attributesForAll b l (attributesIsReadOnly))

(*)




val _attributesForAllSufficientEl: attr: list attribute_t -> s_ent: (attribute_t -> Tot bool)  -> Pure bool
	(requires True)
	(ensures(fun b -> 
		b == true <==> 
			(exists (k: nat {k<length attr}). s_ent (index attr k) == true)))

let _attributesForAllSufficientEl attr s_ent = 
	let result = find s_ent attr in match result with |None -> false |Some _ -> true

assume val attributesForAllSufficient: attr: list attribute_t -> 
	predicates: (buffer (attribute_t -> Tot bool )) -> Pure bool
	(requires True)
	(ensures (fun b -> True))(* (fun b -> b == true <==> 
		(forall (i: nat {i<length predicates}). 
			(exists (k: nat{k < length attr}). 
				let f = (index predicates i) in  f (index attr k) == true))))
*)
(*let attributesForAllSufficient attr predicates = 
	for_all (_attributesForAllSufficientEl attr) predicates
*)

val attributesSufficient: attr: list attribute_t  ->  m: mechanism -> Tot bool

let attributesSufficient attr m = 
	let attributesFromMechanism = getAttributesProvidedByMechanism m in (* list*)
	let attributesDefault = cryptoKiAttributeDefault in 
	let attributesCurrent = attr in 
	let allAttributes = append attributesFromMechanism attributesDefault in 
	let allAttributes = append allAttributes attributesCurrent in 
	let attributesRequired = getMechanismRequiredAttributes m in 
	attributesForAllSufficient allAttributes attributesRequired





(*)
val find_: s: seq nat -> a: nat ->index: nat{Seq.length s > index} -> 
	 Tot (r: option nat {Some? r ==> (Some?.v r)< Seq.length s /\ Seq.index s (Some?.v r) = a /\ Seq.mem a s})
	 (decreases (Seq.length s - index))

let rec find_ s a index = 
	if (Seq.index s index = a) then Some index 
	else if (index +1 = Seq.length s) then None
	else find_ s a (index + 1) 

val find : s: seq nat -> a: nat -> Tot (r: option nat {Some? r ==> (Some?.v r)< Seq.length s 
		/\ Seq.index s (Some?.v r) = a /\ Seq.mem a s})

let find s a = 
	if Seq.length s = 0 then None 
	else find_ s a 0

(*)
val attributesInconsistencyGenerateLists: attr: list attribute_t-> index: nat {index < Seq.length attr} ->
	indexes: seq nat->s: seq (seq attribute_t){Seq.length indexes = Seq.length s} ->  Tot 
		(r: seq (seq attribute_t) {forall (i: nat{i< Seq.length r}) 
			(j: nat {let s_ = Seq.index r i in j< Seq.length s_}). Seq.length (Seq.index r i) >= 1 /\ 
				(let s_ = Seq.index r i in  )


			 })
	(decreases (Seq.length attr - index))
(*)
let rec attributesInconsistencyGenerateLists attr index indexes s = 
	let attribute = Seq.index attr index in
	let typ = attributeGetTypeID attribute in 
	let indexAtr = find indexes typ  in 
	let (updatedIndexes, s) = 
		match indexAtr with 
		| None -> ((Seq.snoc indexes typ), (Seq.snoc s (Seq.create 1 attribute)))
		| Some index -> ((indexes), 
			(let typedSequence = Seq.index s index in 
				let seqUpdated = Seq.snoc typedSequence attribute in Seq.upd s index seqUpdated)) in 
	if (index + 1 = Seq.length attr) then s 
	else attributesInconsistencyGenerateLists attr (index + 1) updatedIndexes s 



