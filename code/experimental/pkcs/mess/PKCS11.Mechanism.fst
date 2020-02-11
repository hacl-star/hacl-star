module PKCS11.Mechanism

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul
open FStar.HyperStack
open FStar.Ghost

open FStar.Seq
open FStar.Buffer

open PKCS11.DateTime
open PKCS11.TypeDeclaration
open PKCS11.Exception

open FStar.Option

(* Getters *)

val isMechanismGeneration: m: mechanism -> Tot bool

let isMechanismGeneration m = 
	match m with
	| Generation _ _ _ _ _ _ _ _  -> true
	| _ -> false

val isMechanismFound: m: mechanism -> Tot bool

let isMechanismFound m = 
	match m with
	| NotFoundMechanism -> true
	| _ -> false	

val mechanismGetType: m: mechanism{Generation? m /\ Test? m} -> Tot _CK_MECHANISM_TYPE

let mechanismGetType m = 
	match m with 
	| Generation identifier _ _ _ _ _ _ _   -> identifier
	| Test identifier -> identifier


val mechanismGetFunctionGeneration: m: mechanism{isMechanismGeneration m} -> 
	Tot (buffer FStar.UInt8.t -> 
		FStar.UInt32.t ->
		attrs: buffer attribute_t -> 
		lenAttr: FStar.UInt32.t{length attrs = UInt32.v lenAttr} ->			
		Stack unit 
			(requires (fun h -> True)) 
			(ensures (fun h0 _ h1 -> True))
		)

let mechanismGetFunctionGeneration m = 
	match m with 
	| Generation _ f _ _ _ _ _ _  -> f 

val mechanismRawGetTypeID: m: _CK_MECHANISM -> Tot _CK_MECHANISM_TYPE	

let mechanismRawGetTypeID m = 
	match m with 
	|MechanismRaw t _ _ -> t

val getMechanismRawParameters: m: _CK_MECHANISM -> Tot _CK_VOID_PTR 

let getMechanismRawParameters m = 
	match m with 
	|MechanismRaw _ par _ -> par


val getMechanismRawParametersLen: m: _CK_MECHANISM -> Tot _CK_ULONG

let getMechanismRawParametersLen m = 
	match m with 
	|MechanismRaw _ _ len -> len
(* /Getters *)

(*
If the attribute values in the supplied template, together with any
default attribute values and any attribute values contributed to the
object by the object-creation function itself, are insufficient to
fully specify the object to create, then the attempt should fail with
the error code CKR_TEMPLATE_INCOMPLETE. 
*)

(*2.33.3 Blowfish key generation

The Blowfish key generation mechanism, denoted CKM_BLOWFISH_KEY_GEN,
is a key generation mechanism Blowfish.

It does not have a parameter.

The mechanism generates Blowfish keys with a particular length, as
specified in the CKA_VALUE_LEN attribute of the template for the key.

The mechanism contributes the CKA_CLASS, CKA_KEY_TYPE, and CKA_VALUE
attributes to the new key. Other attributes supported by the key type
(specifically, the flags indicating which functions the key supports)
may be specified in the template for the key, or else are assigned
default initial values.

For this mechanism, the ulMinKeySize and ulMaxKeySize fields of the
CK_MECHANISM_INFO structure specify the supported range of key sizes
in byte *)



assume val getMemoryMechanismProvidedAttributes: unit -> StackInline (sBuffer attribute_t)
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))

assume val getMemoryMechanismRequiredAttributes: unit -> StackInline (sBuffer _CK_ULONG)
	(requires (fun h -> True))
	(ensures (fun h0 _ h1 -> True))

val getMemoryProvidedAttributes: mechanismIndex: _CK_MECHANISM_TYPE ->  
	elements: FStar.UInt32.t -> 
	Stack (result (buffer attribute_t)) 
		(requires (fun h -> True))
		(ensures (fun h0 _ h1 -> True))

let getMemoryProvidedAttributes mechanismIndex elements= 
	let memory = getMemoryMechanismProvidedAttributes () in 	
	let lengthMemory = getSBufferLength memory in 
	let memory = getSBufferB memory in 
	if UInt32.v mechanismIndex = 1 then begin
		let startIndexMemory = 0ul in 
		let lenMechanism = elements in  
		(*check for sub *)
		if (true) then 
			let memoryCut  = sub memory startIndexMemory lenMechanism in 
			Inl memoryCut
		else 
			Inr(TestExc)	
		end	
	else
		Inr(TestExc)

val getMemoryRequiredAttributes: mechanismIndex: _CK_MECHANISM_TYPE ->  
	elements: FStar.UInt32.t -> 
	Stack (result (buffer _CK_ULONG))
		(requires (fun h -> True))
		(ensures (fun h0 _ h1 -> True))

let getMemoryRequiredAttributes mechanismIndex elements = 
	let memory = getMemoryMechanismRequiredAttributes () in 	
	let lengthMemory = getSBufferLength memory in 
	let memory = getSBufferB memory in 
	if UInt32.v mechanismIndex = 1 then begin
		let startIndexMemory = 0ul in 
		let lenMechanism = elements in 
		(*check for sub *)
		if (true) then 
			let memoryCut  = sub memory startIndexMemory lenMechanism in 
			Inl memoryCut
		else 
			Inr(TestExc)	
		end	
	else
		Inr(TestExc)
