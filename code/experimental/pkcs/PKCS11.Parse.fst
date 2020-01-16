module PKCS11.Parse


module ST = FStar.HyperStack.ST

open FStar.HyperStack.All


open FStar.Mul
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer

open PKCS11.TypeDeclaration
open PKCS11.Attribute
open PKCS11.Mechanism
open PKCS11.Exception
open PKCS11.DateTime
open PKCS11.Cast

open FStar.Option

(*
	new CK_ATTRIBUTE(CKA.CLASS, CKO.SECRET_KEY),
    new CK_ATTRIBUTE(CKA.TOKEN, CK_BBOOL.TRUE),
    new CK_ATTRIBUTE(CKA.SENSITIVE, CK_BBOOL.TRUE),
    new CK_ATTRIBUTE(CKA.VALUE_LEN, 32),
    new CK_ATTRIBUTE(CKA.KEY_TYPE, CKK.AES),
    new CK_ATTRIBUTE(CKA.LABEL, "testAES".getBytes()),
    new CK_ATTRIBUTE(CKA.PRIVATE, new CK_BBOOL(bPrivate)) 
*)


val parseAttribute: attr_r: _CK_ATTRIBUTE -> 
	Stack (result (attr: attribute_t(*{attributeGetTypeID attr = attributeRawGetTypeID attr_r})*)))
		(requires (fun h -> True))
		(ensures (fun h0 _ h1 -> True))

let parseAttribute attr_r = 
	let typ = attributeRawGetTypeID attr_r in 
	let data = attributeRawGetData attr_r in 
	let length = attributeRawGetLength attr_r in 
	let isReadOnly = attributesIsReadOnlyParsing typ  in 
	if UInt32.v typ = 0 then 
		if length = 1ul then 	
			let pointer = castToObjectClass data in 
			//let length = changeSizeOfBuffer length 1ul in 
			let attr = CKA_CLASS typ pointer length isReadOnly in 
			Inl (attr)
		else 
			Inr(O CKR_ATTRIBUTE_TYPE_INVALID)	 
	else if UInt32.v typ = 1 then 
		if length = 1ul then
			let pointer = castToBool data in 
			//let length = changeSizeOfBuffer length 4ul in 
			let attr = CKA_TOKEN typ pointer length isReadOnly in 
			Inl(attr)
		else 
			Inr(O CKR_ATTRIBUTE_TYPE_INVALID)	 		
	else if UInt32.v typ = 2 then
		if length = 1ul then 
			let pointer = castToBool data in 
			//let length = changeSizeOfBuffer length 4ul in 
			let attr = CKA_TOKEN typ pointer length isReadOnly in 	
			Inl(attr)
		else 
			Inr(O CKR_ATTRIBUTE_TYPE_INVALID)	 
	else if UInt32.v typ = 3 then 
		let pointer = castToUlong data in 
		//let length = changeSizeOfBuffer length 4ul in 
		let attr = CKA_LABEL typ pointer length isReadOnly in 
		Inl (attr)	
	else if UInt32.v typ = 100 then 
		if length = 1ul then
			let pointer = castToKeyType data in 
			//let length = changeSizeOfBuffer length 1ul in 
			let attr = CKA_KEY_TYPE typ pointer length isReadOnly in 
			Inl (attr)
		else 
			Inr(O CKR_ATTRIBUTE_TYPE_INVALID)	 		
	else if UInt32.v typ = 103 then 
		if length = 1ul then
			let pointer = castToBool data in 
			//let length = changeSizeOfBuffer length 4ul in 
			let attr = CKA_SENSITIVE typ pointer length isReadOnly in 
			Inl(attr) 
		else 
			Inr(O CKR_ATTRIBUTE_TYPE_INVALID)	 	
	else if UInt32.v typ = 161 then 
		if length = 1ul then
			let pointer = castToUlong data in 
			//let length = changeSizeOfBuffer length 4ul in 
			let attr = CKA_VALUE_LEN typ pointer length isReadOnly in 	
			Inl(attr)
		else 
			Inr(O CKR_ATTRIBUTE_TYPE_INVALID)	 	
	else
	 	Inr (O CKR_ATTRIBUTE_TYPE_INVALID)









(* Add more general -> More general to Lib, concrete impl -> here *)

val _buffer_map: #a: Type -> #b: Type -> b1: buffer a -> b2: buffer b -> 
	f: (a -> Stack (result b)
		(requires (fun h -> True))
		(ensures (fun h0 _ h1 -> True))) -> 
	len: FStar.UInt32.t -> 
	counter: FStar.UInt32.t -> 
	StackInline (result unit)
		(requires (fun h -> True))
		(ensures (fun h0 _ h1 -> True))

let rec _buffer_map #a #b b1 b2 f len counter  = 
	if UInt32.eq counter len then Inl ()
	else 
		let element = (f b1.(counter)) in 
		if resultIsOk element then 
	begin
		let toChange = index b1 counter in 
		let changed = f toChange in 
		if not (resultIsOk changed) then 
			Inr (TestExc)
		else 
			let unpackedChanged = resultLeft changed in 	
		upd b2 counter unpackedChanged;
		let counter = FStar.UInt32.add counter 1ul in 
		_buffer_map #a #b b1 b2 f len counter
	end
		else
			Inr (TestExc)

val buffer_map: #a: Type -> #b: Type -> b1: buffer a -> b2: buffer b -> f: (a -> Stack(result b)
		(requires (fun h -> True))
		(ensures (fun h0 _ h1 -> True))) -> 
	len: FStar.UInt32.t -> 
	StackInline (result unit)
		(requires (fun h -> True))
		(ensures (fun h0 _ h1 -> True))

let buffer_map #a #b b1 b2 f len = 
	_buffer_map #a #b b1 b2 f len 0ul

(* For now I think it´s partially updating the buffer, maybe if there is an 
error we need to cancel the changes*)

val parseAttributes: attr_r: buffer _CK_ATTRIBUTE-> 
	to: buffer attribute_t -> 
	len: UInt32.t -> Stack (result (buffer attribute_t))
		(requires (fun h -> True))
		(ensures (fun h0 _ h1 -> True))

let parseAttributes attr_r to len = 
	let result = buffer_map attr_r to parseAttribute len in 
	if resultIsOk result then 
		Inl to
	else Inr(TestExc)	

val rng_algorithm: input: buffer FStar.UInt8.t ->  length: FStar.UInt32.t -> 
	attrs: buffer attribute_t -> 
	lenAttr: FStar.UInt32.t  -> 
  Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))

let rng_algorithm input length attrs lenAttr = 
	let zero = 0x1uy in 
	upd input 0ul zero    

val rng_algorithm2: input: buffer FStar.UInt8.t ->  length: FStar.UInt32.t -> 
	attrs: buffer attribute_t -> 
	lenAttr: FStar.UInt32.t ->
  Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))    

let rng_algorithm2 input length attrs lenAttr = 
	let zero = 0x1uy in 
	upd input 0ul zero      

(* memory distribution  *)
(* mechanism1 : values for attributes - usually there are just three of them, where the third one is
value - no need to store*)
(*the list of required attributes *)


val parseMechanism: m: _CK_MECHANISM-> Stack(result mechanism)
		(requires (fun h -> True))
	    (ensures (fun h0 _ h1 -> True)) 

let parseMechanism m = 
	let id = mechanismRawGetTypeID m in 
	let params = getMechanismRawParameters m in 
	let paramLen = getMechanismRawParametersLen m in 
	if (UInt32.v id) = 1 then (*Generation mechanisms *) 

		begin
		let lengthProvidedAttr = 2ul in 
		let lengthRequiredAttr = 0ul in 

		let providedAttrs = getMemoryProvidedAttributes id  lengthProvidedAttr  in 
		let requiredAttrs = getMemoryRequiredAttributes id  lengthRequiredAttr in 
		if (resultIsOk providedAttrs && resultIsOk requiredAttrs) then begin
			let unpackedProvidedAttrs = resultLeft providedAttrs in 
			let unpackedRequiredAttrs = resultLeft requiredAttrs in 
			let m = Generation  id rng_algorithm params paramLen 
				unpackedProvidedAttrs lengthProvidedAttr unpackedRequiredAttrs lengthRequiredAttr in 
			Inl m end
		else
			Inr (TestExc) 
		end
	else
		Inr (TestExc)		
	
