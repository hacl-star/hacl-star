module Hacl.Impl.PKCS11.Internal.Attribute

open Lib.IntTypes
open Hacl.Impl.PKCS11.Internal.Types

open LowStar.Buffer

(* 
/* CK_ATTRIBUTE is a structure that includes the type, length
 * and value of an attribute */
typedef struct CK_ATTRIBUTE {
  CK_ATTRIBUTE_TYPE type;
  CK_VOID_PTR       pValue;
  CK_ULONG          ulValueLen;  /* in bytes */
} CK_ATTRIBUTE;

typedef CK_ATTRIBUTE CK_PTR CK_ATTRIBUTE_PTR;
*)

unfold
let typeID_type: nat -> void = function
  |0 -> CK_ULONG
  |_ -> CK_BOOL


noeq
type attribute = 
  | CKA_CLASS: _type: _CK_ATTRIBUTE_TYPE{uint_v _type = 0} -> pValue: buffer (void_t (typeID_type (uint_v _type))) ->  ulValueLen: size_t {length pValue == uint_v ulValueLen} -> attribute
  | CKA_TOKEN: _type: _CK_ATTRIBUTE_TYPE{uint_v _type = 1} -> pValue: buffer (void_t (typeID_type (uint_v _type))) ->  ulValueLen: size_t {length pValue == uint_v ulValueLen} -> attribute
  


(*
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

