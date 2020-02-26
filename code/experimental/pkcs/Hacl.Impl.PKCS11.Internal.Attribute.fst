module Hacl.Impl.PKCS11.Internal.Attribute

open Lib.IntTypes
open Hacl.Impl.PKCS11.Internal.Types

open Hacl.Impl.PKCS11.Result

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.RawIntTypes

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

noextract
unfold
let typeID_type: nat -> void = function
  |0 -> CK_ULONG
  |_ -> CK_BOOL


noeq 
type attributeD  = 
  |A: _type: _CK_ULONG -> pValue: buffer void -> ulValueLen: size_t {length pValue == uint_v ulValueLen} -> attributeD 


val lenAttribute: _CK_ATTRIBUTE_TYPE -> Tot size_t

let lenAttribute attrType = 
  let a = u32_to_UInt32 attrType in 
  match a with 
  |0ul -> (size 1) 
  |1ul -> (size 1)
  |_ -> (size 1)

noeq
type attribute = 
  | CKA_CLASS: _type: _CK_ATTRIBUTE_TYPE{uint_v _type = 0} -> pValue: buffer (void_t (typeID_type (uint_v _type))) ->  ulValueLen: size_t {length pValue == uint_v ulValueLen} -> attribute
  | CKA_TOKEN: _type: _CK_ATTRIBUTE_TYPE{uint_v _type = 1} -> pValue: buffer (void_t (typeID_type (uint_v _type))) ->  ulValueLen: size_t {length pValue == uint_v ulValueLen} -> attribute


val getAttributeType: a: attribute -> Tot _CK_ATTRIBUTE_TYPE

let getAttributeType a = 
  match a with 
  |CKA_CLASS t _ _ -> t
  |CKA_TOKEN t _ _ -> t 


val isAttributeReadOnly_: _CK_ATTRIBUTE_TYPE -> Tot bool

let isAttributeReadOnly_ attrType = 
  let a = u32_to_UInt32 attrType in 
  match a with 
  |0ul -> true
  |_ -> false

val isAttributeReadOnly: _CK_ATTRIBUTE_TYPE -> Tot (r: exception_t {CKR_OK? r \/ CKR_ATTRIBUTE_READ_ONLY? r})

let isAttributeReadOnly attrType = 
  let statusReadOnly = isAttributeReadOnly_ attrType in 
  match statusReadOnly with 
  | true -> CKR_OK
  | false -> CKR_ATTRIBUTE_READ_ONLY
  (* add your not true, not false boolean joke here *) 

val isAttributeReadOnlyBuffer: attribute -> b: buffer exception_t {length b = 1} -> 
  Stack unit 
    (requires fun h -> live h b)
    (ensures fun h0 _ h1 -> True)

let isAttributeReadOnlyBuffer a b = 
  let t = getAttributeType a in 
  let e = isAttributeReadOnly t in 
  let oldException = index b (size 0) in 
  let newException = exceptionAdd oldException e in 
  upd b (size 0) newException
  

val checkAttributes: ulCount: size_t -> pTemplate: buffer attribute{length pTemplate = uint_v ulCount} -> Stack unit
  (requires fun h -> live h pTemplate)
  (ensures fun h0 _ h1 -> True)


let checkAttributes ulCount pTemplate = 
  push_frame();
  [@inline_let]
  let okException = CKR_OK in 
  let bTest = LowStar.Buffer.alloca okException (normalize_term 1ul) in  
  C.Loops.for 0ul ulCount (fun h i -> True) (fun i ->  isAttributeReadOnlyBuffer (index pTemplate i) bTest);
  pop_frame()

