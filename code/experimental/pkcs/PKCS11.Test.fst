module PKCS11.Test

open FStar.HyperStack.All
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer
open FStar.UInt32
open FStar.Option

open FStar.Buffer

open PKCS11.TypeDeclaration
open PKCS11.Parse
open PKCS11.Exception

open PKCS11.Attribute
open PKCS11.Mechanism
open PKCS11.Objects


type _CK_RV = FStar.UInt32.t
type _CK_BBOOL = bool
type _CK_OBJECT_CLASS = buffer FStar.UInt32.t

type int = FStar.UInt32.t

(*CK_RV createKeyObject(CK_SESSION_HANDLE hSession, CK_BYTE_PTR key, CK_ULONG keyLength) {
  CK_RV rc;

  CK_OBJECT_HANDLE hKey;
  CK_BBOOL true = TRUE;
  CK_BBOOL false = FALSE;

  CK_OBJECT_CLASS keyClass = CKO_SECRET_KEY;
  CK_KEY_TYPE keyType = CKK_AES;
  CK_ATTRIBUTE keyTempl[] = {
    {CKA_CLASS (* ulong *), &keyClass, sizeof(keyClass)},
    {CKA_KEY_TYPE, &keyType, sizeof(keyType)},
    {CKA_ENCRYPT, &true, sizeof(true)},
    {CKA_DECRYPT, &true, sizeof(true)},
    {CKA_SIGN, &true, sizeof(true)},
    {CKA_VERIFY, &true, sizeof(true)},
    {CKA_TOKEN, &true, sizeof(true)},     /* token object  */
    {CKA_PRIVATE, &false, sizeof(false)}, /* public object */
    {CKA_VALUE, keyValue, keyLength}, /* AES key       */
    {CKA_LABEL, "My_AES_Key", sizeof("My_AES_Key")}
  };
  rc = C_CreateObject(hSession, keyTempl, sizeof (keyTempl)/sizeof (CK_ATTRIBUTE), &hKey);
  if (rc != CKR_OK) {
  printf("Error creating key object: 0x%X\n", rc); return rc;
  }
  printf("AES Key object creation successful.\n");
}
 *)

(* type ex_result = 
  |Ex : #a:Type -> r:result a -> ex_result

let is_exception = function Ex (Inr _) -> true | _ -> false 
 *)

val checkAttributes: attr: buffer attribute_t -> l: FStar.UInt32.t{length attr == v l} -> 
      m: mechanism -> Stack (result bool)
        (requires (fun h -> True))
        (ensures (fun h0 _ h1 -> True))

let checkAttributes attr l m = 
  let check1 = attributesForAllNotReadOnly attr l in 
  if not check1 then 
    Inr TestExc else
  Inl true 

  (*)
   // let check1 = atrributesAllValid attr in 
    let check2 = attributesForAllNotReadOnly attr in 
    let check3 = attributesSufficient attr m in 
    (* +  two inconsistencies *) 
    if ( check2 && check3) then 
      (Inl true) else (Inr TestExc)  *)


assume val getMemoryDefaultAttributes: unit -> StackInline (sBuffer attribute_t)
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))    


val _CK_C_GenerateKey: hsession: _CK_SESSION_HANDLE -> 
    pMechanism: _CK_MECHANISM -> 
    pTemplate: buffer _CK_ATTRIBUTE -> usCount: FStar.UInt32.t -> 
    phKey: _CK_OBJECT_HANDLE -> 
    Stack _CK_RV
      (requires (fun h -> True))
      (ensures (fun h0 _ h1 -> True))


let _CK_C_GenerateKey hSession pMechanism pTemplate usCount phKey  = 
(* creates a buffer for attributes *)
    let tempP = create true 1ul in 
    let testAttribute = CKA_STUB 999ul tempP 0ul false in 
    let to = Buffer.create testAttribute 10ul in 
  

    let reference = getTheReference phKey in 

    (* Moved to parsing *)
    (*let memory = getMemory() in 
    let b =  getSBufferB memory in 
    let l = getSBufferLength memory in *)

    let parsedMechanism = parseMechanism pMechanism   in 
    let parsedAttributes = parseAttributes pTemplate to usCount in 

    if not (resultIsOk parsedMechanism && resultIsOk parsedAttributes) then 
      castExpectionToRV(Inr #bool TestExc) else
    let unpackedMechanism = resultLeft parsedMechanism in 
    let correctMechanism = (isMechanismGeneration unpackedMechanism) in 
      if not correctMechanism then
        castExpectionToRV(Inr #bool TestExc) else

    let unpackedAttributes = resultLeft parsedAttributes in  
    let checkedAttributes = checkAttributes unpackedAttributes usCount unpackedMechanism in 
      if not (resultIsOk checkedAttributes) then 
        castExpectionToRV (Inr #bool TestExc) else

    let unpackedReference = resultLeft reference in 
    let f = mechanismGetFunctionGeneration unpackedMechanism in 
    f unpackedReference 100ul unpackedAttributes usCount;
    castExpectionToRV(Inl true)

assume val a: unit -> _CK_VOID_PTR

let main()  = 
  let hSession = 10ul in 
  let vd = a() in 
  let pMechanism = MechanismRaw 01ul vd 1ul in 
  let testAttribute = AttributeRaw 1ul vd 1ul in 
  let pTemplate = Buffer.create testAttribute 1ul in 
  let usCount = 1ul in 
  let phKey = 0ul in 
  let r = _CK_C_GenerateKey hSession pMechanism pTemplate usCount phKey in 
  0x1ul