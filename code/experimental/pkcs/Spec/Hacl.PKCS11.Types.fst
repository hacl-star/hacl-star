module Hacl.PKCS11.Types

open FStar.UInt32
open FStar.UInt8

open FStar.Seq

type _HACL_Curve_ID = 
  |Curve25519
  |CurveP256



(* Zero-level types *)
type uint8_t = FStar.UInt8.t 
type uint32_t = a: nat {a < pow2 32}

(* First-level types *)

(* 
/* an unsigned value, at least 32 bits long */
typedef unsigned long int CK_ULONG; 
*)

type _CK_ULONG = uint32_t


(*
/* CK_ATTRIBUTE_TYPE is a value that identifies an attribute
 * type */
typedef CK_ULONG          CK_ATTRIBUTE_TYPE;
*)
type _CK_ATTRIBUTE_TYPE = 
  |CKA_CLASS
  |CKA_PRIVATE
  |CKA_KEY_TYPE
  |CKA_SIGN
  |CKA_VERIFY
  |CKA_LOCAL
  |CKA_SECRET_KEY
  |CKA_TOKEN
  |CKA_MODIFIABLE
  |CKA_LABEL
  |CKA_COPYABLE
  |CKA_DESTROYABLE
  |CKA_ID
  |CKA_START_DATE
  |CKA_END_DATE
  |CKA_DERIVED
  |CKA_KEY_GEN_MECHANISM
  |CKA_ALLOWED_MECHANISMS
  |CKA_SUBJECT
  |CKA_ENCRYPT
  |CKA_VERIFY_RECOVER
  |CKA_WRAP
  |CKA_TRUSTED
  |CKA_WRAP_TEMPLATE
  |CKA_PUBLIC_KEY_INFO
  |CKA_SENSITIVE
  |CKA_DECRYPT
  |CKA_SIGN_RECOVER
  |CKA_UNWRAP
  |CKA_EXTRACTABLE
  |CKA_ALWAYS_SENSITIVE
  |CKA_NEVER_EXTRACTABLE
  |CKA_WRAP_WITH_TRUSTED
  |CKA_UNWRAP_TEMPLATE
  |CKA_ALWAYS_AUTHENTICATE
  |CKA_CHECK_VALUE
  |CKA_EC_PARAMS 
  |CKA_VALUE


(*
/* CK_OBJECT_CLASS is a value that identifies the classes (or
 * types) of objects that Cryptoki recognizes.  It is defined
 * as follows: */
typedef CK_ULONG          CK_OBJECT_CLASS;
*)

(* /* The following classes of objects are defined: */
#define CKO_DATA              0x00000000UL
#define CKO_CERTIFICATE       0x00000001UL
#define CKO_PUBLIC_KEY        0x00000002UL
#define CKO_PRIVATE_KEY       0x00000003UL
#define CKO_SECRET_KEY        0x00000004UL
#define CKO_HW_FEATURE        0x00000005UL
#define CKO_DOMAIN_PARAMETERS 0x00000006UL
#define CKO_MECHANISM         0x00000007UL
#define CKO_OTP_KEY           0x00000008UL

#define CKO_VENDOR_DEFINED    0x80000000UL
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


type _CK_OBJECT_CLASS_EXTENDED = 
  |CKO_OBJECT
  |CKO_STORAGE
  |CKO_KEY


let getAttributesForTypeExtended: t: _CK_OBJECT_CLASS_EXTENDED -> seq _CK_ATTRIBUTE_TYPE = function
  |CKO_OBJECT -> seq_of_list [CKA_CLASS]
  |CKO_KEY -> seq_of_list [CKA_TOKEN; CKA_PRIVATE; CKA_MODIFIABLE; CKA_LABEL; CKA_COPYABLE; CKA_DESTROYABLE]
  |CKO_STORAGE -> seq_of_list [CKA_KEY_TYPE; CKA_ID; CKA_END_DATE; CKA_DERIVED; CKA_LOCAL; CKA_KEY_GEN_MECHANISM; CKA_ALLOWED_MECHANISMS]

(* other objects *)

unfold let cko_secret_key_attributes_list: list _CK_ATTRIBUTE_TYPE = 
    [
      CKA_CLASS; CKA_TOKEN; CKA_PRIVATE; CKA_MODIFIABLE; CKA_LABEL; CKA_COPYABLE; 
      CKA_DESTROYABLE; CKA_KEY_TYPE; CKA_ID; CKA_END_DATE; CKA_DERIVED; CKA_LOCAL;
      CKA_KEY_GEN_MECHANISM; CKA_ALLOWED_MECHANISMS; CKA_SENSITIVE; CKA_ENCRYPT; 
      CKA_DECRYPT; CKA_SIGN; CKA_VERIFY;  CKA_WRAP; CKA_UNWRAP; CKA_EXTRACTABLE;
      CKA_ALWAYS_SENSITIVE; CKA_NEVER_EXTRACTABLE
    ]

unfold let cko_other_list: list _CK_ATTRIBUTE_TYPE = 
  [
    CKA_CLASS; CKA_TOKEN; CKA_PRIVATE; CKA_MODIFIABLE; CKA_LABEL; CKA_COPYABLE; 
    CKA_DESTROYABLE; CKA_KEY_TYPE; CKA_ID; CKA_END_DATE; CKA_DERIVED; CKA_LOCAL;
    CKA_KEY_GEN_MECHANISM; CKA_ALLOWED_MECHANISMS; 
    CKA_SENSITIVE; CKA_ENCRYPT; CKA_DECRYPT; CKA_SIGN; CKA_VERIFY; 
    CKA_WRAP; CKA_UNWRAP; CKA_EXTRACTABLE; CKA_ALWAYS_SENSITIVE; CKA_NEVER_EXTRACTABLE
  ]

let getAttributesForType: t: _CK_OBJECT_CLASS -> (r : seq _CK_ATTRIBUTE_TYPE
  {
    match t with 
    |CKO_SECRET_KEY -> length r == 24 /\ index r 17 = CKA_SIGN
    |_ -> length r == 24
  })  = function 
  |CKO_SECRET_KEY -> 
    assert_norm (List.Tot.length cko_secret_key_attributes_list == 24);
    assert_norm(List.Tot.index cko_secret_key_attributes_list 17 = CKA_SIGN);
    let r = seq_of_list cko_secret_key_attributes_list in 
    assume (index r 17 = CKA_SIGN);
    r
  |_ -> 
    assert_norm (List.Tot.length cko_other_list == 24);
    seq_of_list cko_other_list


(* /* CK_KEY_TYPE is a value that identifies a key type */
typedef CK_ULONG          CK_KEY_TYPE;
*)
type _CK_KEY_TYPE = 
  |CKK_RSA
  |CKK_DSA
  |CKK_DH
  |CKK_EC 
  (*and much more *)


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


let _ck_attribute_get_type: _CK_ATTRIBUTE_TYPE -> Tot Type0 = function
  |CKA_CLASS -> _CK_OBJECT_CLASS
  |CKA_SIGN -> bool
  |CKA_VERIFY -> bool
  |CKA_LOCAL -> bool
  |CKA_TOKEN -> bool
  |CKA_PRIVATE -> bool
  |CKA_MODIFIABLE -> bool
  |CKA_LABEL -> uint32_t
  |CKA_COPYABLE -> bool
  |CKA_DESTROYABLE -> bool
  |CKA_KEY_TYPE -> _CK_KEY_TYPE
  |CKA_ID -> uint32_t
  |CKA_START_DATE -> uint32_t
  |CKA_END_DATE -> uint32_t
  |CKA_DERIVED -> bool
  |CKA_LOCAL -> bool
  |CKA_KEY_GEN_MECHANISM -> _CK_MECHANISM_TYPE
  |CKA_ALLOWED_MECHANISMS -> _CK_MECHANISM_TYPE
  |CKA_SUBJECT -> uint32_t 
  |CKA_ENCRYPT -> bool 
  |CKA_DECRYPT -> bool
  |CKA_VERIFY -> bool
  |CKA_VERIFY_RECOVER -> bool
  |CKA_WRAP -> bool
  |CKA_TRUSTED -> bool
  |CKA_WRAP_TEMPLATE -> _CK_ATTRIBUTE_TYPE
  |CKA_PUBLIC_KEY_INFO -> uint32_t
  |CKA_SENSITIVE -> bool
  |CKA_DECRYPT -> bool
  |CKA_SIGN -> bool
  |CKA_SIGN_RECOVER -> bool
  |_ -> _CK_ULONG
  |CKA_EC_PARAMS -> _CK_ULONG
  |CKA_VALUE -> uint8_t 


(* I am not sure that the length is stated for all possible types *)
let _ck_attribute_get_len: _CK_ATTRIBUTE_TYPE -> Tot (a: option nat {Some? a ==> (match a with Some a -> a) < pow2 32}) = function
  |CKA_CLASS -> Some 1
  |CKA_SIGN -> Some 1
  |CKA_VERIFY -> Some 1
  |CKA_LOCAL -> Some 1
  |CKA_TOKEN -> Some 1
  |CKA_PRIVATE -> Some 1 
  |CKA_MODIFIABLE -> Some 1
  |CKA_COPYABLE -> Some 1
  |CKA_LABEL -> None
  |CKA_DESTROYABLE -> Some 1
  |CKA_KEY_TYPE -> Some 1 
  |CKA_ID -> None
  |CKA_START_DATE -> Some 3
  |CKA_END_DATE -> Some 3
  |CKA_DERIVED -> Some 1
  |CKA_LOCAL -> Some 1
  |CKA_KEY_GEN_MECHANISM -> Some 1
  |CKA_ALLOWED_MECHANISMS -> None
  |_ -> None

(*/* CK_ATTRIBUTE is a structure that includes the type, length
 * and value of an attribute */
*)

type _CK_ATTRIBUTE  = 
  |A: 
    aType: _CK_ATTRIBUTE_TYPE -> 
    pValue: seq (_ck_attribute_get_type aType) 
    {
      let len = _ck_attribute_get_len aType in 
      if Some? len then 
	length pValue == (match len with Some a -> a)
      else 
	True
    } 
    -> _CK_ATTRIBUTE



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
