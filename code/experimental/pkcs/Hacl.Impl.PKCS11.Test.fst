module Hacl.Impl.PKCS11.Test

open Hacl.Impl.PKCS11.Creation.GenKey

open Hacl.Impl.PKCS11.Internal.Types
open Hacl.Impl.PKCS11.Internal.Attribute
open Hacl.Impl.PKCS11.DeviceModule
open Hacl.Impl.PKCS11.Session

open Hacl.Impl.PKCS11.Result
open Hacl.Impl.PKCS11.Parsing

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open LowStar.Buffer


val test:   
  	d: device -> 
  	hSession: _CK_SESSION_HANDLE -> 
  	pMechanism: _CK_MECHANISM_TYPE -> 
  	ulCount: size_t -> 
  	pTemplate: buffer attributeD {length pTemplate = uint_v ulCount} -> 
  	Stack (
    	(exp: exception_t) & (_CK_OBJECT_HANDLE))
  	(requires fun h -> live h pTemplate)
  	(ensures fun h0 _ h1 -> True)


let test d hSession pMechanism ulCount pTemplate =  _CKS_GenerateKey d hSession pMechanism ulCount pTemplate
