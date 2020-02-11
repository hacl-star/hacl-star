module PKCS11.Objects

open FStar.HyperStack.All
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer
open FStar.UInt32
open FStar.Option

open PKCS11.Exception
open PKCS11.TypeDeclaration

(*TODO: from where the references are taken  *)
(*TODO: Check whether the device has enough memory *)
assume val getTheReference: identifier: _CK_OBJECT_HANDLE -> 
	Stack (result (buffer FStar.UInt8.t))
      (requires (fun h -> True))
      (ensures (fun h0 _ h1 -> True))