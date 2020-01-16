module PKCS11.Cast

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All
open FStar.Mul
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer

open PKCS11.TypeDeclaration

assume val castToObjectClass: raw: _CK_VOID_PTR -> 
	Stack (buffer _CK_OBJECT_CLASS)
		(requires (fun h -> True))
		(ensures (fun h0 _ h1 -> True))

assume val castToKeyType: raw: _CK_VOID_PTR -> 
	Stack (buffer _CK_KEY_TYPE_T)
		(requires (fun h -> True))
		(ensures (fun h0 _ h1 -> True))		

assume val castToBool: raw: _CK_VOID_PTR -> Stack (buffer bool)
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))   

assume val castToUlong: raw: _CK_VOID_PTR -> Stack (buffer _CK_ULONG)
	(requires (fun h -> True))
	(ensures (fun h0 _ h1 -> True))    

assume val changeSizeOfBuffer: before: _CK_ULONG -> shift: FStar.UInt32.t -> Tot _CK_ULONG	