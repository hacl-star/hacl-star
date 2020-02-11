module PKCS11.Lib

module ST = FStar.HyperStack.ST

open FStar.UInt32
open FStar.HyperStack.All
open FStar.Mul
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer


val _buffer_for_all: #a: Type -> b: buffer a -> l: UInt32.t{length b == v l} -> 
	f: (a -> Stack bool	(requires (fun h0 -> True)) (ensures (fun h0 _ h1 -> True)))-> 
	counter: UInt32.t {v counter <= v l} -> tempResult: bool -> 
		Stack bool
			(requires (fun h0 -> live h0 b))
			(ensures (fun h0 _ h1 -> live h1 b))

let rec _buffer_for_all #a b l f counter tempResult = 
	if UInt32.v counter = UInt32.v l then 
		tempResult
	else begin
		let element = index b counter in
		let counter = add counter 1ul in 
		let funcResult = f element in 
		let tempResult = tempResult && funcResult in  
		_buffer_for_all #a b l f counter tempResult
	end

val buffer_for_all: #a: Type -> b: buffer a -> l: UInt32.t{length b == v l} -> 
	f: (a -> Tot bool) -> 
	Stack bool
		(requires (fun h -> live h b))
		(ensures (fun h0 value h1 -> live h1 b (*) /\ value <==> (let s = as_seq h0 b in for_all f s*)))

let buffer_for_all #a b l f = 
	_buffer_for_all #a b l f 0ul true


