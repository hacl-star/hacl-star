module Hacl.VRF.Counter

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All
open FStar.Int.Cast
open FStar.Int.Cast.Full
open FStar.Buffer

open Hacl.UInt8
open Hacl.UInt32
open FStar.UInt32

open Hacl.Impl.Ed25519.ExtPoint
open Hacl.Impl.Ed25519.PointAdd
open Hacl.Bignum25519

open Hacl.Hash.SHA2_256.Lemmas

open VRF

private let uint32_t  = FStar.UInt32.t
private let uint64_t = FStar.UInt64.t
private let uint128_t = FStar.UInt128.t


let max_input_len_8 = pow2 61
let size_word = 4ul
let size_hash_w   = 8ul
let size_block_w  = 16ul
let size_hash     = size_word *^ size_hash_w


type hbytes = buffer Hacl.UInt8.t

#set-options "--z3rlimit 50 --initial_fuel 0 --max_fuel 0"


val counterToBuffer: counter: tuple4 uint64_t uint64_t uint64_t uint64_t -> 
	seqToPutCounter: buffer (UInt8.t){length seqToPutCounter = 32} -> 
		Stack unit 
		(requires 
			(fun h0 -> live h0 seqToPutCounter)
		)
		(ensures
			(fun h0 _ h1 -> live h1 seqToPutCounter /\ modifies_1 seqToPutCounter h0 h1)
		)

let counterToBuffer counter seqToPutCounter = 
	let h0 = ST.get	() in 
	let (a,b,c,d) = counter in 
	let temp = a in 
	seqToPutCounter.(0ul) <- (uint64_to_uint8 (FStar.UInt64.rem temp 256uL)); 
		let temp = FStar.UInt64.shift_right a 8ul in 
	seqToPutCounter.(1ul) <- (uint64_to_uint8 (FStar.UInt64.rem temp 256uL));
		let temp = FStar.UInt64.shift_right a 8ul in
	seqToPutCounter.(2ul) <- (uint64_to_uint8 (FStar.UInt64.rem temp 256uL));	
		let temp = FStar.UInt64.shift_right a 8ul in
	seqToPutCounter.(3ul) <- (uint64_to_uint8 (FStar.UInt64.rem temp 256uL));	
		let temp = FStar.UInt64.shift_right a 8ul in
	seqToPutCounter.(4ul) <- (uint64_to_uint8 (FStar.UInt64.rem temp 256uL));		
		let temp = FStar.UInt64.shift_right a 8ul in
	seqToPutCounter.(5ul) <- (uint64_to_uint8 (FStar.UInt64.rem temp 256uL));
		let temp = FStar.UInt64.shift_right a 8ul in
	seqToPutCounter.(6ul) <- (uint64_to_uint8 (FStar.UInt64.rem temp 256uL));	
		let temp = FStar.UInt64.shift_right a 8ul in
	seqToPutCounter.(7ul) <- (uint64_to_uint8 (FStar.UInt64.rem temp 256uL));
		let temp = b in 
	seqToPutCounter.(8ul) <- (uint64_to_uint8 (FStar.UInt64.rem temp 256uL));
		let temp = FStar.UInt64.shift_right a 8ul in
	seqToPutCounter.(9ul) <- (uint64_to_uint8 (FStar.UInt64.rem temp 256uL));
		let temp = FStar.UInt64.shift_right a 8ul in
	seqToPutCounter.(10ul) <- (uint64_to_uint8 (FStar.UInt64.rem temp 256uL));	
		let temp = FStar.UInt64.shift_right a 8ul in
	seqToPutCounter.(11ul) <- (uint64_to_uint8 (FStar.UInt64.rem temp 256uL));	
		let temp = FStar.UInt64.shift_right a 8ul in
	seqToPutCounter.(12ul) <- (uint64_to_uint8 (FStar.UInt64.rem temp 256uL));		
		let temp = FStar.UInt64.shift_right a 8ul in
	seqToPutCounter.(13ul) <- (uint64_to_uint8 (FStar.UInt64.rem temp 256uL));
		let temp = FStar.UInt64.shift_right a 8ul in
	seqToPutCounter.(14ul) <- (uint64_to_uint8 (FStar.UInt64.rem temp 256uL));	
		let temp = FStar.UInt64.shift_right a 8ul in
	seqToPutCounter.(15ul) <- (uint64_to_uint8 (FStar.UInt64.rem temp 256uL));
			let temp = c in  
	seqToPutCounter.(16ul) <- (uint64_to_uint8 (FStar.UInt64.rem temp 256uL));
		let temp = FStar.UInt64.shift_right a 8ul in
	seqToPutCounter.(17ul) <- (uint64_to_uint8 (FStar.UInt64.rem temp 256uL));
		let temp = FStar.UInt64.shift_right a 8ul in
	seqToPutCounter.(18ul) <- (uint64_to_uint8 (FStar.UInt64.rem temp 256uL));	
		let temp = FStar.UInt64.shift_right a 8ul in
	seqToPutCounter.(19ul) <- (uint64_to_uint8 (FStar.UInt64.rem temp 256uL));	
		let temp = FStar.UInt64.shift_right a 8ul in
	seqToPutCounter.(20ul) <- (uint64_to_uint8 (FStar.UInt64.rem temp 256uL));		
		let temp = FStar.UInt64.shift_right a 8ul in
	seqToPutCounter.(21ul) <- (uint64_to_uint8 (FStar.UInt64.rem temp 256uL));
		let temp = FStar.UInt64.shift_right a 8ul in
	seqToPutCounter.(22ul) <- (uint64_to_uint8 (FStar.UInt64.rem temp 256uL));	
		let temp = FStar.UInt64.shift_right a 8ul in
	seqToPutCounter.(23ul) <- (uint64_to_uint8 (FStar.UInt64.rem temp 256uL));
			let temp = d in 
	seqToPutCounter.(24ul) <- (uint64_to_uint8 (FStar.UInt64.rem temp 256uL));
		let temp = FStar.UInt64.shift_right a 8ul in
	seqToPutCounter.(25ul) <- (uint64_to_uint8 (FStar.UInt64.rem temp 256uL));
		let temp = FStar.UInt64.shift_right a 8ul in
	seqToPutCounter.(25ul) <- (uint64_to_uint8 (FStar.UInt64.rem temp 256uL));	
		let temp = FStar.UInt64.shift_right a 8ul in
	seqToPutCounter.(26ul) <- (uint64_to_uint8 (FStar.UInt64.rem temp 256uL));	
		let temp = FStar.UInt64.shift_right a 8ul in
	seqToPutCounter.(27ul) <- (uint64_to_uint8 (FStar.UInt64.rem temp 256uL));		
		let temp = FStar.UInt64.shift_right a 8ul in
	seqToPutCounter.(28ul) <- (uint64_to_uint8 (FStar.UInt64.rem temp 256uL));
		let temp = FStar.UInt64.shift_right a 8ul in
	seqToPutCounter.(29ul) <- (uint64_to_uint8 (FStar.UInt64.rem temp 256uL));	
		let temp = FStar.UInt64.shift_right a 8ul in
	seqToPutCounter.(30ul) <- (uint64_to_uint8 (FStar.UInt64.rem temp 256uL));
		let temp = FStar.UInt64.shift_right a 8ul in
	seqToPutCounter.(31ul) <- (uint64_to_uint8) (FStar.UInt64.rem temp 256uL)

val counterBufferIncrement: counter: tuple4 uint64_t uint64_t uint64_t uint64_t -> Tot (tuple4 uint64_t uint64_t uint64_t uint64_t)
let counterBufferIncrement counter = 
	let maxuint64 = 18446744073709551615uL in 
	assert(FStar.UInt64.v maxuint64 <pow2 64); 
	let (a,b,c,d) = counter in 
	let shift = 
		if (FStar.UInt64.eq d maxuint64) then 1uL else 0uL in 
	let shiftedD =  FStar.UInt64.add_mod d 1uL in 
	let shift = 
		if shift = 1uL && (FStar.UInt64.eq c maxuint64) then 1uL else 0uL in 
	let shiftedC =   FStar.UInt64.add_mod c shift in 
	let shift = 
		if shift = 1uL && (FStar.UInt64.eq b maxuint64) then 1uL else 0uL in
	let shiftedB =  FStar.UInt64.add_mod b shift in 
	let shift = 
		if shift = 1uL && (FStar.UInt64.eq a maxuint64) then 1uL else 0uL in
	let shiftedA = FStar.UInt64.add_mod a shift in 
		 (shiftedA, shiftedB, shiftedC, shiftedD)

val counter_increment: counter: tuple4 uint64_t uint64_t uint64_t uint64_t ->  
	counterBuffer: hbytes{length counterBuffer = 32} ->
    Stack (tuple4 uint64_t uint64_t uint64_t uint64_t)
        (requires
            (fun h0 -> live h0 counterBuffer)
        )
        (ensures
            (fun h0 _ h1 -> live h1 counterBuffer /\ modifies_1 counterBuffer h0 h1)
        )

let counter_increment counter counterBuffer = 
	let counter = counterBufferIncrement counter in 
	push_frame();
		let h0 = ST.get() in 
		let s = create 0uy 32ul in 
		counterToBuffer counter  s;
		let temp = s.(0ul) in 
		counterBuffer.(0ul)<-Hacl.Cast.uint8_to_sint8 (temp);
		let temp = s.(1ul) in 
		counterBuffer.(1ul)<-Hacl.Cast.uint8_to_sint8 (temp);
		let temp = s.(2ul) in 
		counterBuffer.(2ul)<-Hacl.Cast.uint8_to_sint8 (temp);
		let temp = s.(3ul) in 
		counterBuffer.(3ul)<-Hacl.Cast.uint8_to_sint8 (temp);
		let temp = s.(4ul) in 
		counterBuffer.(4ul)<-Hacl.Cast.uint8_to_sint8 (temp);
		let temp = s.(5ul) in 
		counterBuffer.(5ul)<-Hacl.Cast.uint8_to_sint8 (temp);
		let temp = s.(6ul) in 
		counterBuffer.(6ul)<-Hacl.Cast.uint8_to_sint8 (temp);
		let temp = s.(7ul) in 
		counterBuffer.(7ul)<-Hacl.Cast.uint8_to_sint8 (temp);

		let temp = s.(8ul) in 
		counterBuffer.(8ul)<-Hacl.Cast.uint8_to_sint8 (temp);
		let temp = s.(9ul) in 
		counterBuffer.(9ul)<-Hacl.Cast.uint8_to_sint8 (temp);
		let temp = s.(10ul) in 
		counterBuffer.(10ul)<-Hacl.Cast.uint8_to_sint8 (temp);
		let temp = s.(11ul) in 
		counterBuffer.(11ul)<-Hacl.Cast.uint8_to_sint8 (temp);
		let temp = s.(12ul) in 
		counterBuffer.(12ul)<-Hacl.Cast.uint8_to_sint8 (temp);
		let temp = s.(13ul) in 
		counterBuffer.(13ul)<-Hacl.Cast.uint8_to_sint8 (temp);
		let temp = s.(14ul) in 
		counterBuffer.(14ul)<-Hacl.Cast.uint8_to_sint8 (temp);
		let temp = s.(15ul) in 
		counterBuffer.(15ul)<-Hacl.Cast.uint8_to_sint8 (temp);

		let temp = s.(16ul) in 
		counterBuffer.(16ul)<-Hacl.Cast.uint8_to_sint8 (temp);
		let temp = s.(17ul) in 
		counterBuffer.(17ul)<-Hacl.Cast.uint8_to_sint8 (temp);
		let temp = s.(18ul) in 
		counterBuffer.(18ul)<-Hacl.Cast.uint8_to_sint8 (temp);
		let temp = s.(19ul) in 
		counterBuffer.(19ul)<-Hacl.Cast.uint8_to_sint8 (temp);
		let temp = s.(20ul) in 
		counterBuffer.(20ul)<-Hacl.Cast.uint8_to_sint8 (temp);
		let temp = s.(21ul) in 
		counterBuffer.(21ul)<-Hacl.Cast.uint8_to_sint8 (temp);
		let temp = s.(22ul) in 
		counterBuffer.(22ul)<-Hacl.Cast.uint8_to_sint8 (temp);
		let temp = s.(23ul) in 
		counterBuffer.(23ul)<-Hacl.Cast.uint8_to_sint8 (temp);

		let temp = s.(24ul) in 
		counterBuffer.(24ul)<-Hacl.Cast.uint8_to_sint8 (temp);
		let temp = s.(25ul) in 
		counterBuffer.(25ul)<-Hacl.Cast.uint8_to_sint8 (temp);
		let temp = s.(26ul) in 
		counterBuffer.(26ul)<-Hacl.Cast.uint8_to_sint8 (temp);
		let temp = s.(27ul) in 
		counterBuffer.(27ul)<-Hacl.Cast.uint8_to_sint8 (temp);
		let temp = s.(28ul) in 
		counterBuffer.(28ul)<-Hacl.Cast.uint8_to_sint8 (temp);
		let temp = s.(29ul) in 
		counterBuffer.(29ul)<-Hacl.Cast.uint8_to_sint8 (temp);
		let temp = s.(30ul) in 
		counterBuffer.(30ul)<-Hacl.Cast.uint8_to_sint8 (temp);
		let temp = s.(31ul) in 
		counterBuffer.(31ul)<-Hacl.Cast.uint8_to_sint8 (temp);
	pop_frame(); counter

