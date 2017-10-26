module Hacl.VRF.HashToCurveHelper

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

open Hacl.VRF.Counter

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

#set-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0"

val bufferComp:
    counter: tuple4 uint64_t uint64_t uint64_t uint64_t-> Tot bool

let bufferComp counter = 
	let a = 13876462170967809896uL in 
	assert(FStar.UInt64.v a <pow2 64); 
	let b = 12031312481604134578uL in
	assert(FStar.UInt64.v b <pow2 64); 
	let c = 0uL in 
	let d = 9223372036854775808uL in 
	assert(FStar.UInt64.v d <pow2 64); 
	let (a', b', c', d') = counter in 
	(FStar.UInt64.eq a a' && FStar.UInt64.eq b b' && FStar.UInt64.eq c c' && FStar.UInt64.eq d d')


#set-options "--z3rlimit 70 --max_fuel 0"

val _helper_ECVRF_hash_to_curve:
    pointBuffer : point -> (* modifies2 *)
    output: hbytes{disjoint pointBuffer output}-> (* length output = v inputLength + 96 *)
    inputLength : uint32_t
        {length output = v inputLength + 64 /\ v inputLength + 32 < max_input_len_8} -> 
    counter: tuple4 uint64_t uint64_t uint64_t uint64_t -> 
    Stack bool
        (requires
            (fun h0 -> live h0 pointBuffer /\
                  live h0 output
        )
            )
    (ensures (fun h0 _ h1 -> 
    	live h1 output /\ live h1 pointBuffer
        /\ modifies_2 pointBuffer output h0 h1
      ))

#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"


let rec _helper_ECVRF_hash_to_curve pointBuffer output inputLength counter  =
  	let h0 = ST.get () in
  	let lengthBufferToInputHash = (inputLength +^ 32ul) in
  	let bufferForInputHash = Buffer.sub output 0ul lengthBufferToInputHash in
  	let bufferForComputedHash = Buffer.sub output lengthBufferToInputHash 32ul in
	let ctr = Buffer.sub output inputLength 32ul in 
	hash bufferForComputedHash bufferForInputHash lengthBufferToInputHash;  (* l < max_input_len_8*)
	let h1 = ST.get() in
  		assert(modifies_1 output h0 h1);
  	let successful = _OS2ECP pointBuffer bufferForComputedHash in 
  	if successful then 
  	(
		let h2 = ST.get() in 
		assert (modifies_1 pointBuffer h1 h2);
		lemma_modifies_1_1 output pointBuffer h0 h1 h2;	
		assert(modifies_2 pointBuffer output h0 h2); 
		true
  	)
  	else
  	( 
  			let h2 = ST.get() in 
			assert (modifies_1 pointBuffer h1 h2);
			lemma_modifies_1_1 output pointBuffer h0 h1 h2;	
			assert(modifies_2 pointBuffer output h0 h2);  

  		if (bufferComp counter) then 
  		(
  			let h3 = ST.get() in 
			let counter = counter_increment counter ctr in 
			assert(modifies_1 output h2 h3);
			lemma_modifies_0_is_modifies_1 h3 pointBuffer;
			assert(modifies_1 pointBuffer h3 h3);
			lemma_modifies_1_1 output pointBuffer h2 h3 h3; 
			assert(modifies_2 pointBuffer output h2 h3);
			lemma_modifies_2_trans pointBuffer output h0 h2 h3;
			assert(modifies_2 pointBuffer output h0 h3);
	      	_helper_ECVRF_hash_to_curve pointBuffer output inputLength counter
	    )
		else
		(
			 false
	    )
  )