
module Hacl.VRF.HashToCurve

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All
open FStar.Buffer

open Hacl.UInt8
open Hacl.UInt32
open FStar.UInt32

open Hacl.Impl.Ed25519.ExtPoint
open Hacl.Bignum25519

open VRF
open Hacl.VRF.HashToCurveHelper

private let uint32_t  = FStar.UInt32.t
private let uint64_t = FStar.UInt64.t

let max_input_len_8 = pow2 61

type hbytes = buffer Hacl.UInt8.t


#set-options "--max_fuel 0  --z3rlimit 50 "

val _ECVRF_hash_to_curve:
	pointBuffer : point ->
	publicKey: point{disjoint pointBuffer publicKey}->
	input: hbytes{disjoint publicKey input} ->
	inputLength : uint32_t {v inputLength = length input /\ v inputLength + 96 < pow2 32  } -> 
	Stack bool 
		(requires
			(fun h0 -> live h0 pointBuffer /\ live h0 publicKey /\ live h0 input /\
				red_513 (as_seq h0 (Hacl.Impl.Ed25519.ExtPoint.getx publicKey)) /\
				red_513 (as_seq h0 (Hacl.Impl.Ed25519.ExtPoint.gety publicKey)) /\
				red_513 (as_seq h0 (Hacl.Impl.Ed25519.ExtPoint.getz publicKey)) /\
				red_513 (as_seq h0 (Hacl.Impl.Ed25519.ExtPoint.gett publicKey))
			)
		)
		(ensures
			(fun h0 _ h1 -> live h1 pointBuffer  /\ live h1 publicKey /\ live h1 input/\ modifies_1 pointBuffer h0 h1  )
		)
(*live h1 pointBuffer /\ live h1 publicKey /\ live h1 input /\ modifies_1 pointBuffer h0 h1 *)
let lemma_modifies2IsModifies1 (#a:Type) (#a':Type) (b:buffer a) (b':buffer a') h0 h1 : Lemma
  (requires (modifies_2 b b'  h0 h1))
  (ensures  (modifies_1 b h0 h1))
  = admit()

let lemma_modifies0isModifies1 (#a:Type) (b:buffer a)  h0 h1 : Lemma 
	(requires (modifies_0 h0 h1 /\ live h0 b))
	(ensures (modifies_1 b h0 h1 /\ live h1 b)) = admit() 

val _ECVRF_hash_to_curve_i: 
	input : hbytes -> 
	inputLength: uint32_t{v inputLength = length input /\ v inputLength + 96 < pow2 32} ->
	toHashBuffer: hbytes{disjoint input toHashBuffer} ->
	toHashBufferLength: uint32_t{v toHashBufferLength = length toHashBuffer /\ v toHashBufferLength = v inputLength + 96 } ->
	Stack unit 
		(
			requires (fun h0 -> live h0 input /\ live h0 toHashBuffer)
		)	 
		(
			ensures (fun h0 _ h1 -> live h1 input /\ live h1 toHashBuffer /\ modifies_1 toHashBuffer h0 h1)
		)

let _ECVRF_hash_to_curve_i input inputLength toHashBuffer toHashBufferLength = 
	blit input 0ul toHashBuffer 0ul inputLength



val _ECVRF_hash_to_curve_pk:
	inputLength: uint32_t{v inputLength + 96 < pow2 32} ->
	toHashBuffer: hbytes ->
	toHashBufferLength: uint32_t{v toHashBufferLength = length toHashBuffer /\ v toHashBufferLength = v inputLength + 96 } ->
	publicKey: point->
	Stack unit
		(
			requires (fun h0 -> live h0 toHashBuffer /\ live h0 publicKey /\ 
				red_513 (as_seq h0 (Hacl.Impl.Ed25519.ExtPoint.getx publicKey)) /\
				red_513 (as_seq h0 (Hacl.Impl.Ed25519.ExtPoint.gety publicKey)) /\
				red_513 (as_seq h0 (Hacl.Impl.Ed25519.ExtPoint.getz publicKey)) /\
				red_513 (as_seq h0 (Hacl.Impl.Ed25519.ExtPoint.gett publicKey)))
		)
		(
			ensures (fun h0 _ h1 -> live h1 toHashBuffer /\ live h1 publicKey /\ modifies_1 toHashBuffer h0 h1)
		)

let _ECVRF_hash_to_curve_pk inputLength toHashBuffer toHashBufferLength  publicKey = 
	let placeForPublicKey = Buffer.sub toHashBuffer inputLength 32ul in 
	_ECP2OS placeForPublicKey publicKey

let _ECVRF_hash_to_curve pointBuffer publicKey input inputLength  = 
			push_frame();
		let h0 = ST.get() in 

			let sizeToHashBuffer = inputLength +^ 96ul  in 
				assert(v sizeToHashBuffer < pow2 32);
			let haclZero = Hacl.Cast.uint8_to_sint8 0uy in 
			let toHashBuffer = create haclZero sizeToHashBuffer in 
			let sizeInput = inputLength +^ 32ul in 

		let h1 = ST.get() in 

			assert(modifies_0 h0 h1);

			assert(live h1 publicKey);	

			_ECVRF_hash_to_curve_i input inputLength toHashBuffer sizeToHashBuffer;
		let h2 = ST.get() in

			assert(modifies_1 toHashBuffer h1 h2);
			(*)assert(live h2 publicKey);*)
			(*assume(red_513 (as_seq h2 (Hacl.Impl.Ed25519.ExtPoint.getx publicKey)) /\
				red_513 (as_seq h2 (Hacl.Impl.Ed25519.ExtPoint.gety publicKey)) /\
				red_513 (as_seq h2 (Hacl.Impl.Ed25519.ExtPoint.getz publicKey)) /\
				red_513 (as_seq h2 (Hacl.Impl.Ed25519.ExtPoint.gett publicKey)));	*)
			_ECVRF_hash_to_curve_pk inputLength toHashBuffer sizeToHashBuffer publicKey;

		let h3 = ST.get() in 
			assert(modifies_1 toHashBuffer h2 h3);
		let r = _helper_ECVRF_hash_to_curve pointBuffer toHashBuffer sizeInput (0uL, 0uL, 0uL, 0uL) in
		let h4 = ST.get() in 
			assert(modifies_2 pointBuffer toHashBuffer h3 h4);

			pop_frame();
				assert(live h4 pointBuffer);
				assert (live h4 publicKey);
				assert (live h4 input);
				assume(modifies_1 pointBuffer h0 h4);
		r
