
module VRF

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All
open FStar.ST
open FStar.Buffer

open Hacl.UInt8
open Hacl.UInt32
open FStar.UInt32


open Hacl.Hash.SHA2_256
open Hacl.Impl.Ed25519.Ladder.Step
open Hacl.Spec.Endianness
open Hacl.Bignum25519
open Hacl.Impl.Ed25519.PointAdd
open Hacl.Impl.Ed25519.Ladder

open Hacl.Impl.Ed25519.ExtPoint
open Hacl.Impl.Ed25519.PointCompress
open Hacl.Impl.Ed25519.PointDecompress

type bytes = buffer FStar.UInt8.t
type hbytes = buffer Hacl.UInt8.t

private let uint32_t  = FStar.UInt32.t
private let uint64_t = FStar.UInt64.t

open FStar.Mul
open FStar.UInt32
open FStar.HyperStack
open FStar.Seq
open FStar.Buffer

let max_input_len_8 = pow2 61

(* SHA2 *)
let size_word = 4ul 
let size_hash_w   = 8ul 
let size_block_w  = 16ul  // 16 words (Working data block size)
let size_hash     = size_word *^ size_hash_w

let n = 16ul

let cardinality = 1000 (*tochange *)



#reset-options "--max_fuel 0  --z3rlimit 20 --lax"


val hash: 
	hash: hbytes {length hash = v size_hash} ->
	input: hbytes {length input < max_input_len_8 /\ disjoint hash input} -> 
	len : uint32_t {v len = length input} -> 
	Stack unit 
		(requires 
			(fun h0 -> live h0 hash /\ live h0 input))
		(ensures	
			(fun h0 _ h1 -> live h0 input /\ live h0 hash /\ live h1 hash /\ modifies_1 hash h0 h1))

let hash hash input len = 
	Hacl.Hash.SHA2_256.hash hash input len

val scalarAddition:
  out:point ->
  p:point{disjoint p out} ->
  q:point{disjoint q out} ->
  Stack unit
    (requires (fun h -> live h out /\ live h p /\ live h q  /\
      (
        let x1 = as_seq h (getx p) in
        let y1 = as_seq h (gety p) in
        let z1 = as_seq h (getz p) in
        let t1 = as_seq h (gett p) in

        let x2 = as_seq h (getx q) in
        let y2 = as_seq h (gety q) in
        let z2 = as_seq h (getz q) in
        let t2 = as_seq h (gett q) in
        red_513 x1 /\ red_513 y1 /\ red_513 z1 /\ red_513 t1 /\
        red_513 x2 /\ red_513 y2 /\ red_513 z2 /\ red_513 t2)
      ))
    (ensures (fun h0 _ h1 -> live h1 out /\ live h0 p /\ live h0 q /\ modifies_1 out h0 h1 
    	(*/\
      (
        let x1 = as_seq h0 (getx p) in
        let y1 = as_seq h0 (gety p) in
        let z1 = as_seq h0 (getz p) in
        let t1 = as_seq h0 (gett p) in
        let x2 = as_seq h0 (getx q) in
        let y2 = as_seq h0 (gety q) in
        let z2 = as_seq h0 (getz q) in
        let t2 = as_seq h0 (gett q) in
        let x3 = as_seq h1 (getx out) in
        let y3 = as_seq h1 (gety out) in
        let z3 = as_seq h1 (getz out) in
        let t3 = as_seq h1 (gett out) in
        (seval x3, seval y3, seval z3, seval t3) ==
          Spec.Ed25519.point_add (seval x1, seval y1, seval z1, seval t1)
                                 (seval x2, seval y2, seval z2, seval t2)
        /\ red_513 x3 /\ red_513 y3 /\ red_513 z3 /\ red_513 t3) *)
  ))

let scalarAddition out p q = point_add out p q

val scalarMultiplication:
  result:point ->
  q:point ->
  scalar:buffer Hacl.UInt8.t{length scalar = 32} ->
  Stack unit
  	(requires (fun h -> Buffer.live h scalar /\ live h q /\ live h result /\ point_inv h q))
  	(ensures 
  		(fun h0 _ h1 -> Buffer.live h0 scalar /\ live h0 q /\ live h0 result
    		/\ point_inv h0 q /\ live h1 result /\ modifies_1 result h0 h1 /\ point_inv h1 result 
    	(*/\
    	(let r = as_point h1 result in
     let n  = reveal_sbytes (as_seq h0 scalar) in
     let q  = as_point h0 q in
     r == Spec.Ed25519.point_mul n q) )**)
    	)
  	)

let scalarMultiplication result  q scalar = point_mul result scalar q

val _ECP2OS: out: hbytes{length out = 32} -> p: point -> Stack unit 
	(requires
		(fun h0 -> live h0 out /\ live h0 p  /\
			red_513 (as_seq h0 (Hacl.Impl.Ed25519.ExtPoint.getx p)) /\
			red_513 (as_seq h0 (Hacl.Impl.Ed25519.ExtPoint.gety p)) /\
			red_513 (as_seq h0 (Hacl.Impl.Ed25519.ExtPoint.getz p)) /\
			red_513 (as_seq h0 (Hacl.Impl.Ed25519.ExtPoint.gett p))
		)
	)
	(ensures
		(fun h0 _ h1 -> 
			live h0 out /\ live h1 out /\ live h1 p /\  modifies_1 out h0 h1 
			(*/\ h1.[out] == Spec.Ed25519.point_compress(Hacl.Impl.Ed25519.ExtPoint.as_point h0 p)*)
		)
	)

let _ECP2OS out p = point_compress out p

val random: randomBuffer: hbytes {length randomBuffer = 32} -> 	
	Stack unit 
		(requires 
			(fun h0 -> live h0 randomBuffer)
		)
		(ensures 
			(fun h0 _ h1 -> live h1 randomBuffer /\ modifies_1 randomBuffer h0 h1)
		)

let random randomBuffer = 
	randomBuffer.(0ul) <- (Hacl.Cast.uint8_to_sint8 1uy)


val _OS2ECP: out: point -> number: hbytes{length number = 32} -> 
	Stack bool
		(requires (fun h0 -> live h0 out /\ live h0 number))
		(ensures 
			(fun h0 _ h1 -> live h1 out/\ live h1 number /\ modifies_1 out h0 h1)
		)

let _OS2ECP out number = 
	point_decompress out number	
(*)

val _ECVRF_hash_to_curve:
	output: point -> 
	publicKey: point{disjoint output publicKey}->
	input: hbytes ->
	inputLength : uint32_t {v inputLength = length input /\ v inputLength < pow2 32 - 65 } -> 
	fieldAsBuff: hbytes{length fieldAsBuff = 32 /\ disjoint fieldAsBuff input } -> 
	Stack bool 
		(requires
			(fun h0 -> live h0 output /\ live h0 publicKey /\ live h0 input /\
				red_513 (as_seq h0 (Hacl.Impl.Ed25519.ExtPoint.getx publicKey)) /\
				red_513 (as_seq h0 (Hacl.Impl.Ed25519.ExtPoint.gety publicKey)) /\
				red_513 (as_seq h0 (Hacl.Impl.Ed25519.ExtPoint.getz publicKey)) /\
				red_513 (as_seq h0 (Hacl.Impl.Ed25519.ExtPoint.gett publicKey))
			)
		)
		(ensures
			(fun h0 _ h1 -> live h1 output /\ live h1 publicKey /\ live h1 input /\ modifies_1 output h0 h1)
		)

let _ECVRF_hash_to_curve output publicKey input inputLength fieldAsBuff  = 
	push_frame();
		let counter = create (Hacl.Cast.uint8_to_sint8 0uy) 32ul in 
		let sizeToHashBuffer = 32ul + 32ul + 32ul + 32ul + inputLength in 
		let toHashBuffer = create (Hacl.Cast.uint8_to_sint8 0uy) sizeToHashBuffer in 
		blit toHashBuffer 0ul input 0ul inputLength;
		blit toHashBuffer inputLength publicKey 0ul 32ul;
	_helper_ECVRF_hash_to_curve toHashBuffer counter publicKey input inputLength fieldAsBuff
(* toHashBuffer = input + pk +  *)

(*)
		let pkBuffer = create (Hacl.Cast.uint8_to_sint8 0uy) 32ul in 
	_ECP2OS pkBuffer publicKey;
		let lengthFirstBuffer = add inputLength 32ul in (* 32 is length of the point*) 
		let firstBuffer = create (Hacl.Cast.uint8_to_sint8 0uy) lengthFirstBuffer in 
	concat firstBuffer input pkBuffer inputLength 32ul; 
		let lengthSecondBuffer = add lengthFirstBuffer 32ul  in 
		let secondBuffer = create (Hacl.Cast.uint8_to_sint8 0uy) lengthSecondBuffer in 
	concat secondBuffer firstBuffer ctr lengthFirstBuffer 32ul;
		let bufferForHash = create (Hacl.Cast.uint8_to_sint8 0uy) 32ul in 
	hash bufferForHash secondBuffer lengthSecondBuffer;
		let possiblePoint = pointCreate() in 
	let successful = _OS2ECP output bufferForHash in 
		counter_increment ctr;
	if successful then pop_frame (); true (* output point returns *)
	else if bufferComp ctr fieldAsBuff  then 
			_helper_ECVRF_hash_to_curve output ctr publicKey 
				input inputLength fieldAsBuff
	else (pointDelete output; pop_frame (); false)
(*)
val _ECVRF_hash_to_curve:
	output: point -> 
	publicKey: point{disjoint output publicKey}->
	input: hbytes ->
	inputLength : uint32_t {v inputLength = length input /\ v inputLength < pow2 32 - 65 } -> 
	fieldAsBuff: hbytes{length fieldAsBuff = 32 /\ disjoint fieldAsBuff input } -> 
	Stack bool 
		(requires
			(fun h0 -> live h0 output /\ live h0 publicKey /\ live h0 input /\
				red_513 (as_seq h0 (Hacl.Impl.Ed25519.ExtPoint.getx publicKey)) /\
				red_513 (as_seq h0 (Hacl.Impl.Ed25519.ExtPoint.gety publicKey)) /\
				red_513 (as_seq h0 (Hacl.Impl.Ed25519.ExtPoint.getz publicKey)) /\
				red_513 (as_seq h0 (Hacl.Impl.Ed25519.ExtPoint.gett publicKey))
			)
		)
		(ensures
			(fun h0 _ h1 -> live h1 output /\ live h1 publicKey /\ live h1 input /\ modifies_1 output h0 h1)
		)

let _ECVRF_hash_to_curve output publicKey input inputLength fieldAsBuff  = 
	let counter = create (Hacl.Cast.uint8_to_sint8 0uy) 32ul in 
	_helper_ECVRF_hash_to_curve output counter publicKey input inputLength fieldAsBuff




(*)
assume val bytesMultiplication: out: hbytes -> m1: bytes{disjoint out m1} -> m2 : hbytes -> mod: hbytes -> Stack unit 
	(requires (fun h0 -> live h0 out /\ live h0 m1))
	(ensures (fun h0 _ h1 -> live h1 m1 /\ modifies_1 out h0 h1))

assume val bytesInverse: out: bytes -> m: bytes -> Stack unit
	(requires(fun h0 -> live h0 out /\ live h0 m))
	(ensures (fun h0 _ h1 -> live h1 m /\ modifies_1 out h0 h1))	

assume val bytesAddition: out: hbytes -> m1: hbytes -> m2: hbytes -> Stack unit
	(requires (fun h0 -> live h0 out /\ live h0 m1 /\ live h0 m2))
	(ensures (fun h0 _ h1 -> live h1 out /\ modifies_1 out h0 h1 /\ live h1 m1 /\ live h1 m2))

assume val bytesConcat: out: bytes -> m1: bytes -> m2: bytes -> Stack unit
	(requires (fun h0 -> live h0 out /\ live h0 m1 /\ live h0 m2))
	(ensures (fun h0 _ h1 -> live h1 out /\ live h1 m1 /\ live h1 m2 /\ modifies_1 out h0 h1))

assume val bytesSplit: out: bytes -> m: bytes ->  p1: int -> p2: int -> Stack unit
	(requires (fun h0 -> live h0 out /\ live h0 m))
	(ensures (fun h0 _ h1 -> live h1 out /\ live h1 m /\ modifies_1 out h0 h1 ))

assume val _ECVRF_hash_points : out: hbytes {length out = 32} -> 
	generator : point -> h: point -> publicKey : point -> 
	gamma: point -> gk: point -> hk: point -> 
	Stack unit 
		(requires
			(fun h0 -> live h0 out /\ live h0 generator /\ live h0 h /\ live h0 publicKey /\
				live h0 gamma /\ live h0 gk /\ live h0 hk
			)
		)
		(ensures 
			(fun h0 _ h1 -> live h1 out /\ live h1 generator /\ live h1 h /\ live h1 publicKey /\
				live h1 gamma /\ live h1 gk /\ live h1 hk
			)
		)

val _ECVRF_prove: 
	proof: bytes{length proof = 96} ->
	input: hbytes  ->
	inputLength : uint32_t {v inputLength = length input /\ v inputLength < pow2 32 - 65 } -> 
	publicKey: point -> 
	privateKey: hbytes {length privateKey = 32 /\ disjoint input privateKey} -> 
	generator: point -> 
	fieldAsBuff: hbytes {length fieldAsBuff = 32 /\ disjoint fieldAsBuff privateKey} -> 
	Stack bool 
		(requires 
			(fun h0 -> live h0 proof /\ live h0 input /\ live h0 publicKey /\ live h0 privateKey 
				/\ live h0 generator /\ live h0 fieldAsBuff /\
				red_513 (as_seq h0 (Hacl.Impl.Ed25519.ExtPoint.getx publicKey)) /\
				red_513 (as_seq h0 (Hacl.Impl.Ed25519.ExtPoint.gety publicKey)) /\
				red_513 (as_seq h0 (Hacl.Impl.Ed25519.ExtPoint.getz publicKey)) /\
				red_513 (as_seq h0 (Hacl.Impl.Ed25519.ExtPoint.gett publicKey)) 
			)
		)
		(ensures
			(fun h0 _ h1 -> live h1 proof /\ live h1 input /\ live h1 publicKey /\ 
			live h1 privateKey /\ live h1 generator /\ live h1 fieldAsBuff /\  modifies_1 proof h0 h1)
		)

let _ECVRF_prove proof input inputLength publicKey privateKey generator fieldAsBuff  = 
		let h = pointCreate() in 
	let hashResult = _ECVRF_hash_to_curve h publicKey input inputLength fieldAsBuff in 
		if (not hashResult) then false else 
		let gamma = pointCreate () in 
	scalarMultiplication gamma h privateKey; 
		let k = create (Hacl.Cast.uint8_to_sint8 0uy) 32ul in 
		let gk = pointCreate() in 
		let hk = pointCreate() in 
	random k; 
	scalarMultiplication gk generator k;
	scalarMultiplication hk h k;
		let c = create (Hacl.Cast.uint8_to_sint8 0uy) 32ul  in
	_ECVRF_hash_points c generator h publicKey gamma gk hk; 
	(* length c = 32 *)
	(* length field = 32*)
	(* length max of next buffer = 64 *)
	(* modulo by field = 32*)
		let cqmod = create (Hacl.Cast.uint8_to_sint8 0uy) 32ul in 
	bytesMultiplication cqmod c(*hbytes*) fieldAsBuff fieldAsBuff; (* smaller than field*)
	bytesInverse cqmod cqmod;
		let s = create (Hacl.Cast.uint8_to_sint8 0uy) 32ul in 
	(* k is length 32*)
	(* cqmod is length 32  *)
	(* the biggest is 32 bits minus field*)
	bytesAddition s k cqmod;
		let pointBuffer = create 0uy 32ul in 
	_ECP2OS pointBuffer gamma; (* point = 32  *)
		let lengthSecondBuffer = add 32ul 32ul in 
		let fstsnd = create 0uy lengthSecondBuffer in 
	concat fstsnd pointBuffer c 32ul 32ul;
	concat proof fstsnd s 64ul 32ul; true

val _ECVRF_proof2hash: out: hbytes -> 
		proof: hbytes{length proof = 96 /\ disjoint out proof} -> 
		Stack unit
			(requires (fun h0 -> live h0 out /\ live h0 proof))
			(ensures (fun h0 _ h1 -> live h1 out /\ live h1 proof))

let _ECVRF_proof2hash out proof = 
	bytesSplit out proof 0 32

val _ECVRF_decode_proof: 
		gamma: point -> 
		c: hbytes{length c = 32} -> 
		s : hbytes{disjoint c s /\ length s = 32} -> 
		proof: hbytes{length proof = 96} -> 
		Stack bool
			(requires (fun h0 -> live h0 gamma /\ live h0 c /\ live h0 s /\ live h0 proof))
			(ensures (fun h0 _ h1 -> live h1 gamma /\ live h1 c /\ live h1 s /\ 
				live h1 proof /\ modifies_1 gamma h0 h1 /\ modifies_1 c h0 h1 /\ modifies_1 s h0 h1 ))

let _ECVRF_decode_proof gamma c s proof = 
		let bufferForPoint = create (Hacl.Cast.uint8_to_sint8 0uy) 32ul in 
	bytesSplit bufferForPoint proof 0 32;
	bytesSplit c proof 32 64;
	bytesSplit s proof 64 96;
		let successful = _OS2ECP gamma bufferForPoint in 
		(	
			if successful then true
			else 
				(pointDelete gamma; false)
		)			

val _ECVRF_verify: 
	generator: point -> 
	publicKey : point {disjoint generator publicKey}->
	proof: hbytes {length proof = 96} -> 
	input: hbytes {disjoint input proof} ->
	inputLength : uint32_t {v inputLength = length input /\  v inputLength < pow2 32 - 65} -> 
	fieldAsBuff: hbytes{length fieldAsBuff = 32 /\ disjoint fieldAsBuff input } -> 
	Stack bool
		(requires 
			(fun h0 -> live h0 generator /\ live h0 publicKey /\ live h0 proof /\ live h0 input)
		)
		(ensures 
			(fun h0 _ h1 -> live h1 generator /\ live h1 publicKey /\ live h1 proof /\ live h1 input)
		)

let _ECVRF_verify generator publicKey proof input inputLength fieldAsBuff = 
		let gamma = pointCreate () in 
		let c = create (Hacl.Cast.uint8_to_sint8 0uy) 32ul in  
		let s = create (Hacl.Cast.uint8_to_sint8 0uy) 32ul in 
	let decoded = _ECVRF_decode_proof gamma c s proof in 
		if not(decoded) 
			then false 
		else if not(isPointOnCurve gamma) 
			then false
		else 
		let pkc = pointCreate() in 
		let gs = pointCreate() in 
	scalarMultiplication pkc publicKey c;
	scalarMultiplication gs generator s;
		let u = pointCreate () in 
	scalarAddition u pkc gs; 
		let h = pointCreate () in 
	let h_ = _ECVRF_hash_to_curve h publicKey input inputLength fieldAsBuff in 
		if not(h_) 
			then false else 
		let gammac = pointCreate() in 
		let hs = pointCreate() in 
	scalarMultiplication gammac gamma c; 
	scalarMultiplication hs h s; 	
		let v = pointCreate() in 
	scalarAddition v gammac hs; 
		let c_prime = create (Hacl.Cast.uint8_to_sint8 0uy) 32ul in 
	_ECVRF_hash_points c_prime generator h publicKey gamma u v;
	bufferComp c c_prime