module MGF

open FStar.HyperStack.All
open FStar.Buffer
open FStar.Int.Cast
open FStar.All
open FStar.Mul

open Convert
open Lib

module U32 = FStar.UInt32
module U8 = FStar.UInt8

val hash_sha256:
	mHash:lbytes 32ul ->
	len:U32.t ->
	m:uint8_p{length m = U32.v len /\ disjoint mHash m} -> Stack unit
	(requires (fun h -> live h m /\ live h mHash))
	(ensures (fun h0 _ h1 -> live h0 m /\ live h0 mHash /\
	 	live h1 m /\ live h1 mHash /\ modifies_1 mHash h0 h1))
		 
let hash_sha256 mHash len m = SHA2_256.hash mHash m len

type mgf_state (accLen:blen) = lbytes U32.(32ul +^ 4ul +^ 4ul +^ 32ul +^ accLen)

let get_mgfseed_counter #a (st:mgf_state a) : lbytes U32.(32ul +^ 4ul) = Buffer.sub st 0ul U32.(32ul +^ 4ul)
let get_counter #a (st:mgf_state a) : lbytes 4ul = Buffer.sub st U32.(32ul +^ 4ul) 4ul 
let get_mHash #a (st:mgf_state a) : lbytes 32ul = Buffer.sub st U32.(32ul +^ 4ul +^ 4ul) 32ul
let get_acc #a (st:mgf_state a) : lbytes a = Buffer.sub st U32.(32ul +^ 4ul +^ 4ul +^ 32ul) a

let mgf_state_inv a (st:mgf_state a) = 
           let mgfseed_counter = get_mgfseed_counter st in
		   let counter = get_counter st in
           let mHash = get_mHash st in
           let acc = get_acc st in
	       let r = frameOf mgfseed_counter in
		 r == frameOf counter /\  
	     r == frameOf mHash /\
	     r == frameOf acc /\
		 disjoint mgfseed_counter counter /\
	     disjoint mgfseed_counter mHash /\
	     disjoint mgfseed_counter acc /\
		 disjoint counter mHash /\
		 disjoint counter acc /\
	     disjoint mHash acc

let mgf_state_st_inv (aLen:blen) (st:mgf_state aLen) (h:FStar.HyperStack.mem) = 
	     mgf_state_inv aLen st /\ live h st

val mgf_loop:
	count_max:U32.t ->
	mgfseed:lbytes 32ul ->
	accLen:blen{U32.v accLen = 32 * (U32.v count_max)} -> 
	st:mgf_state accLen{disjoint st mgfseed} ->
	counter:U32.t{U32.v counter <= U32.v count_max} -> Stack unit
	(requires (fun h -> live h mgfseed /\ mgf_state_st_inv accLen st h ))
	(ensures (fun h0 _ h1 -> live h0 mgfseed /\ mgf_state_st_inv accLen st h0 /\
			live h1 mgfseed /\ mgf_state_st_inv accLen st h1 /\
			modifies_1 st h0 h1))

#set-options "--z3rlimit 150 --max_fuel 2"

let rec mgf_loop count_max mgfseed accLen st counter =
	if U32.(counter <^ count_max) then begin
		let mgfseed_counter = get_mgfseed_counter st in
		let c = get_counter st in
		let mHash = get_mHash st in
		let acc = get_acc st in
		
		(**) assert(length c = 4);
		(**) assert(length mgfseed_counter = 32 + 4);
		c.(0ul) <- uint32_to_uint8 (U32.(counter >>^ 24ul));
		c.(1ul) <- uint32_to_uint8 (U32.(counter >>^ 16ul));
		c.(2ul) <- uint32_to_uint8 (U32.(counter >>^ 8ul));
		c.(3ul) <- uint32_to_uint8 counter;
		
		(* blit mgfseed 0ul tmp 0ul 32ul; *)
		blit c 0ul mgfseed_counter 32ul 4ul;
		hash_sha256 mHash U32.(32ul +^ 4ul) mgfseed_counter;
		(**) assert(length mHash = 32);
		(**) assert(32 * (U32.v counter) < length acc);
		blit mHash 0ul acc U32.(32ul *^ counter) 32ul;
		mgf_loop count_max mgfseed accLen st U32.(counter +^ 1ul) end


val mgf_sha256:
	mgfseed:lbytes 32ul ->
	len:blen -> res:lbytes len{disjoint mgfseed res} -> Stack unit
	(requires (fun h -> live h res /\ live h mgfseed))
	(ensures (fun h0 _ h1 ->
		live h0 res /\ live h0 mgfseed /\
		live h1 res /\ live h1 mgfseed /\ modifies_1 res h0 h1))

#set-options "--z3rlimit 50"

let mgf_sha256 mgfseed len res =
	push_frame();
	let count_max = U32.((len -^ 1ul) /^ 32ul +^ 1ul) in
	(**) assume(32 * (U32.v count_max) > 0 /\ 32 * (U32.v count_max) <= 65536);
	let accLen: blen  = U32.(32ul *^ count_max) in
	(**) assume(32 + 4 + 4 + 32 + U32.v accLen > 0 /\ 32 + 4 + 4 + 32 + U32.v accLen <= 65536);
	let stLen = U32.(32ul +^ 4ul +^ 4ul +^ 32ul +^ accLen) in
	let st: mgf_state accLen = create 0uy stLen in
	let mgfseed_counter = get_mgfseed_counter st in
	blit mgfseed 0ul mgfseed_counter 0ul 32ul;
	mgf_loop count_max mgfseed accLen st 0ul;
	let acc = get_acc st in
	blit acc 0ul res 0ul len;
	pop_frame()