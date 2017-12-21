module MGF

open FStar.HyperStack.All
open FStar.Buffer
open FStar.Int.Cast
open FStar.Mul

open Convert
open Lib

module U8 = FStar.UInt8
module U32 = FStar.UInt32

(* SHA 256 *)
let hLen = 32ul
val hash_sha256:
	mHash:lbytes hLen ->
	len:U32.t ->
	m:uint8_p{length m = U32.v len /\ disjoint mHash m} -> Stack unit
	(requires (fun h -> live h m /\ live h mHash))
	(ensures (fun h0 _ h1 -> live h0 m /\ live h0 mHash /\
	 						 live h1 m /\ live h1 mHash /\
							 modifies_1 mHash h0 h1))
		 
let hash_sha256 mHash len m = SHA2_256.hash mHash m len

(* Mask Generation Function *)
type mgf_state (accLen:blen) = lbytes U32.(hLen +^ 4ul +^ 4ul +^ hLen +^ accLen)

let get_mgfseed_counter #a (st:mgf_state a) : lbytes U32.(hLen +^ 4ul) = Buffer.sub st 0ul U32.(hLen +^ 4ul)
let get_counter #a (st:mgf_state a) : lbytes 4ul = Buffer.sub st U32.(hLen +^ 4ul) 4ul 
let get_mHash #a (st:mgf_state a) : lbytes hLen = Buffer.sub st U32.(hLen +^ 4ul +^ 4ul) hLen
let get_acc #a (st:mgf_state a) : lbytes a = Buffer.sub st U32.(hLen +^ 4ul +^ 4ul +^ hLen) a

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

val mgf_:
	count_max:U32.t ->
	mgfseed:lbytes hLen ->
	accLen:blen{U32.v accLen = (U32.v hLen) * (U32.v count_max)} -> 
	st:mgf_state accLen{disjoint st mgfseed} ->
	counter:U32.t{U32.v counter <= U32.v count_max} -> Stack unit
	(requires (fun h -> live h mgfseed /\ mgf_state_st_inv accLen st h ))
	(ensures (fun h0 _ h1 -> live h0 mgfseed /\ mgf_state_st_inv accLen st h0 /\
							 live h1 mgfseed /\ mgf_state_st_inv accLen st h1 /\
							 modifies_1 st h0 h1))

let rec mgf_ count_max mgfseed accLen st counter =
	if U32.(counter <^ count_max) then begin
		let mgfseed_counter = get_mgfseed_counter st in
		let c = get_counter st in
		let mHash = get_mHash st in
		let acc = get_acc st in
		
		(**) assert(length c = 4);
		c.(0ul) <- uint32_to_uint8 (U32.(counter >>^ 24ul));
		c.(1ul) <- uint32_to_uint8 (U32.(counter >>^ 16ul));
		c.(2ul) <- uint32_to_uint8 (U32.(counter >>^ 8ul));
		c.(3ul) <- uint32_to_uint8 counter;
		
		(* blit mgfseed 0ul tmp 0ul 32ul; *)
		(**) assert(length mgfseed_counter = U32.v hLen + 4);
		blit c 0ul mgfseed_counter hLen 4ul;
		(**) assert(length mHash = U32.v hLen);
		hash_sha256 mHash U32.(hLen +^ 4ul) mgfseed_counter;
		(**) assert((U32.v hLen) * (U32.v counter) < length acc);
		(**) assert((U32.v hLen) * (U32.v counter) + U32.v hLen <= length acc);
		blit mHash 0ul acc U32.(hLen *^ counter) hLen;
		mgf_ count_max mgfseed accLen st U32.(counter +^ 1ul) 
	end

val mgf_sha256:
	mgfseed:lbytes hLen ->
	len:blen -> res:lbytes len{disjoint mgfseed res} -> Stack unit
	(requires (fun h -> live h res /\ live h mgfseed))
	(ensures (fun h0 _ h1 -> live h0 res /\ live h0 mgfseed /\
							 live h1 res /\ live h1 mgfseed /\
							 modifies_1 res h0 h1))

let mgf_sha256 mgfseed len res =
	push_frame();
	let count_max = U32.((len -^ 1ul) /^ hLen +^ 1ul) in
	(**) assume(0 < (U32.v hLen) * (U32.v count_max) /\ (U32.v hLen) * (U32.v count_max) <= 65536);
	let accLen: blen  = U32.(hLen *^ count_max) in
	(**) assume(U32.v hLen + 4 + 4 + U32.v hLen + U32.v accLen > 0 /\ U32.v hLen + 4 + 4 + U32.v hLen + U32.v accLen <= 65536);
	let stLen = U32.(hLen +^ 4ul +^ 4ul +^ hLen +^ accLen) in
	let st: mgf_state accLen = create 0uy stLen in
	let mgfseed_counter = get_mgfseed_counter st in
	blit mgfseed 0ul mgfseed_counter 0ul hLen;
	mgf_ count_max mgfseed accLen st 0ul;
	let acc = get_acc st in
	blit acc 0ul res 0ul len;
	pop_frame()