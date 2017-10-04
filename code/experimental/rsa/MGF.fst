module MGF

open FStar.HyperStack.All
open FStar.Buffer
open FStar.Int.Cast
open FStar.All
open FStar.Mul

open Convert

module U32 = FStar.UInt32
module U8 = FStar.UInt8

type uint8_p = buffer FStar.UInt8.t
type lbytes (len:U32.t) =
     b:uint8_p{length b = U32.v len}

type blen = (l:U32.t{U32.v l > 0 /\ U32.v l <= 8192})

inline_for_extraction let hLen = 32ul

val hash_sha256:
	mHash:lbytes hLen ->
	len:blen ->
	m:lbytes len{disjoint mHash m} -> Stack unit
	(requires (fun h -> live h m /\ live h mHash))
	(ensures (fun h0 _ h1 -> live h0 m /\ live h0 mHash /\
	 	live h1 m /\ live h1 mHash /\ modifies_1 mHash h0 h1))
let hash_sha256 mHash len m = SHA2_256.hash mHash m len

type mgf_state (mgfseedLen:blen) (accLen:blen) = lbytes U32.((mgfseedLen +^ 4ul) +^ 4ul +^ 32ul +^ accLen)

let get_mgfseed_counter #m #a (st:mgf_state m a) : lbytes U32.(m +^ 4ul) = Buffer.sub st 0ul U32.(m +^ 4ul)
let get_counter #m #a (st:mgf_state m a) : lbytes 4ul = Buffer.sub st U32.(m +^ 4ul) 4ul 
let get_mHash #m #a (st:mgf_state m a) : lbytes 32ul = Buffer.sub st U32.(m +^ 4ul +^ 4ul) 32ul
let get_acc #m #a (st:mgf_state m a) : lbytes a = Buffer.sub st U32.(m +^ 4ul +^ 4ul +^ 32ul) a

let mgf_state_inv m a (st:mgf_state m a) = 
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

let mgf_state_st_inv (mLen:blen) (aLen:blen) (st:mgf_state mLen aLen) (h:FStar.HyperStack.mem) = 
	     mgf_state_inv mLen aLen st /\ live h st

val mgf_loop:
	mgfseedLen:blen -> mgfseed:lbytes mgfseedLen ->
	accLen:blen -> st:mgf_state mgfseedLen accLen {disjoint st mgfseed} ->
	counter:U32.t{32 * (U32.v counter + 1) <= U32.v accLen} -> Stack unit
	(requires (fun h -> live h mgfseed /\ mgf_state_st_inv mgfseedLen accLen st h ))
	(ensures (fun h0 _ h1 -> live h1 mgfseed /\ mgf_state_st_inv mgfseedLen accLen st h1 /\
			 modifies_1 st h0 h1))

#set-options "--z3rlimit 150 --max_fuel 2"

let rec mgf_loop mgfseedLen mgfseed accLen st counter =
	if U32.(32ul *^ counter <^ accLen) then begin
		let mgfseed_counter = get_mgfseed_counter st in
		let c = get_counter st in
		let mHash = get_mHash st in
		let acc = get_acc st in
		
		c.(0ul) <- uint32_to_uint8 (U32.(counter >>^ 24ul));
		c.(1ul) <- uint32_to_uint8 (U32.(counter >>^ 16ul));
		c.(2ul) <- uint32_to_uint8 (U32.(counter >>^ 8ul));
		c.(3ul) <- uint32_to_uint8 counter;
		
		(* blit mgfseed 0ul tmp 0ul mgfseedLen; *)
		blit c 0ul mgfseed_counter mgfseedLen 4ul;
		(* fill mHash 0uL hLen; *)
		assume(U32.v mgfseedLen + 4 > 0 /\ U32.v mgfseedLen + 4 <= 8192);
		hash_sha256 mHash U32.(mgfseedLen +^ 4ul) mgfseed_counter;
		blit mHash 0ul acc U32.(32ul *^ counter) 32ul;
		assert(32 * (U32.v counter + 1) <= U32.v accLen);
		mgf_loop mgfseedLen mgfseed accLen st U32.(counter +^ 1ul) end

val mgf:
	mgfseedLen:blen -> mgfseed:lbytes mgfseedLen ->
	len:blen -> res:lbytes len -> Stack unit
	(requires (fun h -> live h res /\ live h mgfseed))
	(ensures (fun h0 _ h1 -> live h1 res /\ live h1 mgfseed /\ modifies_1 res h0 h1))
	
let mgf mgfseedLen mgfseed len res =
	(* if len > op_Multiply (pow2 32) hLen then failwith "mask too long" *)
	push_frame();
	let count_max = U32.((len -^ 1ul) /^ hLen +^ 1ul) in
	let accLen = U32.(hLen *^ count_max) in
	assume(U32.v accLen > 0 /\ U32.v accLen <= 8192);
	let accLen: blen = accLen in
	let st: mgf_state mgfseedLen accLen = create 0uy U32.((mgfseedLen +^ 4ul) +^ 4ul +^ 32ul +^ accLen) in
	let mgfseed_counter = get_mgfseed_counter st in
	blit mgfseed 0ul mgfseed_counter 0ul mgfseedLen;
	mgf_loop mgfseedLen mgfseed accLen st 0ul;
	let acc = get_acc st in
	blit acc 0ul res 0ul len;
	pop_frame()