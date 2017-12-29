module MGF

open FStar.HyperStack.All
open FStar.Buffer
open FStar.Int.Cast
open FStar.Mul

open Lib
open Convert

module U8 = FStar.UInt8
module U32 = FStar.UInt32
open U32

(* SHA 256 *)
let hLen = 32ul
assume val hash_sha256:
	mHash:lbytes hLen ->
	len:U32.t ->
	m:lbytes len -> Stack unit
	(requires (fun h -> True))
	(ensures (fun h0 _ h1 -> True))
//let hash_sha256 mHash len m = SHA2_256.hash mHash m len

(* Mask Generation Function *)
type mgf_state (accLen:U32.t) = lbytes (hLen +^ 4ul +^ 4ul +^ hLen +^ accLen)

let get_mgfseed_counter #a (st:mgf_state a) : lbytes (hLen +^ 4ul) = Buffer.sub st 0ul (hLen +^ 4ul)
let get_counter #a (st:mgf_state a) : lbytes 4ul = Buffer.sub st (hLen +^ 4ul) 4ul 
let get_mHash #a (st:mgf_state a) : lbytes hLen = Buffer.sub st (hLen +^ 4ul +^ 4ul) hLen
let get_acc #a (st:mgf_state a) : lbytes a = Buffer.sub st (hLen +^ 4ul +^ 4ul +^ hLen) a

val mgf_:
	count_max:U32.t ->
	mgfseed:lbytes hLen ->
	accLen:U32.t{v accLen = v hLen * v count_max} ->
	st:mgf_state accLen ->
	counter:U32.t{v counter <= v count_max} -> Stack unit
	(requires (fun h -> True))
	(ensures (fun h0 _ h1 -> True))

let rec mgf_ count_max mgfseed accLen st counter =
	if (counter <^ count_max) then begin
		let mgfseed_counter = get_mgfseed_counter st in
		let c = get_counter st in
		let mHash = get_mHash st in
		let acc = get_acc st in
		
		(**) assert(length c = 4);
		c.(0ul) <- uint32_to_uint8 (counter >>^ 24ul);
		c.(1ul) <- uint32_to_uint8 (counter >>^ 16ul);
		c.(2ul) <- uint32_to_uint8 (counter >>^ 8ul);
		c.(3ul) <- uint32_to_uint8 counter;
		
		(* blit mgfseed 0ul tmp 0ul 32ul; *)
		(**) assert(length mgfseed_counter = U32.v hLen + 4);
		blit c 0ul mgfseed_counter hLen 4ul;
		(**) assert(length mHash = U32.v hLen);
		hash_sha256 mHash (hLen +^ 4ul) mgfseed_counter;
		(**) assert(v hLen * v counter < length acc);
		(**) assert(v hLen * v counter + v hLen <= length acc);
		blit mHash 0ul acc (hLen *^ counter) hLen;
		mgf_ count_max mgfseed accLen st (counter +^ 1ul)
	end

val mgf_sha256:
	mgfseed:lbytes hLen ->
	len:U32.t ->
	res:lbytes len -> Stack unit
	(requires (fun h -> True))
	(ensures (fun h0 _ h1 -> True))
let mgf_sha256 mgfseed len res =
	push_frame();
	let count_max = (len -^ 1ul) /^ hLen +^ 1ul in
	let accLen = hLen *^ count_max in
	let stLen = hLen +^ 4ul +^ 4ul +^ hLen +^ accLen in
	let st:mgf_state accLen = create 0uy stLen in
	let mgfseed_counter = get_mgfseed_counter st in
	blit mgfseed 0ul mgfseed_counter 0ul hLen;
	mgf_ count_max mgfseed accLen st 0ul;
	let acc = get_acc st in
	blit acc 0ul res 0ul len;
	pop_frame()