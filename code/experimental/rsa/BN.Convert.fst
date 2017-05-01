module BN.Convert

open FStar.HyperStack
open FStar.ST
open FStar.Buffer
open FStar.Int.Cast
open FStar.All

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U8 = FStar.UInt8

type uint8_p = buffer FStar.UInt8.t
type bignum = buffer FStar.UInt64.t

let bn_bytes = 8ul
let zero_64 = 0uL
let zero_32 = 0ul

val bn_bin2bn_loop: input: uint8_p -> ret: bignum -> len: U32.t -> num_words: U32.t -> m: U32.t -> word: U64.t -> i: U32.t -> ST unit
(requires (fun h -> live h input /\ live h ret))
(ensures (fun h0 _ h1 -> live h0 input /\ live h0 ret /\ live h1 input /\ live h1 ret /\ modifies_1 ret h0 h1))
let rec bn_bin2bn_loop input ret len num_words m word i =
	if U32.(len >^ 0ul) then
	let tmp = input.(i) in 
	let tmp = uint8_to_uint64 tmp in
	let word = U64.((word <<^ 8ul) |^ tmp) in
	let len = U32.(len -^ 1ul) in
	let i = U32.(i +^ 1ul) in
	if U32.(m =^ 0ul) then
		let num_words = U32.(num_words -^ 1ul) in
		ret.(num_words) <- word;
		let word = 0uL in
		let m = U32.(bn_bytes -^ 1ul) in
		bn_bin2bn_loop input ret len num_words m word i 
	else 
		let m = U32.(m -^ 1ul) in
		bn_bin2bn_loop input ret len num_words m word i
	else ()

val bn_bin2bn: input: uint8_p -> len: U32.t -> ret: bignum -> ST unit
(requires (fun h -> live h input /\ live h ret))
(ensures (fun h0 _ h1 -> live h0 input /\ live h0 ret /\ live h1 input /\ live h1 ret /\ modifies_1 ret h0 h1))
let bn_bin2bn input len ret =
	if U32.(len >^ 0ul) then
	let num_words = U32.((len -^ 1ul) /^ bn_bytes +^ 1ul) in
	let m = U32.((len -^ 1ul) %^ bn_bytes) in
	bn_bin2bn_loop input ret len num_words m zero_64 zero_32
	else ()

val bn_bn2bin_padded_loop: input: bignum -> out: uint8_p -> len: U32.t -> i: U32.t -> ST unit
(requires (fun h -> live h input /\ live h out))
(ensures (fun h0 _ h1 -> live h0 input /\ live h0 out /\ live h1 input /\ live h1 out /\ modifies_1 out h0 h1))
let rec bn_bn2bin_padded_loop input out len i =
	if U32.(len >^ 0ul) then
	let len = U32.(len -^ 1ul) in
	let l = input.(U32.(len /^ bn_bytes)) in
	let tmp = uint64_to_uint8 (U64.(l >>^ U32.(8ul *^ (len %^ bn_bytes)))) in
	out.(i) <- U8.(tmp &^ 0xffuy);
	let i = U32.(i +^ 1ul) in
	bn_bn2bin_padded_loop input out len i
	else ()

val get_border: len: U32.t -> Tot U32.t
let get_border len = U32.((len +^ (bn_bytes -^ 1ul)) /^ bn_bytes)

val bn_bn2bin_padded: len: U32.t -> input: bignum {length input < U32.v (get_border len)} -> out: uint8_p -> ST unit
(requires (fun h -> live h input /\ live h out))
(ensures (fun h0 _ h1 -> live h0 input /\ live h0 out /\ live h1 input /\ live h1 out /\ modifies_1 out h0 h1))
let bn_bn2bin_padded len input out =
	(* if input = zero then out = 0 *)
 	if not (U32.((len %^ bn_bytes) =^ 0ul)) then
		let l = input.(U32.(len /^ bn_bytes)) in
		let tmp = U64.(l >>^ U32.(8ul *^ (len %^ bn_bytes))) in
		(if U64.(tmp =^ zero_64) then bn_bn2bin_padded_loop input out len zero_32)
	else bn_bn2bin_padded_loop input out len zero_32