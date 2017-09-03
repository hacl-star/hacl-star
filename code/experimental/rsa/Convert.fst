module Convert

open FStar.HyperStack
open FStar.ST
open FStar.Buffer
open FStar.Int.Cast

module U32 = FStar.UInt32
module U8 = FStar.UInt8
module U64 = FStar.UInt64

type uint8_p = buffer FStar.UInt8.t
type bignum = buffer FStar.UInt64.t

let bn_bytes = 8ul

(* the length of the message in octets *)
val get_size_nat: lenText:U32.t -> Tot U32.t
let get_size_nat lenText =
     U32.((lenText -^ 1ul) /^ bn_bytes +^ 1ul)

val text_to_nat_loop: 
    input:uint8_p -> len:U32.t -> res:bignum ->
    num_words:U32.t{U32.v num_words <= length res} -> m:U32.t -> word:U64.t ->
    i:U32.t{U32.v i <= length input} -> ST unit
    (requires (fun h -> live h input /\ live h res))
    (ensures (fun h0 _ h1 -> live h0 input /\ live h0 res /\ live h1 input /\ live h1 res /\ modifies_1 res h0 h1))
let rec text_to_nat_loop input len res num_words m word i =
	if U32.(len >^ 0ul) then
    let len = U32.(len -^ 1ul) in
    let tmp = input.(i) in
	let word = U64.((word <<^ 8ul) |^ uint8_to_uint64 tmp) in
	let i = U32.(i +^ 1ul) in
	if U32.(m =^ 0ul) then
	    let num_words = U32.(num_words -^ 1ul) in
	    res.(num_words) <- word;
	    let word = 0uL in
        let m = U32.(bn_bytes -^ 1ul) in
	    text_to_nat_loop input len res num_words m word i
	else
        text_to_nat_loop input len res num_words U32.(m -^ 1ul) word i
	else ()

val text_to_nat:
    input:uint8_p -> len:U32.t{U32.v len = length input} -> res:bignum -> ST unit
	(requires (fun h -> live h input /\ live h res))
	(ensures (fun h0 _ h1 -> live h0 input /\ live h0 res /\ live h1 res /\ modifies_1 res h0 h1))
let text_to_nat input len res =
    let num_words = get_size_nat len in
    let m = U32.((len -^ 1ul) %^ bn_bytes) in
    text_to_nat_loop input len res num_words m 0uL 0ul

val nat_to_text_loop:
    input:bignum -> res:uint8_p -> i:U32.t -> 
    j:U32.t{U32.v j <= length res} -> ST unit
	(requires (fun h -> live h input /\ live h res))
	(ensures (fun h0 _ h1 -> live h0 input /\ live h0 res /\ live h1 res /\ modifies_1 res h0 h1))
let rec nat_to_text_loop input res i j =
    if U32.(i >^ 0ul) then
    let i = U32.(i -^ 1ul) in
    let ind = U32.(i /^ bn_bytes) in
    let l = input.(ind) in
    let tmp = U32.(i %^ bn_bytes) in (* a bug in F* ? *)
    res.(j) <- U8.(uint64_to_uint8 (U64.(l >>^ U32.(8ul *^ tmp))) &^ 0xffuy);
    nat_to_text_loop input res i U32.(j +^ 1ul)
    else () 

val nat_to_text:
    input:bignum -> len:U32.t -> res:uint8_p{length res = U32.v len} -> ST unit
	(requires (fun h -> live h input /\ live h res))
	(ensures (fun h0 _ h1 -> live h0 input /\ live h0 res /\ live h1 res /\ modifies_1 res h0 h1))
let nat_to_text input len res = 
    nat_to_text_loop input res len 0ul