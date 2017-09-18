module Convert

open FStar.HyperStack.All
open FStar.Buffer
open FStar.Int.Cast

module U32 = FStar.UInt32
module U8 = FStar.UInt8
module U64 = FStar.UInt64

type uint8_p = buffer FStar.UInt8.t
type bignum = buffer FStar.UInt64.t

let bn_bytes = 8ul

(* text_to_bn *)
val get_size_nat: lenText:U32.t{U32.v lenText > 0} -> Tot (res:U32.t{U32.v res > 0})
let get_size_nat lenText =
    U32.(((lenText -^ 1ul) >>^ 3ul) +^ 1ul)

val bits_to_bn: bits:U32.t{U32.v bits > 0} -> Tot (res:U32.t{U32.v res > 0})
let bits_to_bn bits =
    U32.(((bits -^ 1ul) >>^ 6ul) +^ 1ul)

val bits_to_text: bits:U32.t{U32.v bits > 0} -> Tot (res:U32.t{U32.v res > 0})
let bits_to_text bits =
    U32.(((bits -^ 1ul) >>^ 3ul) +^ 1ul)

val text_to_nat_loop:
    input:uint8_p -> len:U32.t{U32.v len = length input /\ U32.v len > 0} ->
    res:bignum{length res = U32.v (get_size_nat len)} ->
    num_words:U32.t{U32.v num_words <= length res /\ U32.v num_words > 0} ->
    m:U32.t{0 <= U32.v m /\ U32.v m < 8} -> word:U64.t ->
    i:U32.t{U32.v i <= length input} -> Stack unit
    (requires (fun h -> live h input /\ live h res))
    (ensures (fun h0 _ h1 -> live h0 input /\ live h0 res /\ 
        live h1 input /\ live h1 res /\ modifies_1 res h0 h1))
      (* #set-options "--z3rlimit 20" *)
let rec text_to_nat_loop input len res num_words m word i =
    (* len = 8 * num_words + m *)
	if U32.(i <^ len) then
        begin
        let tmp = input.(i) in
	    let word = U64.((word <<^ 8ul) |^ uint8_to_uint64 tmp) in
	    let i = U32.(i +^ 1ul) in
        if U32.(m =^ 0ul) then
	        (let num_words = U32.(num_words -^ 1ul) in
	        res.(num_words) <- word;
	        text_to_nat_loop input len res num_words 7ul 0uL i)
	    else
            (let m = U32.(m -^ 1ul) in
            text_to_nat_loop input len res num_words m word i)
        end
	else ()

val text_to_nat:
    input:uint8_p -> len:U32.t{U32.v len = length input /\ U32.v len > 0} ->
    res:bignum{length res = U32.v (get_size_nat len)} -> Stack unit
	(requires (fun h -> live h input /\ live h res))
	(ensures (fun h0 _ h1 -> live h0 input /\ live h0 res /\
        live h1 input /\ live h1 res /\ modifies_1 res h0 h1))
let text_to_nat input len res =
    let num_words = get_size_nat len in
    let m = U32.((len -^ 1ul) %^ bn_bytes) in
    text_to_nat_loop input len res num_words m 0uL 0ul

(*
val nat_to_text_loop:
    input:bignum -> res:uint8_p -> i:U32.t{U32.(v (i /^ bn_bytes)) <= length input} ->
    j:U32.t{U32.v j <= length res} -> Stack unit
	(requires (fun h -> live h input /\ live h res))
	(ensures (fun h0 _ h1 -> live h0 input /\ live h0 res /\ 
        live h1 input /\ live h1 res /\ modifies_1 res h0 h1))
let rec nat_to_text_loop input res i j =
    if U32.(i >^ 0ul) then
        let i = U32.(i -^ 1ul) in
        let ind = U32.(i /^ bn_bytes) in
        let l = input.(ind) in
        let tmp = U32.(i %^ bn_bytes) in
        res.(j) <- U8.(uint64_to_uint8 (U64.(l >>^ U32.(8ul *^ tmp))) &^ 0xffuy);
        let j = U32.(j +^ 1ul) in
        nat_to_text_loop input res i j
    else ()

val nat_to_text:
    input:bignum -> len:U32.t -> res:uint8_p{length res = U32.v len} -> Stack unit
	(requires (fun h -> live h input /\ live h res))
	(ensures (fun h0 _ h1 -> live h0 input /\ live h0 res /\ 
        live h1 input  /\ live h1 res /\ modifies_1 res h0 h1))
let nat_to_text input len res =
    nat_to_text_loop input res len 0ul
    *)