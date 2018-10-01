module Convert

open FStar.HyperStack.All
open FStar.Buffer
open FStar.Int.Cast
open Hacl.Endianness
open Lib

module U32 = FStar.UInt32
module U8 = FStar.UInt8
module U64 = FStar.UInt64

(* text_to_bn *)
val get_size_nat: lenText:U32.t{U32.v lenText > 0} -> Tot (res:bnlen)
let get_size_nat lenText =
    let l = U32.(((lenText -^ 1ul) >>^ 3ul) +^ 1ul) in
    (**) assume(U32.v l > 0 /\ U32.v l <= 8192);
    l

val bits_to_bn: bits:U32.t{U32.v bits > 0} -> Tot (res:bnlen)
let bits_to_bn bits =
    let l = U32.(((bits -^ 1ul) >>^ 6ul) +^ 1ul) in
    (**) assume(U32.v l > 0 /\ U32.v l <= 8192);
    l

val bits_to_text: bits:U32.t{U32.v bits > 0} -> Tot (res:blen)
let bits_to_text bits =
    let l = U32.(((bits -^ 1ul) >>^ 3ul) +^ 1ul) in
    (**) assume(U32.v l > 0 /\ U32.v l <= 65536);
    l

val text_to_nat_loop:
    len:bnlen ->
	input:lbytes U32.(8ul *^ len) ->
    res:lbignum len{disjoint input res} ->
    i:U32.t{U32.v i <= U32.v len} -> Stack unit
    (requires (fun h -> live h input /\ live h res))
    (ensures (fun h0 _ h1 -> live h0 input /\ live h0 res /\
        live h1 input /\ live h1 res /\ modifies_1 res h0 h1))

let rec text_to_nat_loop len input res i =
    if U32.(i <^ len) then begin
        let inputi = hload64_be (sub input U32.(8ul *^ i) 8ul) in
        let ind = U32.(len -^ i -^ 1ul) in
        res.(ind) <- inputi;
        text_to_nat_loop len input res U32.(i +^ 1ul) end

val text_to_nat:
    len:blen ->
    input:lbytes len ->
    res:lbignum (get_size_nat len){disjoint input res} -> Stack unit
	(requires (fun h -> live h input /\ live h res))
	(ensures (fun h0 _ h1 -> live h0 input /\ live h0 res /\
        live h1 input /\ live h1 res /\ modifies_1 res h0 h1))

#set-options "--z3rlimit 50 --max_fuel 2"

let text_to_nat len input res =
    push_frame();
    let num_words = get_size_nat len in
    (**) assert(0 < U32.v num_words);
    let m = U32.(len %^ 8ul) in
    (**) assert(0 <= U32.v m /\ U32.v m < 8);
    (**) assume(FStar.Mul.(8 * U32.v num_words) <= 65536);
    let tmpLen = U32.(8ul *^ num_words) in
    (**) assert(FStar.Mul.(U32.(8 <= 8 * U32.v num_words)));
    (**) assert(FStar.Mul.(U32.v tmpLen = 8 * U32.v num_words));
    (**) assert(8 <= U32.v tmpLen);
    (**) assert(U32.(8 - (U32.v m) <= 8));
    (**) assert(U32.(8 - (U32.v m) <= U32.v tmpLen));
    let tmp = create 0uy tmpLen in
    let ind = if U32.(m =^ 0ul) then 0ul else U32.(8ul -^ m) in
    blit input 0ul tmp ind len;
    text_to_nat_loop num_words tmp res 0ul;
    pop_frame()


val nat_to_text_loop:
    len:bnlen ->
	input:lbignum len ->
    res:lbytes U32.(8ul *^ len){disjoint input res} ->
    i:U32.t{U32.v i <= U32.v len} -> Stack unit
    (requires (fun h -> live h input /\ live h res))
    (ensures (fun h0 _ h1 -> live h0 input /\ live h0 res /\
        live h1 input /\ live h1 res /\ modifies_1 res h0 h1))

let rec nat_to_text_loop len input res i =
    if U32.(i <^ len) then begin
        let ind = U32.(len -^ i -^ 1ul) in
        let tmp = input.(ind) in
        hstore64_be (sub res U32.(8ul *^ i) 8ul) tmp;
        nat_to_text_loop len input res U32.(i +^ 1ul) end

val nat_to_text:
    len:blen ->
    input:lbignum (get_size_nat len) ->
    res:lbytes len{disjoint res input} -> Stack unit
	(requires (fun h -> live h input /\ live h res))
	(ensures (fun h0 _ h1 -> live h0 input /\ live h0 res /\
        live h1 input  /\ live h1 res /\ modifies_1 res h0 h1))

let nat_to_text len input res =
    push_frame();
    let num_words = get_size_nat len in
    (**) assert(0 < U32.v num_words);
    let m = U32.(len %^ 8ul) in
    (**) assert(0 <= U32.v m /\ U32.v m < 8);
    (**) assume(FStar.Mul.(8 * U32.v num_words) <= 65536);
    let tmpLen = U32.(8ul *^ num_words) in
    (**) assert(FStar.Mul.(U32.(8 <= 8 * U32.v num_words)));
    (**) assert(FStar.Mul.(U32.v tmpLen = 8 * U32.v num_words));
    (**) assert(8 <= U32.v tmpLen);
    (**) assert(U32.(8 - (U32.v m) <= 8));
    (**) assert(U32.(8 - (U32.v m) <= U32.v tmpLen));
    let tmp = create 0uy tmpLen in
    nat_to_text_loop num_words input tmp 0ul;
    let ind = if U32.(m =^ 0ul) then 0ul else U32.(8ul -^ m) in
    blit tmp ind res 0ul len;
    pop_frame()