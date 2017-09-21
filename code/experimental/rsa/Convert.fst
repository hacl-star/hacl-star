module Convert

open FStar.HyperStack.All
open FStar.Buffer
open FStar.Int.Cast
open Hacl.Endianness

module U32 = FStar.UInt32
module U8 = FStar.UInt8
module U64 = FStar.UInt64

type uint8_p = buffer FStar.UInt8.t
type bignum = buffer FStar.UInt64.t

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
	input:uint8_p ->
    res:bignum{disjoint input res} ->
    len:U32.t{length res = U32.v len /\ FStar.Mul.(8 * U32.v len) < pow2 32 /\ length input = U32.(v (8ul *^ len))} ->
    i:U32.t{U32.v i <= U32.v len} -> Stack unit
    (requires (fun h -> live h input /\ live h res))
    (ensures (fun h0 _ h1 -> live h0 input /\ live h0 res /\
        live h1 input /\ live h1 res /\ modifies_1 res h0 h1))

let rec text_to_nat_loop input res len i =
    if U32.(i <^ len) then
        begin
        let inputi = hload64_be (sub input U32.(8ul *^ i) 8ul) in
        let ind = U32.(len -^ i -^ 1ul) in
        res.(ind) <- inputi;
        text_to_nat_loop input res len U32.(i +^ 1ul)
        end
    else ()

val text_to_nat:
    input:uint8_p ->
    len:U32.t{U32.v len = length input /\ U32.v len > 0} ->
    res:bignum{length res = U32.v (get_size_nat len) /\ length res > 0 /\ disjoint input res} -> Stack unit
	(requires (fun h -> live h input /\ live h res))
	(ensures (fun h0 _ h1 -> live h0 input /\ live h0 res /\
        live h1 input /\ live h1 res /\ modifies_1 res h0 h1))

#set-options "--z3rlimit 50 --max_fuel 2"

let text_to_nat input len res =
    push_frame();
    let num_words = get_size_nat len in
    assert(0 < U32.v num_words);
    let m = U32.(len %^ 8ul) in
    assert(0 <= U32.v m /\ U32.v m < 8);
    assume(FStar.Mul.(8 * U32.v num_words) < pow2 32);
    let tmpLen = U32.(8ul *^ num_words) in
    assert(FStar.Mul.(U32.(8 <= 8 * U32.v num_words)));
    assert(FStar.Mul.(U32.v tmpLen = 8 * U32.v num_words));
    assert(8 <= U32.v tmpLen);
    assert(U32.(8 - (U32.v m) <= 8));
    assert(U32.(8 - (U32.v m) <= U32.v tmpLen));
    let tmp = create 0uy tmpLen in
    let ind = if U32.(m =^ 0ul) then 0ul else U32.(8ul -^ m) in
    blit input 0ul tmp ind len;
    text_to_nat_loop tmp res num_words 0ul;
    pop_frame()

val nat_to_text_loop:
	input:bignum ->
    res:uint8_p{disjoint input res} ->
    len:U32.t{length input = U32.v len /\ FStar.Mul.(8 * U32.v len) < pow2 32 /\ length res = U32.(v (8ul *^ len))} ->
    i:U32.t{U32.v i <= U32.v len} -> Stack unit
    (requires (fun h -> live h input /\ live h res))
    (ensures (fun h0 _ h1 -> live h0 input /\ live h0 res /\
        live h1 input /\ live h1 res /\ modifies_1 res h0 h1))

let rec nat_to_text_loop input res len i =
    if U32.(i <^ len) then
        begin
        let ind = U32.(len -^ i -^ 1ul) in
        let tmp = input.(ind) in
        hstore64_be (sub res U32.(8ul *^ i) 8ul) tmp;
        nat_to_text_loop input res len U32.(i +^ 1ul)
        end
    else ()

val nat_to_text:
    input:bignum{length input > 0 } ->
    len:U32.t{U32.v len > 0 /\ length input = U32.v (get_size_nat len)} ->
    res:uint8_p{length res = U32.v len /\ disjoint res input} -> Stack unit
	(requires (fun h -> live h input /\ live h res))
	(ensures (fun h0 _ h1 -> live h0 input /\ live h0 res /\
        live h1 input  /\ live h1 res /\ modifies_1 res h0 h1))

let nat_to_text input len res =
    push_frame();
    let num_words = get_size_nat len in
    assert(0 < U32.v num_words);
    let m = U32.(len %^ 8ul) in
    assert(0 <= U32.v m /\ U32.v m < 8);
    assume(FStar.Mul.(8 * U32.v num_words) < pow2 32);
    let tmpLen = U32.(8ul *^ num_words) in
    assert(FStar.Mul.(U32.(8 <= 8 * U32.v num_words)));
    assert(FStar.Mul.(U32.v tmpLen = 8 * U32.v num_words));
    assert(8 <= U32.v tmpLen);
    assert(U32.(8 - (U32.v m) <= 8));
    assert(U32.(8 - (U32.v m) <= U32.v tmpLen));
    let tmp = create 0uy tmpLen in
    nat_to_text_loop input tmp num_words 0ul;
    let ind = if U32.(m =^ 0ul) then 0ul else U32.(8ul -^ m) in
    blit tmp ind res 0ul len;
    pop_frame()