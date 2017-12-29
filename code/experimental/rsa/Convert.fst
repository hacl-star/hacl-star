module Convert

open FStar.HyperStack.All
open FStar.Buffer
open Hacl.Endianness
open Lib

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
open U32

val text_to_nat_:
    len:U32.t ->
    input:lbytes (8ul *^ len) ->
    res:lbignum len ->
    i:U32.t{v i <= v len} -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let rec text_to_nat_ len input res i =
    if (i <^ len) then begin
        let inputi = hload64_be (Buffer.sub input (8ul *^ i) 8ul) in
        let ind = len -^ i -^ 1ul in
        res.(ind) <- inputi;
        text_to_nat_ len input res (i +^ 1ul)
    end

val text_to_nat:
    len:U32.t ->
    input:lbytes len ->
    res:lbignum (get_size_nat len) -> Stack unit
	(requires (fun h -> True))
	(ensures (fun h0 _ h1 -> True))
let text_to_nat len input res =
    push_frame();
    let num_words = get_size_nat len in
    (**) assert(0 < U32.v num_words);
    let m = len %^ 8ul in
    (**) assert(0 <= U32.v m /\ U32.v m < 8);
    (**) assume(FStar.Mul.(8 * U32.v num_words) <= 65536);
    let tmpLen = 8ul *^ num_words in
    (**) assert(FStar.Mul.(U32.(8 <= 8 * U32.v num_words)));
    (**) assert(FStar.Mul.(U32.v tmpLen = 8 * U32.v num_words));
    (**) assert(8 <= U32.v tmpLen);
    (**) assert(U32.(8 - (U32.v m) <= 8));
    (**) assert(U32.(8 - (U32.v m) <= U32.v tmpLen));
    let tmp = create 0uy tmpLen in
    let ind = if (m =^ 0ul) then 0ul else 8ul -^ m in
    blit input 0ul tmp ind len;
    text_to_nat_ num_words tmp res 0ul;
    pop_frame()


val nat_to_text_:
    len:U32.t ->
	input:lbignum len ->
    res:lbytes (8ul *^ len) ->
    i:U32.t{v i <= v len} -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let rec nat_to_text_ len input res i =
    if (i <^ len) then begin
        let ind = len -^ i -^ 1ul in
        let tmp = input.(ind) in
        hstore64_be (Buffer.sub res (8ul *^ i) 8ul) tmp;
        nat_to_text_ len input res (i +^ 1ul)
    end

val nat_to_text:
    len:U32.t ->
    input:lbignum (get_size_nat len) ->
    res:lbytes len -> Stack unit
	(requires (fun h -> True))
	(ensures (fun h0 _ h1 -> True))
let nat_to_text len input res =
    push_frame();
    let num_words = get_size_nat len in
    (**) assert(0 < U32.v num_words);
    let m = len %^ 8ul in
    (**) assert(0 <= U32.v m /\ U32.v m < 8);
    (**) assume(FStar.Mul.(8 * U32.v num_words) <= 65536);
    let tmpLen = 8ul *^ num_words in
    (**) assert(FStar.Mul.(U32.(8 <= 8 * U32.v num_words)));
    (**) assert(FStar.Mul.(U32.v tmpLen = 8 * U32.v num_words));
    (**) assert(8 <= U32.v tmpLen);
    (**) assert(U32.(8 - (U32.v m) <= 8));
    (**) assert(U32.(8 - (U32.v m) <= U32.v tmpLen));
    let tmp = create 0uy tmpLen in
    nat_to_text_ num_words input tmp 0ul;
    let ind = if (m =^ 0ul) then 0ul else 8ul -^ m in
    blit tmp ind res 0ul len;
    pop_frame()