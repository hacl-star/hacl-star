module Lib

open FStar.HyperStack.All
open FStar.Buffer
open FStar.Int.Cast
open FStar.All
open FStar.Mul

module U32 = FStar.UInt32
module U64 = FStar.UInt64
open U32

type uint8_p = buffer FStar.UInt8.t
type lbytes (len:U32.t) = b:uint8_p{length b = U32.v len}
type blen = (l:U32.t{U32.v l > 0 /\ U32.v l <= 65536})

type bignum = buffer FStar.UInt64.t
type lbignum (len:U32.t) = b:bignum{length b = U32.v len}
type bnlen = (l:U32.t{U32.v l > 0 /\ U32.v l <= 8192})

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

(* check if input[ind] is equal to 1 *)
val bn_is_bit_set:
    input:bignum -> 
    ind:U32.t{U32.v ind / 64 < length input} -> Stack bool
    (requires (fun h -> live h input))
    (ensures  (fun h0 r h1 -> live h0 input /\ live h1 input))
let bn_is_bit_set input ind =
    let i = U32.(ind /^ 64ul) in
    let j = U32.(ind %^ 64ul) in
    let tmp = input.(i) in
    let res = U64.(((tmp >>^ j) &^ 1uL) =^ 1uL) in
    res

val bn_set_bit:
    len:bnlen -> input:lbignum len ->
    ind:U32.t{v ind / 64 < v len} -> Stack unit
    (requires (fun h -> live h input))
    (ensures  (fun h0 r h1 -> live h0 input /\ live h1 input))
let bn_set_bit len input ind =
    let i = U32.(ind /^ 64ul) in
    let j = U32.(ind %^ 64ul) in
    let tmp = input.(i) in
    input.(i) <- U64.(tmp |^ (1uL <<^ j))