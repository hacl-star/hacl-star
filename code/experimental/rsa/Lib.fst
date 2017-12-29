module Lib

open FStar.HyperStack.All
open FStar.Buffer
open FStar.Mul

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
open U32

type lbytes  (len:U32.t) = b:buffer U8.t{length b = U32.v len}
type lbignum (len:U32.t) = b:buffer U64.t{length b = U32.v len}

(* text_to_bn *)
val get_size_nat: lenText:U32.t{v lenText > 0} -> Tot (res:U32.t{v res > 0})
let get_size_nat lenText = ((lenText -^ 1ul) >>^ 3ul) +^ 1ul

val bits_to_bn: bits:U32.t{v bits > 0} -> Tot (res:U32.t{v res > 0})
let bits_to_bn bits = ((bits -^ 1ul) >>^ 6ul) +^ 1ul

val bits_to_text: bits:U32.t{v bits > 0} -> Tot (res:U32.t{v res > 0})
let bits_to_text bits = ((bits -^ 1ul) >>^ 3ul) +^ 1ul

(* check if input[ind] is equal to 1 *)
val bn_is_bit_set:
    len:U32.t ->
    input:lbignum len ->
    ind:U32.t{v ind / 64 < v len} -> Stack bool
    (requires (fun h -> True))
    (ensures  (fun h0 r h1 -> True))
let bn_is_bit_set len input ind =
    let i = ind /^ 64ul in
    let j = ind %^ 64ul in
    let tmp = input.(i) in
    let res = U64.(((tmp >>^ j) &^ 1uL) =^ 1uL) in
    res

val bn_set_bit:
    len:U32.t ->
    input:lbignum len ->
    ind:U32.t{v ind / 64 < v len} -> Stack unit
    (requires (fun h -> True))
    (ensures  (fun h0 r h1 -> True))
let bn_set_bit len input ind =
    let i = ind /^ 64ul in
    let j = ind %^ 64ul in
    let tmp = input.(i) in
    input.(i) <- U64.(tmp |^ (1uL <<^ j))