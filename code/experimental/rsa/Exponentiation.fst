module Exponentiation

open FStar.HyperStack.All
open FStar.Buffer
open FStar.Int.Cast
open FStar.All

open Multiplication
open Division

module U32 = FStar.UInt32
module U64 = FStar.UInt64

type bignum = buffer FStar.UInt64.t

let bn_bits2 = 64ul 

(* check if input[ind] is equal to 1 *)
val bn_bit_is_set:
    input:bignum -> ind:U32.t{U32.(v (ind /^ bn_bits2)) < length input} -> Stack bool
    (requires (fun h -> live h input))
    (ensures  (fun h0 r h1 -> live h0 input /\ live h1 input))
let bn_bit_is_set input ind =
    push_frame();
    let i = U32.(ind /^ bn_bits2) in
    let j = U32.(ind %^ bn_bits2) in
    let tmp = input.(i) in
    let res = U64.(((tmp >>^ j) &^ 1uL) =^ 1uL) in
    pop_frame();
    res

val mod_exp_loop:
    modBits:U32.t -> aLen:U32.t -> bBits:U32.t -> resLen:U32.t -> 
    n:bignum -> tmpV:bignum{U32.v aLen = length tmpV} -> b:bignum ->
    res:bignum{U32.v resLen = length res} -> count:U32.t{U32.v count < length b} -> Stack unit
    (requires (fun h -> live h n /\ live h tmpV /\ live h b /\ live h res))
    (ensures  (fun h0 r h1 -> live h1 n /\ live h1 tmpV /\ live h1 b /\ live h1 res /\ modifies_1 res h0 h1 /\ modifies_1 tmpV h0 h1))
let rec mod_exp_loop modBits aLen bBits resLen n tmpV b res count =
    push_frame();
    let tmpLen = U32.(2ul *^ aLen) in
    let tmp = create 0uL tmpLen in
    let tmpBits = U32.(tmpLen *^ 64ul) in
    let tmpLen2 = U32.(aLen +^ resLen) in
    let tmp2 = create 0uL tmpLen2 in
    let tmpBits2 = U32.(tmpLen2 *^ 64ul) in
    (if U32.(count <^ bBits) then
        (sqr aLen tmpV tmp;
        remainder tmpBits modBits aLen tmp n tmpV;
        (if (bn_bit_is_set b count) then
        (mult resLen aLen res tmpV tmp2; 
        remainder tmpBits2 modBits resLen tmp2 n res));
        mod_exp_loop modBits aLen bBits resLen n tmpV b res U32.(count +^ 1ul)));
    pop_frame()

(* res = a ^^ b mod n *)
val mod_exp:
    modBits:U32.t -> aLen:U32.t -> bBits:U32.t -> resLen:U32.t -> 
    n:bignum -> a:bignum{U32.v aLen = length a} -> b:bignum -> 
    res:bignum{U32.v resLen = length res} -> Stack unit
    (requires (fun h -> live h n /\ live h a /\ live h b /\ live h res))
    (ensures  (fun h0 r h1 -> live h1 n /\ live h1 a /\ live h1 b /\ live h1 res /\ modifies_1 res h0 h1))
let mod_exp modBits aLen bBits resLen n a b res =
    push_frame();
    let tmpV = create 0uL aLen in
    blit a 0ul tmpV 0ul aLen;

    if (bn_bit_is_set b 0ul) then
    blit a 0ul res 0ul aLen
    else res.(0ul) <- 1uL;

    mod_exp_loop modBits aLen bBits resLen n b res tmpV 1ul;
    pop_frame()