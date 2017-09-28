module Exponentiation

open FStar.HyperStack.All
open FStar.Buffer
open FStar.Int.Cast
open FStar.All

open Multiplication
open Division
open Convert

module U32 = FStar.UInt32
module U64 = FStar.UInt64

type bignum = buffer FStar.UInt64.t

(* check if input[ind] is equal to 1 *)
val bn_bit_is_set:
    input:bignum -> 
    ind:U32.t{U32.v ind / 64 < length input} -> 
    Stack bool
    (requires (fun h -> live h input))
    (ensures  (fun h0 r h1 -> live h0 input /\ live h1 input))
let bn_bit_is_set input ind =
    let i = U32.(ind /^ 64ul) in
    let j = U32.(ind %^ 64ul) in
    let tmp = input.(i) in
    let res = U64.(((tmp >>^ j) &^ 1uL) =^ 1uL) in
    res

val mod_exp_loop:
    modBits:U32.t{U32.v modBits > 0} ->
    aLen:U32.t{U32.v aLen > 0} -> 
    bBits:U32.t{U32.v bBits > 0} -> 
    resLen:U32.t{U32.v resLen > 0} ->
    n:bignum{length n = U32.v (bits_to_bn modBits)} -> 
    tmpV:bignum{length tmpV = U32.v aLen} -> 
    b:bignum{length b = U32.v (bits_to_bn bBits)} ->
    res:bignum{length res = U32.v resLen} ->
    count:U32.t{U32.v count <= length b} -> Stack unit
    (requires (fun h -> live h n /\ live h tmpV /\ live h b /\ live h res))
    (ensures  (fun h0 _ h1 -> live h0 n /\ live h0 tmpV /\ live h0 b /\ live h0 res /\
        live h1 n /\ live h1 tmpV /\ live h1 b /\ live h1 res /\ 
        modifies_2 tmpV res h0 h1))
let rec mod_exp_loop modBits aLen bBits resLen n tmpV b res count =
    push_frame();
    let tmpLen = U32.(2ul *^ aLen) in
    let tmp = create 0uL tmpLen in
    
    let tmpLen2 = U32.(aLen +^ resLen) in
    let tmp2 = create 0uL tmpLen2 in
    let diffBits1 = U32.(64ul *^ 2ul *^ aLen -^ modBits) in
    let diffBits2 = U32.(64ul *^ (aLen +^ resLen) -^ modBits) in
    let modLen = bits_to_bn modBits in

    (if U32.(count <^ bBits) then
       (sqr aLen tmpV tmp;
       remainder tmpLen modLen aLen diffBits1 tmp n tmpV;
       (if (bn_bit_is_set b count) then
           (mult resLen aLen res tmpV tmp2;
            remainder tmpLen2 modLen resLen diffBits2 tmp2 n res));
        let count = U32.(count +^ 1ul) in
        mod_exp_loop modBits aLen bBits resLen n tmpV b res count));
    pop_frame()

(* res = a ^^ b mod n *)
val mod_exp:
    modBits:U32.t{U32.v modBits > 0} ->
    aLen:U32.t{U32.v aLen > 0} -> 
    bBits:U32.t{U32.v bBits > 0} -> 
    resLen:U32.t{U32.v resLen > 0} ->
    n:bignum{length n = U32.v (bits_to_bn modBits)} ->
    a:bignum{length a = U32.v aLen} ->
    b:bignum{length b = U32.v (bits_to_bn bBits)} ->
    res:bignum{length res = U32.v resLen} -> Stack unit
    (requires (fun h -> live h n /\ live h a /\ live h b /\ live h res))
    (ensures  (fun h0 _ h1 -> live h0 n /\ live h0 a /\ live h0 b /\ live h0 res /\
        live h1 n /\ live h1 a /\ live h1 b /\ live h1 res /\
        modifies_1 res h0 h1))
let mod_exp modBits aLen bBits resLen n a b res =
    push_frame();
    let tmpV = create 0uL aLen in
    blit a 0ul tmpV 0ul aLen;

    if (bn_bit_is_set b 0ul) then
        blit a 0ul res 0ul aLen
    else res.(0ul) <- 1uL;

    mod_exp_loop modBits aLen bBits resLen n b res tmpV 1ul;
    pop_frame()