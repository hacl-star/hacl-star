module Exponentiation

open FStar.HyperStack.All
open FStar.Buffer
open FStar.Int.Cast
open FStar.All

open Multiplication
open Convert

module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Div = Division

type bignum = buffer FStar.UInt64.t
type lbignum (len:U32.t) = 
     b:bignum{length b = U32.v len} 

type bnlen = (l:U32.t{U32.v l > 0 /\ U32.v l <= 8192})

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

(* mod_exp_loop modBits aLen bBits resLen n a1 b acc count *)
val mod_exp_loop:
    modBits:U32.t{U32.v modBits > 0} -> aLen:bnlen ->
    bBits:U32.t{U32.v bBits > 0} -> resLen:bnlen ->
    n:lbignum (bits_to_bn modBits) ->
    a:lbignum aLen ->
    b:lbignum (bits_to_bn bBits) ->
    acc:lbignum resLen ->
    count:U32.t{U32.v count <= U32.v bBits} -> Stack unit
    (requires (fun h -> live h n /\ live h a /\ live h b /\ live h acc))
    (ensures  (fun h0 _ h1 -> live h0 n /\ live h0 a /\ live h0 b /\ live h0 acc /\
        live h1 n /\ live h1 a /\ live h1 b /\ live h1 acc /\
        modifies_2 a acc h0 h1))

let rec mod_exp_loop modBits aLen bBits resLen n a b acc count =
    push_frame();
    let a2Len = U32.(aLen +^ aLen) in
    let acc2Len = U32.(resLen +^ aLen) in
    let a2 = create 0uL a2Len in
    let acc2 = create 0uL acc2Len in
    let a2_r = create 0uL aLen in

    let diffBits1 = U32.(64ul *^ a2Len -^ modBits) in
    let diffBits2 = U32.(64ul *^ acc2Len -^ modBits) in
    let modLen = bits_to_bn modBits in

    (if U32.(count <^ bBits) then begin
        sqr aLen a a2;
        Div.remainder a2Len modLen aLen diffBits1 a2 n a2_r;
        (if (bn_bit_is_set b count) then begin
            mult resLen aLen acc a2_r acc2;
            Div.remainder acc2Len modLen resLen diffBits2 acc2 n acc
        end);
        blit a2_r 0ul a 0ul aLen;
        mod_exp_loop modBits aLen bBits resLen n a b acc U32.(count +^ 1ul)
    end);
    pop_frame()

(* res = a ^^ b mod n *)
val mod_exp:
    modBits:U32.t{U32.v modBits > 0} -> aLen:bnlen ->
    bBits:U32.t{U32.v bBits > 0} -> resLen:bnlen ->
    n:lbignum (bits_to_bn modBits) ->
    a:lbignum aLen ->
    b:lbignum (bits_to_bn bBits) ->
    res:lbignum resLen -> Stack unit
    (requires (fun h -> live h n /\ live h a /\ live h b /\ live h res))
    (ensures  (fun h0 _ h1 -> live h0 n /\ live h0 a /\ live h0 b /\ live h0 res /\
        live h1 n /\ live h1 a /\ live h1 b /\ live h1 res /\
        modifies_1 res h0 h1))

let mod_exp modBits aLen bBits resLen n a b res =
    push_frame();
    let acc = create 0uL resLen in
    let a_1 = create 0uL aLen in
    blit a 0ul a_1 0ul aLen;

    (if (bn_bit_is_set b 0ul) then
        blit a_1 0ul acc 0ul aLen
    else acc.(0ul) <- 1uL);

    mod_exp_loop modBits aLen bBits resLen n a_1 b acc 1ul;
    blit acc 0ul res 0ul resLen;
    pop_frame()