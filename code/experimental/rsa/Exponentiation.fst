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
type exp_state (rLen:bnlen) (aLen:bnlen) = lbignum U32.(rLen +^ aLen +^ (2ul *^ aLen) +^ (aLen +^ rLen))

let get_r_i #r #a (st:exp_state r a) : lbignum r = Buffer.sub st 0ul r
let get_tmp #r #a (st:exp_state r a) : lbignum a = Buffer.sub st r a
let get_tmp2 #r #a (st:exp_state r a) : lbignum U32.(2ul *^ a) = Buffer.sub st U32.(r +^ a) U32.(2ul *^ a)
let get_r_itmp #r #a (st:exp_state r a) :lbignum U32.(a +^ r) = Buffer.sub st U32.(r +^ a +^ 2ul *^ a) U32.(a +^ r)

let exp_state_inv r a (st:exp_state r a) = 
           let r_i = get_r_i st in
           let tmp = get_tmp st in
           let tmp2 = get_tmp2 st in
           let r_itmp = get_r_itmp st in
           let r = frameOf r_i in
	     r == frameOf tmp /\
	     r == frameOf tmp2 /\
	     r == frameOf r_itmp /\
	     disjoint r_i tmp /\
	     disjoint r_i tmp2 /\
	     disjoint r_i r_itmp /\ 
	     disjoint tmp tmp2 /\ 
	     disjoint tmp r_itmp /\ 
       	 disjoint tmp2 r_itmp 


let exp_state_st_inv (rLen:bnlen) (aLen:bnlen) (st:exp_state rLen aLen) (h:FStar.HyperStack.mem) = 
	     exp_state_inv rLen aLen st /\ live h st
		       

(* check if input[ind] is equal to 1 *)
val bn_bit_is_set:
    input:bignum ->
    ind:U32.t{U32.v ind / 64 < length input} ->
    Stack bool
    (requires (fun h -> live h input))
    (ensures  (fun h0 _ h1 -> live h0 input /\ live h1 input /\ h0 == h1))

let bn_bit_is_set input ind =
    let i = U32.(ind /^ 64ul) in
    let j = U32.(ind %^ 64ul) in
    let tmp = input.(i) in
    let res = U64.(((tmp >>^ j) &^ 1uL) =^ 1uL) in
    res


val mod_exp_loop:
    modBits:U32.t{U32.v modBits > 0} -> aLen:bnlen ->
    bBits:U32.t{U32.v bBits > 0} -> resLen:bnlen ->
    n:lbignum (bits_to_bn modBits) ->
    b:lbignum (bits_to_bn bBits){disjoint n b} ->
    count:U32.t{U32.v count <= length b} ->
    st:exp_state resLen aLen{disjoint st n /\ disjoint st b} -> Stack unit
    (requires (fun h -> live h n /\ live h b /\ exp_state_st_inv resLen aLen st h))
    (ensures  (fun h0 _ h1 -> live h1 n /\ live h1 b /\ exp_state_st_inv resLen aLen st h1 /\
                modifies_1 st h0 h1))

let rec mod_exp_loop modBits aLen bBits resLen n b count st =   
    if U32.(count <^ bBits) then begin
        let r_i = get_r_i st in
        let tmp = get_tmp st in
        let tmp2 = get_tmp2 st in
        let r_itmp = get_r_itmp st in

        let diffBits1 = U32.(64ul *^ 2ul *^ aLen -^ modBits) in
        let diffBits2 = U32.(64ul *^ (aLen +^ resLen) -^ modBits) in
        let modLen = bits_to_bn modBits in

        (sqr aLen tmp tmp2;
        Div.remainder U32.(2ul *^ aLen) modLen aLen diffBits1 tmp2 n tmp;
        (if (bn_bit_is_set b count) then
            (mult resLen aLen r_i tmp r_itmp;
            Div.remainder U32.(aLen +^ resLen) modLen resLen diffBits2 r_itmp n r_i)));    
        mod_exp_loop modBits aLen bBits resLen n b U32.(count +^ 1ul) st
        end


(* res = a ^^ b mod n *)
val mod_exp:
    modBits:U32.t{U32.v modBits > 0} -> aLen:bnlen ->
    bBits:U32.t{U32.v bBits > 0} -> resLen:bnlen ->
    n:lbignum (bits_to_bn modBits) ->
    a:lbignum aLen{disjoint a n} ->
    b:lbignum (bits_to_bn bBits){disjoint b n /\ disjoint b a} ->
    res:lbignum resLen{disjoint res n /\ disjoint res a /\ disjoint res b} -> Stack unit
    (requires (fun h -> live h n /\ live h a /\ live h b /\ live h res))
    (ensures  (fun h0 _ h1 -> live h0 n /\ live h0 a /\ live h0 b /\ live h0 res /\
        live h1 n /\ live h1 a /\ live h1 b /\ live h1 res /\
        modifies_1 res h0 h1))

let mod_exp modBits aLen bBits resLen n a b res =
    push_frame();
    let st : exp_state resLen aLen = create 0uL U32.(resLen +^ aLen +^ (2ul *^ aLen) +^ (aLen +^ resLen)) in
    let r_0 = get_r_i st in
    let tmp = get_tmp st in
    blit a 0ul tmp 0ul aLen;

    (if (bn_bit_is_set b 0ul) then
        blit a 0ul r_0 0ul aLen
    else r_0.(0ul) <- 1uL);

    mod_exp_loop modBits aLen bBits resLen n b 1ul st;
    blit r_0 0ul res 0ul resLen;
    pop_frame()