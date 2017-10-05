module Exponentiation

open FStar.HyperStack.All
open FStar.Buffer
open FStar.Int.Cast
open FStar.All

open Multiplication
open Convert
open Lib

module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Div = Division

type exp_state (rLen:bnlen) (aLen:bnlen) = lbignum U32.(rLen +^ aLen +^ (aLen +^ aLen) +^ (rLen +^ aLen))

let get_acc #r #a (st:exp_state r a) : lbignum r = Buffer.sub st 0ul r
let get_a_1 #r #a (st:exp_state r a) : lbignum a = Buffer.sub st r a
let get_a2 #r #a (st:exp_state r a) : lbignum U32.(a +^ a) = Buffer.sub st U32.(r +^ a) U32.(a +^ a)
let get_acc2 #r #a (st:exp_state r a) :lbignum U32.(a +^ r) = Buffer.sub st U32.(r +^ a +^ (a +^ a)) U32.(r +^ a)

let exp_state_inv r a (st:exp_state r a) = 
           let acc = get_acc st in
           let a = get_a_1 st in
           let a2 = get_a2 st in
           let acc2 = get_acc2 st in
           let r = frameOf acc in
	     r == frameOf a /\
	     r == frameOf a2 /\
	     r == frameOf acc2 /\
	     disjoint acc a /\
	     disjoint acc a2 /\
	     disjoint acc acc2 /\ 
	     disjoint a a2 /\ 
	     disjoint a acc2 /\ 
       	 disjoint acc2 a2 


let exp_state_st_inv (rLen:bnlen) (aLen:bnlen) (st:exp_state rLen aLen) (h:FStar.HyperStack.mem) = 
	     exp_state_inv rLen aLen st /\ live h st

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

val mod_exp_loop_:
    modBits:U32.t{U32.v modBits > 0} -> aLen:bnlen ->
    bBits:U32.t{U32.v bBits > 0} -> resLen:bnlen ->
    n:lbignum (bits_to_bn modBits) ->
    b:lbignum (bits_to_bn bBits) ->
    st:exp_state resLen aLen{disjoint st n /\ disjoint st b} ->
    count:U32.t{U32.v count <= U32.v bBits} -> Stack unit
    (requires (fun h -> live h n /\ live h b /\ exp_state_st_inv resLen aLen st h))
    (ensures  (fun h0 _ h1 -> live h1 n /\ live h1 b /\ exp_state_st_inv resLen aLen st h1 /\
                modifies_1 st h0 h1))

#set-options "--z3rlimit 150"

let mod_exp_loop_ modBits aLen bBits resLen n b st count =
    let acc = get_acc st in
    let a = get_a_1 st in
    let acc2 = get_acc2 st in
    let acc2Len = U32.(resLen +^ aLen) in
    fill acc2 0uL acc2Len;

    let diffBits2 = U32.(64ul *^ acc2Len -%^ modBits) in
    let modLen = bits_to_bn modBits in

    (if (bn_bit_is_set b count) then begin
        mult resLen aLen acc a acc2;
        Div.remainder acc2Len modLen resLen diffBits2 acc2 n acc
    end)

(* mod_exp_loop modBits aLen bBits resLen n a1 b acc count *)
val mod_exp_loop:
    modBits:U32.t{U32.v modBits > 0} -> aLen:bnlen ->
    bBits:U32.t{U32.v bBits > 0} -> resLen:bnlen ->
    n:lbignum (bits_to_bn modBits) ->
    b:lbignum (bits_to_bn bBits) ->
    st:exp_state resLen aLen{disjoint st n /\ disjoint st b} ->
    count:U32.t{U32.v count <= U32.v bBits} -> Stack unit
    (requires (fun h -> live h n /\ live h b /\ exp_state_st_inv resLen aLen st h))
    (ensures  (fun h0 _ h1 -> live h1 n /\ live h1 b /\ exp_state_st_inv resLen aLen st h1 /\
                modifies_1 st h0 h1))

#set-options "--z3rlimit 150 --max_fuel 2"

let rec mod_exp_loop modBits aLen bBits resLen n b st count =
    let a = get_a_1 st in
    let a2 = get_a2 st in
    let a2Len = U32.(aLen +^ aLen) in
    fill a2 0uL a2Len;

    let diffBits1 = U32.(64ul *^ a2Len -%^ modBits) in
    let modLen = bits_to_bn modBits in
    (if U32.(count <^ bBits) then begin
        sqr aLen a a2;
        Div.remainder a2Len modLen aLen diffBits1 a2 n a;
        mod_exp_loop_ modBits aLen bBits resLen n b st count;
        mod_exp_loop modBits aLen bBits resLen n b st U32.(count +^ 1ul)
    end)

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

#set-options "--z3rlimit 150 --max_fuel 0"

let mod_exp modBits aLen bBits resLen n a b res =
    push_frame();
    let st : exp_state resLen aLen = create 0uL U32.(resLen +^ aLen +^ (aLen +^ aLen) +^ (resLen +^ aLen)) in
    let acc = get_acc st in
    let a_1 = get_a_1 st in
    blit a 0ul a_1 0ul aLen;

    (if (bn_bit_is_set b 0ul) then
        blit a_1 0ul acc 0ul aLen
    else acc.(0ul) <- 1uL);

    mod_exp_loop modBits aLen bBits resLen n b st 1ul;
    blit acc 0ul res 0ul resLen;
    pop_frame()