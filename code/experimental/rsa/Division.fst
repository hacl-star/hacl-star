module Division

open FStar.HyperStack.All
open FStar.Buffer
open FStar.Int.Cast

open Shift 
open Comparison
open Addition

module U32 = FStar.UInt32
module U64 = FStar.UInt64

type bignum = buffer FStar.UInt64.t
type lbignum (len:U32.t) = 
     b:bignum{length b = U32.v len} 

type bnlen = (l:U32.t{U32.v l > 0 /\ U32.v l <= 8192})

val remainder_loop:
    rLen:bnlen ->
    modLen:bnlen ->
    r_i:lbignum rLen ->
    mod:lbignum modLen ->
    count:U32.t -> Stack unit
        (requires (fun h -> live h r_i /\ live h mod))
	    (ensures (fun h0 _ h1 -> live h0 r_i /\ live h0 mod /\
            live h1 r_i /\ live h1 mod /\ modifies_2 mod r_i h0 h1))

let rec remainder_loop rLen modLen r_i mod count =
    push_frame();
    let mod1 = create 0uL modLen in
    let tmp = create 0uL rLen in
    (if U32.(count >^ 0ul) then begin
        rshift1 modLen mod mod1;
        let tmp_b = isMore modLen rLen mod r_i in
        (if not tmp_b then begin
		    sub rLen modLen r_i mod tmp; 
            blit tmp 0ul r_i 0ul rLen end);
        blit mod1 0ul mod 0ul modLen;    
        remainder_loop rLen modLen r_i mod U32.(count -^ 1ul)
        end);
    pop_frame()

(* res = a % mod *)
val remainder:
    aLen:bnlen ->
    modLen:bnlen{U32.v modLen <= U32.v aLen} ->
    resLen:bnlen{U32.v resLen <= U32.v modLen} ->
    diffBits:U32.t{U32.v diffBits = op_Multiply 64 (U32.v aLen - U32.v modLen)} ->
    a:lbignum aLen ->
    mod:lbignum modLen ->
    res:lbignum resLen -> Stack unit
	    (requires (fun h -> live h a /\ live h mod /\ live h res))
	    (ensures (fun h0 _ h1 -> live h0 a /\ live h0 mod /\  live h0 res /\
            live h1 a /\ live h1 mod /\ live h1 res /\ modifies_1 res h0 h1))

let remainder aLen modLen resLen diffBits a mod res =
    push_frame();
    let modk = U32.(diffBits /^ 64ul) in
    let mod1Len = U32.(modLen +^ modk +^ 1ul) in
    let mod1 = create 0uL mod1Len in
    lshift modLen mod diffBits mod1;
    let a1Len = U32.(aLen +^ 1ul) in
    let r0 = create 0uL a1Len in
    blit a 0ul r0 0ul aLen;
    remainder_loop a1Len mod1Len r0 mod1 diffBits;
    blit r0 0ul res 0ul resLen;
    pop_frame()