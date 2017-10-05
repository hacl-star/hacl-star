module Division

open FStar.HyperStack.All
open FStar.Buffer
open FStar.Int.Cast

open Shift 
open Comparison
open Addition
open Lib

module U32 = FStar.UInt32
module U64 = FStar.UInt64

type rem_state (rLen:bnlen) (modLen:bnlen) = lbignum U32.(rLen +^ modLen +^ modLen +^ rLen)

let get_r_i #r #m (st:rem_state r m) : lbignum r = Buffer.sub st 0ul r
let get_mod #r #m (st:rem_state r m) : lbignum m = Buffer.sub st r m
let get_mod_1 #r #m (st:rem_state r m) : lbignum m = Buffer.sub st U32.(r +^ m) m
let get_tmp #r #m (st:rem_state r m) :lbignum r = Buffer.sub st U32.(r +^ m +^ m) r

let rem_state_inv r m (st:rem_state r m) = 
           let r_i = get_r_i st in
           let tmp = get_tmp st in
           let mod = get_mod st in
           let mod_1 = get_mod_1 st in
           let r = frameOf r_i in
	     r == frameOf mod /\
	     r == frameOf mod_1 /\
	     r == frameOf tmp /\
	     disjoint r_i tmp /\
	     disjoint r_i mod /\
	     disjoint r_i mod_1 /\ 
	     disjoint tmp mod /\ 
	     disjoint tmp mod_1 /\ 
       	 disjoint mod mod_1 


let rem_state_st_inv (rLen:bnlen) (modLen:bnlen) (st:rem_state rLen modLen) (h:FStar.HyperStack.mem) = 
	     rem_state_inv rLen modLen st /\ live h st

val remainder_loop:
    rLen:bnlen ->
    modLen:bnlen ->
    count:U32.t ->
    st:rem_state rLen modLen -> Stack unit
        (requires (fun h -> rem_state_st_inv rLen modLen st h))
	    (ensures (fun h0 _ h1 -> rem_state_st_inv rLen modLen st h1 /\
			   modifies_1 st h0 h1))

let rec remainder_loop rLen modLen count st =
    let r_i = get_r_i st in
    let mod = get_mod st in
    let mod1 = get_mod_1 st in
    let tmp = get_tmp st in
    if U32.(count >^ 0ul) then begin
        rshift1 modLen mod mod1;
        let tmp_b = isMore modLen rLen mod r_i in
        (if not tmp_b then begin
		    sub rLen modLen r_i mod tmp;
            blit tmp 0ul r_i 0ul rLen end);
        blit mod1 0ul mod 0ul modLen;
        remainder_loop rLen modLen U32.(count -^ 1ul) st
        end

(* res = a % mod *)
val remainder:
    aLen:bnlen ->
    modLen:bnlen{U32.v modLen <= U32.v aLen} ->
    resLen:bnlen{U32.v resLen <= U32.v modLen} ->
    diffBits:U32.t{U32.v diffBits = op_Multiply 64 (U32.v aLen - U32.v modLen)} ->
    a:lbignum aLen ->
    mod:lbignum modLen{disjoint mod a} ->
    res:lbignum resLen{disjoint res a /\ disjoint res mod} -> Stack unit
	    (requires (fun h -> live h a /\ live h mod /\ live h res))
	    (ensures (fun h0 _ h1 -> live h0 a /\ live h0 mod /\  live h0 res /\
            live h1 a /\ live h1 mod /\ live h1 res /\ modifies_1 res h0 h1))

#set-options "--z3rlimit 150"

let remainder aLen modLen resLen diffBits a mod res =
    push_frame();
    let modk = U32.(diffBits /^ 64ul) in
    let mod1Len = U32.(modLen +^ modk +^ 1ul) in
    (**) assume(U32.v mod1Len > 0 /\ U32.v mod1Len <= 8192);
    let a1Len = U32.(aLen +^ 1ul) in
    (**) assume(U32.v a1Len > 0 /\ U32.v a1Len <= 8192);
    let mod1Len: bnlen = mod1Len in
    let a1Len: bnlen = a1Len in
    (**) assert(U32.v a1Len = U32.v mod1Len);
    let st : rem_state a1Len mod1Len = create 0uL U32.(a1Len +^ a1Len +^ mod1Len +^ mod1Len) in
    let r_0 = get_r_i st in
    let mod1 = get_mod st in
    lshift modLen mod diffBits mod1;
    blit a 0ul r_0 0ul aLen;
    remainder_loop a1Len mod1Len U32.(diffBits +^ 1ul) st;
    blit r_0 0ul res 0ul resLen;
    pop_frame()

    (*(if U32.(isMore aLen modLen a mod) then begin
        lshift modLen mod diffBits mod1;
        blit a 0ul r_0 0ul aLen;
        remainder_loop a1Len mod1Len U32.(diffBits +^ 1ul) st;
        blit r_0 0ul res 0ul resLen end
    else
        assume(U32.v aLen <= U32.v resLen); 
        blit a 0ul res 0ul aLen); *)