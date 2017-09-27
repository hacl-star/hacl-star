module Division

open FStar.HyperStack.All
open FStar.Buffer
open FStar.Int.Cast

open Convert
open Shift
open Comparison
open Addition

module ST = FStar.HyperStack.ST
module U32 = FStar.UInt32
module U64 = FStar.UInt64

type bignum = buffer FStar.UInt64.t

type lbytes (len:U32.t) = 
     b:buffer FStar.UInt64.t{length b = U32.v len} 

type bnlen = (l:U32.t{U32.v l > 0 /\ U32.v l <= 8192})
type rem_state (rLen:bnlen) (modLen:bnlen) = lbytes U32.(rLen +^ rLen +^ modLen +^ modLen)

let get_r_i #r #m (st:rem_state r m) : lbytes r = Buffer.sub st 0ul r
let get_tmp #r #m (st:rem_state r m) : lbytes r = Buffer.sub st r r
let get_mod #r #m (st:rem_state r m) : lbytes m = Buffer.sub st U32.(r +^ r) m
let get_mod_1 #r #m (st:rem_state r m) :lbytes m = Buffer.sub st U32.(r +^ r +^ m) m

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
		       

[@ "substitute"]
val remainder_r_i:
    rLen:bnlen -> modLen:bnlen{U32.v modLen = U32.v rLen} ->
    tmp_b:bool -> st:rem_state rLen modLen -> Stack unit 
    	       (requires (fun h -> rem_state_st_inv rLen modLen st h))
	       (ensures (fun h r h' -> rem_state_st_inv rLen modLen st h' /\
				     modifies_1 st h h'))
let remainder_r_i rLen modLen tmp_b st =
    if not tmp_b then
	let r_i = get_r_i st in
	let tmp = get_tmp st in
	let mod = get_mod st in
        sub rLen modLen r_i mod tmp;
        blit tmp 0ul r_i 0ul rLen

let lemma_modifies_0_is_modifies_1 (#a:Type) (h:HyperStack.mem) (b:buffer a{live h b}) : Lemma
  (modifies_1 b h h) =
  lemma_modifies_sub_1 h h b



val remainder_loop:
    rLen:bnlen -> modLen:bnlen{ U32.v modLen = U32.v rLen} ->
    count:U32.t ->  st:rem_state rLen modLen -> Stack unit
    (requires (fun h -> rem_state_st_inv rLen modLen st h))
    (ensures (fun h0 _ h1 -> rem_state_st_inv rLen modLen st h1 /\ 
			   modifies_1 st h0 h1))

#set-options "--z3rlimit 300 --max_fuel 0"
let rec remainder_loop rLen modLen count st =
  if U32.(count >^ 0ul) then begin
    let tmp = get_tmp st in
    let mod_1 = get_mod_1 st in
    let r_i = get_r_i st in
    let mod = get_mod st in
    let h1 = ST.get() in
    let tmp_b = isMore modLen rLen mod r_i in
    let h2 = ST.get() in
    no_upd_lemma_0 h1 h2 st;
    lemma_modifies_0_is_modifies_1 h2 st; (* IDIOTIC LEMMA NEEDED *)
    rshift1 modLen mod mod_1;
    remainder_r_i rLen modLen tmp_b st;
    blit mod_1 0ul mod 0ul modLen;
    remainder_loop rLen modLen U32.(count -^ 1ul) st 
    end 
    


val remainder_:
    rLen:bnlen ->  modLen:bnlen{U32.v modLen = U32.v rLen} ->
    count:U32.t ->  st:rem_state rLen modLen -> Stack unit
    (requires (fun h -> rem_state_st_inv rLen modLen st h))
    (ensures (fun h0 _ h1 -> rem_state_st_inv rLen modLen st h1 /\ 
			   modifies_1 st h0 h1))

let remainder_ rLen modLen count st =
    remainder_loop rLen modLen count st


(*
(* res = a % mod *)
val remainder:
    aBits:U32.t{U32.v aBits > 0} ->
    modBits:U32.t{U32.v modBits > 0 /\ U32.v aBits >= U32.v modBits} ->
    resLen:U32.t{U32.v resLen > 0} ->
    a:bignum{length a = U32.v (bits_to_bn aBits)} ->
    mod:bignum{length mod = U32.v (bits_to_bn modBits) /\ length mod <= length a /\ disjoint a mod} ->
    res:bignum{length res = U32.v resLen /\ length res <= length mod /\ disjoint a res} -> Stack unit
	(requires (fun h -> live h a /\ live h mod /\ live h res))
	(ensures (fun h0 _ h1 -> live h0 a /\ live h0 mod /\  live h0 res /\
        live h1 a /\ live h1 mod /\ live h1 res /\ modifies_1 res h0 h1))

#set-options "--z3rlimit 150"

let remainder aBits modBits resLen a mod res =
    push_frame();
    let aLen = bits_to_bn aBits in
    assert(length a = U32.v (bits_to_bn aBits));
    let modLen = bits_to_bn modBits in
    assert(length mod = U32.v (bits_to_bn modBits));

    let k = U32.(aBits -^ modBits) in
    let modk = U32.(k /^ 64ul) in
    assume(U32.v modLen + U32.v modk + 1 < pow2 32);
    let mod1Len = U32.(modLen +^ modk +^ 1ul) in

    let a1Len = U32.(aLen +^ 1ul) in
    assert(U32.v mod1Len = U32.v a1Len);

    let mod1 = create 0uL mod1Len in
    lshift modLen mod k mod1;

    let r_0 = create 0uL a1Len in
    blit a 0ul r_0 1ul aLen;

    remainder_ a1Len mod1Len r_0 mod1 k;
    blit r_0 0ul res 0ul resLen;
    pop_frame()
    *)
