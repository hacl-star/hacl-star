module Division

open FStar.HyperStack.All
open FStar.Buffer
open FStar.Int.Cast
open Convert

open Shift
open Comparison
open Addition

module U32 = FStar.UInt32
module U64 = FStar.UInt64

type bignum = buffer FStar.UInt64.t

let bn_bits2 = 64ul

val remainder_loop:
    rLen:U32.t -> modLen:U32.t -> resLen:U32.t ->
    r_i:bignum{length r_i = U32.v rLen} -> mod:bignum{length mod = U32.v modLen} ->
    count:U32.t -> res:bignum{length res = U32.v resLen} -> Stack unit
    (requires (fun h -> live h r_i /\ live h mod /\ live h res))
	(ensures (fun h0 _ h1 -> live h0 r_i /\ live h0 mod /\  live h0 res /\ live h1 res /\ modifies_1 res h0 h1))
let rec remainder_loop rLen modLen resLen r_i mod count res =
    push_frame();
    let isSet = if U64.(mod.(U32.(modLen -^ 1ul)) =^ 1uL) then 1ul else 0ul in
    let mod1Len = U32.(modLen -^ isSet) in
    let mod1 = create 0uL mod1Len in
    let tmp = create 0uL rLen in
    (if U32.(count >^ 0ul) then
    (rshift1 modLen mod mod1;
    if not (isMore modLen rLen mod r_i) then
		(sub rLen modLen r_i mod tmp; blit tmp 0ul r_i 0ul rLen;
		remainder_loop rLen mod1Len resLen r_i mod1 U32.(count -^ 1ul) res)
	else
		remainder_loop rLen mod1Len resLen r_i mod1 U32.(count -^ 1ul) res)
    else
        let len = if U32.(resLen >^ rLen) then rLen else resLen in
        blit r_i 0ul res 0ul len);
    pop_frame()

(* res = a % mod *)
val remainder:
    aBits:U32.t -> modBits:U32.t{U32.(modBits <^ aBits)} -> resLen:U32.t ->
    a:bignum{length a = U32.v (bits_to_bn aBits)} ->
    mod:bignum{length mod = U32.v (bits_to_bn modBits)} ->
    res:bignum{length res = U32.v resLen} -> Stack unit
	(requires (fun h -> live h a /\ live h mod /\ live h res))
	(ensures (fun h0 _ h1 -> live h0 a /\ live h0 mod /\  live h0 res /\ live h1 res /\ modifies_1 res h0 h1))
let remainder aBits modBits resLen a mod res =
    push_frame();
    let aLen = bits_to_bn aBits in
    let modLen = bits_to_bn modBits in
    let k = U32.(aBits -^ modBits) in
    let modk = U32.(k /^ bn_bits2) in
    let mod1Len = U32.(modLen +^ modk) in
    let mod1 = create 0uL mod1Len in
    lshift modLen mod k mod1;
    remainder_loop aLen mod1Len resLen a mod1 k res;
    pop_frame()
