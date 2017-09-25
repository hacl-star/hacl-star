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

[@ "substitute"]
val remainder_r_i:
    rLen:U32.t{U32.v rLen > 0} ->
    modLen:U32.t{U32.v modLen > 0 /\ U32.v modLen = U32.v rLen} ->
    r_i:bignum{length r_i = U32.v rLen} ->
    mod:bignum{length mod = U32.v modLen /\ disjoint r_i mod} ->
    tmp_b:bool -> Stack unit
    (requires (fun h -> live h r_i /\ live h mod))
	(ensures (fun h0 _ h1 -> live h0 r_i /\ live h0 mod /\ 
        live h1 r_i /\ live h1 mod /\ modifies_1 r_i h0 h1))

let remainder_r_i rLen modLen r_i mod tmp_b =
    push_frame();
    let tmp = create 0uL rLen in
    let h0 = ST.get () in
    (if not tmp_b then
        (sub rLen modLen r_i mod tmp;
        blit tmp 0ul r_i 0ul rLen));
    lemma_modifies_sub_1 h0 h0 r_i;
    pop_frame()
  
val remainder_loop:
    rLen:U32.t{U32.v rLen > 0} ->
    modLen:U32.t{U32.v modLen > 0 /\ U32.v modLen = U32.v rLen} ->
    r_i:bignum{length r_i = U32.v rLen} ->
    mod:bignum{length mod = U32.v modLen /\ disjoint r_i mod} ->
    mod1:bignum{length mod1 = U32.v modLen /\ disjoint mod mod1} ->
    count:U32.t -> Stack unit
    (requires (fun h -> live h r_i /\ live h mod /\ live h mod1))
	(ensures (fun h0 _ h1 -> live h0 r_i /\ live h0 mod /\ live h0 mod1 /\
        live h1 r_i /\ live h1 mod /\ live h1 mod1 /\ modifies_3 r_i mod mod1 h0 h1))

#set-options "--z3rlimit 50 --max_fuel 2"

let rec remainder_loop rLen modLen r_i mod mod1 count =
    rshift1 modLen mod mod1;
    if U32.(count >^ 0ul) then
        begin
        let tmp_b = isMore modLen rLen mod r_i in
        remainder_r_i rLen modLen r_i mod tmp_b;
        blit mod1 0ul mod 0ul modLen;
        remainder_loop rLen modLen r_i mod mod1 U32.(count -^ 1ul)
        end

val remainder_:
    rLen:U32.t{U32.v rLen > 0} ->
    modLen:U32.t{U32.v modLen > 0 /\ U32.v modLen = U32.v rLen} ->
    r_i:bignum{length r_i = U32.v rLen} ->
    mod:bignum{length mod = U32.v modLen /\ disjoint r_i mod} ->
    count:U32.t -> Stack unit
    (requires (fun h -> live h r_i /\ live h mod))
	(ensures (fun h0 _ h1 -> live h0 r_i /\ live h0 mod /\ 
        live h1 r_i /\ live h1 mod /\ modifies_2 r_i mod h0 h1))

let remainder_ rLen modLen r_i mod count =
    push_frame();
    let mod1 = create 0uL modLen in
    remainder_loop rLen modLen r_i mod mod1 count;
    pop_frame()

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