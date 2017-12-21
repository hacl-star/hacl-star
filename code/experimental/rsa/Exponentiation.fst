module Exponentiation

open FStar.HyperStack.All
open FStar.Buffer

open Montgomery
open Multiplication
open Convert
open Lib

module U32 = FStar.UInt32
module U64 = FStar.UInt64
open U32

val karatsuba_mont_mod:
    exp_r:U32.t ->
    rLen:bnlen -> r:lbignum rLen ->
    n:lbignum rLen -> nInv:lbignum rLen ->
    aM:lbignum rLen -> bM:lbignum rLen ->
    resM:lbignum rLen -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))

let karatsuba_mont_mod exp_r rLen r n nInv aM bM resM =
    push_frame();
    let c = create 0uL (rLen +^ rLen) in
    bn_mul rLen aM rLen bM c; // c = a * b
    mont_reduction exp_r rLen r n nInv c resM; // resM = c % n
    pop_frame()

val mod_exp_:
    exp_r:U32.t ->
    rLen:bnlen -> r:lbignum rLen ->
    n:lbignum rLen -> nInv:lbignum rLen -> aM:lbignum rLen ->
    bBits:U32.t{U32.v bBits > 0} -> b:lbignum (bits_to_bn bBits) ->
    accM:lbignum rLen -> count:U32.t{U32.v count <= U32.v bBits} -> Stack unit
    (requires (fun h -> True))
    (ensures  (fun h0 _ h1 -> True))

let rec mod_exp_ exp_r rLen r n nInv aM bBits b accM count =
    if U32.(count <^ bBits) then begin
        (if (bn_is_bit_set b count) then
            karatsuba_mont_mod exp_r rLen r n nInv aM accM accM); //acc = (acc * a) % n
        karatsuba_mont_mod exp_r rLen r n nInv aM aM aM; //a = (a * a) % n
        mod_exp_ exp_r rLen r n nInv aM bBits b accM U32.(count +^ 1ul)
    end

// res = a ^^ b mod n
val mod_exp:
    modBits:U32.t{U32.v modBits > 0} ->
    nLen:U32.t -> n:lbignum nLen -> a:lbignum nLen ->
    bBits:U32.t{U32.v bBits > 0} -> b:lbignum (bits_to_bn bBits) ->
    res:lbignum nLen -> Stack unit
    (requires (fun h -> True))
    (ensures  (fun h0 _ h1 -> True))

let mod_exp modBits nLen n a bBits b res =
    push_frame();
    let rLen = bits_to_bn (3ul +^ modBits) in
    let exp_r = modBits +^ 2ul in

    let n1 = create 0uL rLen in
    let a1 = create 0uL rLen in
    let acc = create 0uL rLen in
    let r = create 0uL rLen in
    let r2 = create 0uL rLen in
    let nInv = create 0uL rLen in
    let aM = create 0uL rLen in
    let accM = create 0uL rLen in
    let res1 = create 0uL rLen in

    blit n 0ul n1 0ul nLen;
    blit a 0ul a1 0ul nLen;
    acc.(0ul) <- 1uL;
    bn_set_bit rLen r exp_r; // r = pow2 (2 + modBits)
    bn_pow2_mod_n modBits rLen n1 (exp_r +^ exp_r) r2; // r2 = r * r % n
    mont_inverse rLen n1 exp_r nInv; // n * nInv = 1 (mod r)
    to_mont exp_r rLen r n1 nInv r2 a1 aM;
    to_mont exp_r rLen r n1 nInv r2 acc accM;

    mod_exp_ exp_r rLen r n1 nInv aM bBits b accM 0ul;

    from_mont exp_r rLen r n1 nInv accM res1;
    blit res1 0ul res 0ul nLen;
    pop_frame()