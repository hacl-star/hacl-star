module Montgomery

open FStar.HyperStack.All
open FStar.Buffer

open Multiplication
open Addition
open Shift
open Comparison
open Convert
open Lib

module U32 = FStar.UInt32
module U64 = FStar.UInt64
open U32

val bn_pow2_mod_n_:
    rLen:bnlen -> a:lbignum rLen ->
    i:U32.t -> p:U32.t ->
    r:lbignum rLen -> Stack unit
	(requires (fun h -> True))
	(ensures (fun h0 _ h1 -> True))

let rec bn_pow2_mod_n_ len a i p r =
    if (i <^ p) then begin
        bn_lshift1 len r r;
        (if not (bn_is_less len r a) then
            bn_sub len r len a r);
        bn_pow2_mod_n_ len a (i +^ 1ul) p r
    end

// res = 2 ^^ p % a
val bn_pow2_mod_n:
    aBits:U32.t ->
    rLen:U32.t -> a:lbignum rLen ->
    p:U32.t{v p > v aBits} ->
    r:lbignum rLen -> Stack unit
	(requires (fun h -> True))
	(ensures (fun h0 _ h1 -> True))

let bn_pow2_mod_n aBits rLen a p r =
    bn_set_bit rLen r aBits;
    bn_sub rLen r rLen a r; // r = r - a
    bn_pow2_mod_n_ rLen a aBits p r


type mont_inverse_state (rLen:bnlen) = lbignum U32.(rLen +^ rLen +^ (rLen +^ rLen) +^ rLen)

let get_ri1 #r (st:mont_inverse_state r) : lbignum r = Buffer.sub st 0ul r
let get_ri  #r (st:mont_inverse_state r) : lbignum r = Buffer.sub st r r
let get_nni #r (st:mont_inverse_state r) : lbignum (r +^ r) = Buffer.sub st (r +^ r) (r +^ r)
let get_nni_mod #r (st:mont_inverse_state r) : lbignum r = Buffer.sub st (r +^ r +^ r +^ r) r
let get_ninv #r (st:mont_inverse_state r) : lbignum r = Buffer.sub st (r +^ r +^ r +^ r +^ r) r

val mont_inverse_:
    rLen:bnlen -> n:lbignum rLen ->
    exp_2:U32.t -> i:U32.t ->
    st:mont_inverse_state rLen -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))

let rec mont_inverse_ rLen n exp_2 i st =
    let pow2_i1 = get_ri1 st in
    let pow2_i = get_ri st in
    let nnInv = get_nni st in
    let nnInv_mod = get_nni_mod st in
    let nInv = get_ninv st in

    bn_lshift1 rLen pow2_i1 pow2_i1;
    bn_lshift1 rLen pow2_i1 pow2_i;

    fill nnInv 0uL (rLen +^ rLen);
    bn_mul rLen n rLen nInv nnInv; // nnInv = n * nInv
    bn_mod_pow2_n (rLen +^ rLen) nnInv i rLen nnInv_mod; // nnInv_mod = nnInv % pow2_i

    if (i <^ exp_2) then begin
        (if (bn_is_less rLen pow2_i1 nnInv_mod) then
            bn_add rLen nInv rLen pow2_i1 nInv);
        mont_inverse_ rLen n exp_2 (i +^ 1ul) st
    end

val mont_inverse:
    rLen:bnlen -> n:lbignum rLen ->
    exp_2:U32.t ->
    nInv:lbignum rLen -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))

let mont_inverse rLen n exp_2 nInv =
    let st:mont_inverse_state rLen = create 0uL (rLen +^ rLen +^ (rLen +^ rLen) +^ rLen +^ rLen) in
    let pow2_i1 = get_ri1 st in
    let nInv_t = get_ninv st in
    pow2_i1.(0ul) <- 1uL;
    nInv_t.(0ul) <- 1uL;
    mont_inverse_ rLen n (exp_2 +^ 1ul) 2ul st;
    blit nInv_t 0ul nInv 0ul rLen

val mont_reduction:
    exp_r:U32.t ->
    rLen:bnlen -> r:lbignum rLen ->
    n:lbignum rLen -> nInv:lbignum rLen ->
    c:lbignum (rLen +^ rLen) ->
    res:lbignum rLen -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))

let mont_reduction exp_r rLen r n nInv c res =
    push_frame();
    let cLen = rLen +^ rLen in
    let crLen = cLen +^ rLen in
    let r2Len = rLen +^ rLen in

    let tmp = create 0uL crLen in
    let tmp1 = create 0uL r2Len in
    let m = create 0uL rLen in

    bn_mul cLen c rLen nInv tmp; // tmp = c * nInv
    bn_mod_pow2_n crLen tmp exp_r rLen m; // m = tmp % r
    bn_sub rLen r rLen m m; // m = r - m
    
    bn_mul rLen m rLen n tmp1; // tmp1 = m * n
    bn_add r2Len tmp1 cLen c tmp1; // tmp1 = c + tmp1
    bn_rshift r2Len tmp1 exp_r tmp1; // tmp1 = tmp1 / r

    blit tmp1 0ul res 0ul rLen;
    pop_frame()

val to_mont:
    exp_r:U32.t ->
    rLen:bnlen -> r:lbignum rLen ->
    n:lbignum rLen -> nInv:lbignum rLen ->
    r2:lbignum rLen -> a:lbignum rLen ->
    aM:lbignum rLen -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))

let to_mont exp_r rLen r n nInv r2 a aM =
    push_frame();
    let c = create 0uL (rLen +^ rLen) in
    bn_mul rLen a rLen r2 c; // c = a * r2
    mont_reduction exp_r rLen r n nInv c aM; //aM = c % n
    pop_frame()

val from_mont:
    exp_r:U32.t ->
    rLen:bnlen -> r:lbignum rLen ->
    n:lbignum rLen -> nInv:lbignum rLen ->
    aM:lbignum rLen -> a:lbignum rLen -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))

let from_mont exp_r rLen r n nInv aM a =
    push_frame();
    let r2Len = rLen +^ rLen in
    
    let tmp = create 0uL r2Len in
    let m = create 0uL rLen in

    bn_mul rLen aM rLen nInv tmp; // tmp = aM * nInv
    bn_mod_pow2_n r2Len tmp exp_r rLen m; // m = tmp % r
    bn_sub rLen r rLen m m; // m = r - m
    fill tmp 0uL r2Len;
    bn_mul rLen m rLen n tmp; //tmp = m * n
    bn_add r2Len tmp rLen aM tmp; //tmp = aM + tmp
    bn_rshift r2Len tmp exp_r tmp; //tmp = tmp / r
    blit tmp 0ul a 0ul rLen;
    pop_frame()