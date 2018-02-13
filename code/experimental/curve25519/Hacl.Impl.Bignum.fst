module Hacl.Impl.Bignum

open FStar.HyperStack.All
open Spec.Lib.IntBuf.Lemmas
open Spec.Lib.IntBuf
open Spec.Lib.IntTypes
open Spec.Lib.RawIntTypes
open Spec.Lib.Endian
open FStar.Mul

module Buffer = Spec.Lib.IntBuf

inline_for_extraction
let v = size_v

type lbytes (len:size_nat) = lbuffer uint8 len
type lbignum (len:size_nat) = lbuffer uint64 len

val lt_u64: a:uint64 -> b:uint64 -> Tot bool
[@ "substitute"]
let lt_u64 a b = FStar.UInt64.(u64_to_UInt64 a <^ u64_to_UInt64 b)

val mul_wide: a:uint64 -> b:uint64 -> Tot uint128
[@ "substitute"]
let mul_wide a b = u128_from_UInt128 (FStar.UInt128.mul_wide (u64_to_UInt64 a) (u64_to_UInt64 b))

val fill:
    #len:size_nat -> clen:size_t{v clen == len} ->
    b:lbignum len -> z:uint64 -> Stack unit
    (requires (fun h -> live h b))
    (ensures (fun h0 r h1 -> preserves_live h0 h1 /\ modifies1 b h0 h1))
  
let fill #len clen b z =
    alloc #uint64 #unit #len clen z [] [BufItem b]
    (fun h0 _ h1 -> True)
    (fun tmp ->
       copy clen tmp b
    )

(* ADDITION *)
val bn_add_:
    #aLen:size_nat -> #bLen:size_nat ->
    caLen:size_t{v caLen == aLen} -> a:lbignum aLen ->
    cbLen:size_t{v cbLen == bLen} -> b:lbignum bLen ->
    i:size_t{v i <= aLen} -> carry:uint64 ->
    res:lbignum aLen -> Stack uint64
    (requires (fun h -> live h a /\ live h b /\ live h res))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
    
let rec bn_add_ #aLen #bLen caLen a cbLen b i carry res =
    if (i <. caLen) then begin
       let t1 = a.(i) in
       let t2 = if (i <. cbLen) then b.(i) else u64 0 in
       let t1 = add_mod #U64 t1 carry in
       let carry = if (lt_u64 t1 carry) then u64 1 else u64 0 in
       let res_i = add_mod #U64 t1 t2 in
       res.(i) <- res_i;
       let carry = if (lt_u64 res_i t1) then add #U64 carry (u64 1) else carry in
       bn_add_ #aLen #bLen caLen a cbLen b (size_incr i) carry res end
    else carry

val bn_add:
    #aLen:size_nat -> #bLen:size_nat ->
    caLen:size_t{v caLen == aLen} -> a:lbignum aLen ->
    cbLen:size_t{v cbLen == bLen /\ bLen <= aLen} -> b:lbignum bLen ->
    res:lbignum aLen -> Stack unit
    (requires (fun h -> live h a /\ live h b /\ live h res))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))

let bn_add #aLen #bLen caLen a cbLen b res =
    let _ = bn_add_ #aLen #bLen caLen a cbLen b (size 0) (u64 0) res in ()

val bn_add_carry:
    #aLen:size_nat -> #bLen:size_nat ->
    caLen:size_t{v caLen == aLen /\ aLen + 1 < max_size_t} -> a:lbignum aLen ->
    cbLen:size_t{v cbLen == bLen /\ bLen <= aLen} -> b:lbignum bLen ->
    res:lbignum (aLen + 1) -> Stack unit
    (requires (fun h -> live h a /\ live h b /\ live h res))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
    
let bn_add_carry #aLen #bLen caLen a cbLen b res =
    let res' = Buffer.sub #uint64 #(aLen + 1) #aLen res (size 0) caLen in
    let carry = bn_add_ #aLen #bLen caLen a cbLen b (size 0) (u64 0) res' in
    res.(caLen) <- carry

(* MULTIPLICATION *)
val bn_mul_by_limb_addj_f:
    a_i:uint64 -> l:uint64 -> c:uint64 -> r_ij:uint64 -> Tot (tuple2 uint64 uint64)
[@ "substitute"]
let bn_mul_by_limb_addj_f a_i l c r_ij =
    assume (uint_v #U64 a_i * uint_v #U64 l + uint_v #U64 c + uint_v #U64 r_ij < pow2 128);
    let res = add #U128 (add #U128 (mul_wide a_i l) (to_u128 #U64 c)) (to_u128 #U64 r_ij) in
    let r = to_u64 res in
    let c' = to_u64 (res >>. u32 64) in
    (c', r)

val bn_mult_by_limb_addj:
    #aLen:size_nat ->
    aaLen:size_t{v aaLen == aLen} -> a:lbignum aLen ->
    l:uint64 -> i:size_t{v i <= aLen} -> j:size_t ->
    resLen:size_t{aLen + v j < v resLen} ->
    carry:uint64 -> res:lbignum (v resLen) -> Stack unit
    (requires (fun h -> live h a /\ live h res /\ disjoint res a))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))

let rec bn_mult_by_limb_addj #aLen aaLen a l i j resLen carry res =
    let ij = add #SIZE i j in
    if (i <. aaLen) then begin
        let res_ij = res.(ij) in
	let (carry', res_ij) = bn_mul_by_limb_addj_f a.(i) l carry res_ij in
        res.(ij) <- res_ij;
        bn_mult_by_limb_addj aaLen a l (size_incr i) j resLen carry' res end
    else
        res.(ij) <- carry

val bn_mult_:
    #aLen:size_nat -> #bLen:size_nat ->
    aaLen:size_t{v aaLen == aLen} -> a:lbignum aLen ->
    bbLen:size_t{v bbLen == bLen /\ aLen + bLen < max_size_t} -> b:lbignum bLen ->
    j:size_t{v j <= bLen} ->
    resLen:size_t{v resLen = aLen + bLen} -> res:lbignum (aLen + bLen) -> Stack unit
    (requires (fun h -> live h a /\ live h b /\ live h res /\ disjoint res a /\ disjoint res b))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))

let rec bn_mult_ #aLen #bLen aaLen a bbLen b j resLen res =
    if (j <. bbLen) then begin
        bn_mult_by_limb_addj aaLen a b.(j) (size 0) j resLen (u64 0) res;
        bn_mult_ aaLen a bbLen b (size_incr j) resLen res
    end

// res = a * b
val bn_mul:
    #aLen:size_nat -> #bLen:size_nat ->
    aaLen:size_t{v aaLen == aLen} -> a:lbignum aLen ->
    bbLen:size_t{v bbLen == bLen /\ aLen + bLen < max_size_t} -> b:lbignum bLen ->
    res:lbignum (aLen + bLen) -> Stack unit
    (requires (fun h -> live h a /\ live h b /\ live h res /\ disjoint res a /\ disjoint res b))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))    
  
let bn_mul #aLen #bLen aaLen a bbLen b res =
    let resLen = add #SIZE aaLen bbLen in
    fill resLen res (u64 0);
    bn_mult_ #aLen #bLen aaLen a bbLen b (size 0) resLen res

// res = a * a
val bn_sqr:
    #aLen:size_nat ->
    aaLen:size_t{v aaLen == aLen /\ aLen + aLen < max_size_t} -> a:lbignum aLen ->
    res:lbignum (aLen + aLen) -> Stack unit
    (requires (fun h -> live h a /\ live h res /\ disjoint res a))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
  
let bn_sqr #aLen aaLen a res =
    let resLen = add #SIZE aaLen aaLen in
    fill resLen res (u64 0);
    bn_mult_ #aLen #aLen aaLen a aaLen a (size 0) resLen res

val bn_mul_u64:
    #aLen:size_nat ->
    aaLen:size_t{v aaLen == aLen /\ aLen + 1 < max_size_t} ->
    a:lbignum aLen -> b:uint64 -> res:lbignum (aLen + 1) -> Stack unit
    (requires (fun h -> live h a /\ live h res /\ disjoint res a))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
let bn_mul_u64 #aLen aaLen a b res = 
    let resLen = add #SIZE aaLen (size 1) in
    fill resLen res (u64 0);
    bn_mult_by_limb_addj #aLen aaLen a b (size 0) (size 0) resLen (u64 0) res

(* MODULAR REDUCTION *)
val bn_reduce:
    a:lbignum 8 -> res:lbignum 4 -> Stack unit
    (requires (fun h -> live h a /\ live h res /\ disjoint res a))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
  
let bn_reduce a res =
    // a = [a0; a1] = [4; 4]
    // c1 = a1 * 38 + a0; |c1| = 5
    // c1 = [c0; c1] = [4; 1] and c1 has at most 6 bits
    // c2 = c1 * 38 + c0; |c2| = 5
    // c2 = [c0'; c1'] and c1' is either 0 or 1
    // c3 = c1' * 38 + c0'; |c3| = 4
    // return c3
    let a0 = Buffer.sub #uint64 #8 #4 a (size 0) (size 4) in
    let a1 = Buffer.sub #uint64 #8 #4 a (size 4) (size 4) in

    alloc #uint64 #unit #5 (size 5) (u64 0) [BufItem a] [BufItem res]
    (fun h0 _ h1 -> True)
    (fun tmp ->
       assume (disjoint tmp a1);
       bn_mul_u64 #4 (size 4) a1 (u64 38) tmp; // tmp = 38 * a1
       bn_add (size 5) tmp (size 4) a0 tmp; // tmp = tmp + a0

       let c0 = Buffer.sub #uint64 #5 #4 tmp (size 0) (size 4) in
       let c1 = tmp.(size 4) in
       (* res.(size 0) <- mul_mod #U64 (u64 38) c1;
       bn_add_carry (size 4) res (size 4) c0 tmp; *)

       res.(size 0) <- mul_mod #U64 (u64 38) c1;
       bn_add (size 4) res (size 4) c0 res
    )

val bn_mul_mod:
    a:lbignum 4 -> b:lbignum 4 -> res:lbignum 4 -> Stack unit
    (requires (fun h -> live h a /\ live h b /\ live h res /\ disjoint res a /\ disjoint res b))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))    

let bn_mul_mod a b res =
    fill (size 4) res (u64 0);
    alloc #uint64 #unit #8 (size 8) (u64 0) [BufItem a; BufItem b] [BufItem res]
    (fun h0 _ h1 -> True)
    (fun tmp ->
       bn_mul (size 4) a (size 4) b tmp;
       bn_reduce tmp res
    )
    
(* CONVERT FUNCTIONS *)
val text_to_nat:
    input:lbytes 32 -> res:lbignum 4 -> Stack unit
    (requires (fun h -> live h input /\ live h res /\ disjoint res input))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))

let text_to_nat input res =
    res.(size 0) <- uint64_from_bytes_be (Buffer.sub input (size 24) (size 8));
    res.(size 1) <- uint64_from_bytes_be (Buffer.sub input (size 16) (size 8));
    res.(size 2) <- uint64_from_bytes_be (Buffer.sub input (size 8) (size 8));
    res.(size 3) <- uint64_from_bytes_be (Buffer.sub input (size 0) (size 8))
  

val nat_to_text:
    input:lbignum 4 -> res:lbytes 32 -> Stack unit
    (requires (fun h -> live h input /\ live h res /\ disjoint res input))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
    
let nat_to_text input res =
    uint64_to_bytes_be (Buffer.sub res (size 0) (size 8)) input.(size 3);
    uint64_to_bytes_be (Buffer.sub res (size 8) (size 8)) input.(size 2);
    uint64_to_bytes_be (Buffer.sub res (size 16) (size 8)) input.(size 1);
    uint64_to_bytes_be (Buffer.sub res (size 24) (size 8)) input.(size 0)
