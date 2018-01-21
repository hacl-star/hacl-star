module Hacl.Impl.Multiplication

open FStar.HyperStack.All
open Spec.Lib.IntBuf.Lemmas
open Spec.Lib.IntBuf
open Spec.Lib.IntTypes
open FStar.Mul

open Hacl.Impl.Lib
open Hacl.Impl.Comparison
open Hacl.Impl.Addition

module Buffer = Spec.Lib.IntBuf

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
    bn_mult_ #aLen #bLen aaLen a bbLen b (size 0) (add #SIZE aaLen bbLen) res

val abs:
    #aLen:size_nat ->
    aaLen:size_t{v aaLen == aLen} ->
    a:lbignum aLen -> b:lbignum aLen -> 
    res:lbignum aLen -> Stack unit
    (requires (fun h -> live h a /\ live h b /\ live h res /\ disjoint a b))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))

let abs #aLen aaLen a b res =
    if (bn_is_less aaLen a b) then
       //a < b ==> res = b - a
       bn_sub aaLen b aaLen a res
    else bn_sub aaLen a aaLen b res

type sign =
     | Positive : sign
     | Negative : sign

val add_sign:
    #aLen:size_nat -> #cLen:size_nat -> #resLen:size_nat ->
    aaLen:size_t{v aaLen == aLen} ->
    ccLen:size_t{v ccLen == cLen /\ cLen = aLen + aLen /\ cLen + 1 < max_size_t} ->
    rresLen:size_t{v rresLen == resLen /\ resLen = cLen + 1} ->
    c0:lbignum cLen -> c1:lbignum cLen -> c2:lbignum cLen ->
    a0:lbignum aLen -> a1:lbignum aLen -> a2:lbignum aLen ->
    b0:lbignum aLen -> b1:lbignum aLen -> b2:lbignum aLen ->
    res:lbignum (v rresLen) -> Stack unit
    (requires (fun h -> live h c0 /\ live h c1 /\ live h c2 /\ 
                      live h a0 /\ live h a1 /\ live h a2 /\
                      live h b0 /\ live h b1 /\ live h b2 /\
		      live h res /\ disjoint a0 a1 /\ disjoint b0 b1))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))

let add_sign #aLen #cLen #resLen aaLen ccLen rresLen c0 c1 c2 a0 a1 a2 b0 b1 b2 res =
    let sa2 = if (bn_is_less aaLen a0 a1) then Negative else Positive in
    let sb2 = if (bn_is_less aaLen b0 b1) then Negative else Positive in
    bn_add_carry ccLen c0 ccLen c1 res;
    if ((sa2 = Positive && sb2 = Positive) || (sa2 = Negative && sb2 = Negative))
    then bn_sub rresLen res ccLen c2 res
    else bn_add rresLen res ccLen c2 res
    
// iLen is the upper bound for a and b
// iLen must be a power of 2
val karatsuba_:
    #aLen:size_nat ->
    aaLen:size_t{v aaLen == aLen /\ 4 * aLen < max_size_t} ->
    a:lbignum aLen -> b:lbignum aLen ->
    tmp:lbignum (4 * aLen) ->
    res:lbignum (aLen + aLen) -> Stack unit
    (requires (fun h -> live h a /\ live h b /\ live h res /\ live h tmp /\
		      disjoint res a /\ disjoint res b /\ disjoint res tmp))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1))

let rec karatsuba_ #aLen aaLen a b tmp res =
    let tmpLen = mul #SIZE (size 4) aaLen in
    let resLen = add #SIZE aaLen aaLen in
    let aaLen2 = add #SIZE aaLen aaLen in
    let aaLen0 = aaLen /. (size 2) in
    assume (v aaLen = v aaLen0 + v aaLen0);    
    fill resLen res (u64 0);
    
    if (aaLen <. size 9) then begin
         bn_mul #aLen #aLen aaLen a aaLen b res end
    else begin
         let a0 = Buffer.sub #uint64 #aLen #(v aaLen0) a (size 0) aaLen0 in
         let a1 = Buffer.sub #uint64 #aLen #(v aaLen0) a aaLen0 aaLen0 in
         let b0 = Buffer.sub #uint64 #aLen #(v aaLen0) b (size 0) aaLen0 in
         let b1 = Buffer.sub #uint64 #aLen #(v aaLen0) b aaLen0 aaLen0 in

         let c0 = Buffer.sub #uint64 #(v resLen) #(v aaLen) res (size 0) aaLen in
         let tmp0 = Buffer.sub #uint64 #(v tmpLen) #(v aaLen2) tmp (size 0) aaLen2 in
         karatsuba_ #(v aaLen0) aaLen0 a0 b0 tmp0 c0; // c0 = a0 * b0

         let c1 = Buffer.sub #uint64 #(v resLen) #(v aaLen) res aaLen aaLen in
         let tmp1 = Buffer.sub #uint64 #(v tmpLen) #(v aaLen2) tmp aaLen aaLen2 in
         karatsuba_ #(v aaLen0) aaLen0 a1 b1 tmp1 c1; // c1 = a1 * b1
         
         let a2 = Buffer.sub #uint64 #(v tmpLen) #(v aaLen0) tmp (size 0) aaLen0 in
         let b2 = Buffer.sub #uint64 #(v tmpLen) #(v aaLen0) tmp aaLen0 aaLen0 in
         let c2 = Buffer.sub #uint64 #(v tmpLen) #(v aaLen) tmp aaLen aaLen in
         let tmp0 = Buffer.sub #uint64 #(v tmpLen) #(v aaLen2) tmp aaLen2 aaLen2 in
	 
         abs #(v aaLen0) aaLen0 a0 a1 a2; // a2 = |a0 - a1|
         abs #(v aaLen0) aaLen0 b0 b1 b2; // b2 = |b0 - b1|
         karatsuba_ #(v aaLen0) aaLen0 a2 b2 tmp0 c2; // c2 = a2 * b2

	 let tmp1Len = add #SIZE aaLen (size 1) in
         let tmp1 = Buffer.sub #uint64 #(v tmpLen) #(v tmp1Len) tmp aaLen2 tmp1Len in
         add_sign #(v aaLen0) #(v aaLen) #(v tmp1Len) aaLen0 aaLen tmp1Len c0 c1 c2 a0 a1 a2 b0 b1 b2 tmp1; //tmp1 = (c0 + c1) +/- c2

         //res = [c0; c1]
         //tmp = [a2; b2; c2; tmp1; _]
         let res1Len = add #SIZE aaLen0 aaLen in
         let res1 = Buffer.sub #uint64 #(v resLen) #(v res1Len) res aaLen0 res1Len in
         bn_add res1Len res1 tmp1Len tmp1 res1
     end
      
    
val karatsuba:
    #aLen:size_nat ->
    iLen:size_t{8 * v iLen < max_size_t} ->
    aaLen:size_t{v aaLen == aLen /\ aLen + aLen < max_size_t /\ aLen <= v iLen} ->
    a:lbignum aLen -> b:lbignum aLen ->
    res:lbignum (aLen + aLen) -> Stack unit
    (requires (fun h -> live h a /\ live h b /\ live h res /\ disjoint res a /\ disjoint res b))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
    
let karatsuba #aLen iLen aaLen a b res =
    let tmpLen = mul #SIZE (size 4) iLen in
    let stLen = add #SIZE tmpLen tmpLen in
    let aaLen2 = add #SIZE aaLen aaLen in
    
    alloc #uint64 #unit #(v stLen) stLen (u64 0) [BufItem a; BufItem b] [BufItem res]
    (fun h0 _ h1 -> True)
    (fun st ->
       let tmp = Buffer.sub #uint64 #(v stLen) #(v tmpLen) st (size 0) tmpLen in
       let a_ = Buffer.sub #uint64 #(v stLen) #(v iLen) st tmpLen iLen in
       let b_ = Buffer.sub #uint64 #(v stLen) #(v iLen) st (add #SIZE tmpLen iLen) iLen in
       let res_ = Buffer.sub #uint64 #(v stLen) #(v iLen + v iLen) st (add #SIZE iLen (add #SIZE tmpLen iLen)) (add #SIZE iLen iLen) in
       
       let a_' = Buffer.sub #uint64 #(v iLen) #(aLen) a_ (size 0) aaLen in
       let b_' = Buffer.sub #uint64 #(v iLen) #(aLen) b_ (size 0) aaLen in
       
       copy aaLen a a_';
       copy aaLen b b_';
       
       karatsuba_ #(v iLen) iLen a_ b_ tmp res_;
       
       let res_' = Buffer.sub #uint64 #(v iLen + v iLen) #(aLen + aLen) res_ (size 0) aaLen2 in
       copy aaLen2 res_' res;
       admit()
    )
