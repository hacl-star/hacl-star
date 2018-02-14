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
    let resLen = add #SIZE aaLen bbLen in
    fill resLen res (u64 0);
    bn_mult_ #aLen #bLen aaLen a bbLen b (size 0) resLen res

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

val bn_sqr_sqr:
    #aLen:size_nat ->
    aaLen:size_t{v aaLen == aLen /\ aLen + aLen < max_size_t} -> a:lbignum aLen ->
    i:size_t{v i <= aLen} ->
    res:lbignum (aLen + aLen) -> Stack unit
    (requires (fun h -> live h a /\ live h res /\ disjoint res a))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))

let rec bn_sqr_sqr #aLen aaLen a i res =
    if (i <. aaLen) then begin
       let a_i = a.(i) in
       let a2 = mul_wide a_i a_i in
       let ind = mul #SIZE i (size 2) in
       res.(ind) <- to_u64 #U128 a2;
       res.(size_incr ind) <- to_u64 (shift_right #U128 a2 (u32 64));
       bn_sqr_sqr aaLen a (size_incr i) res
    end

val bn_sqr_:
    #aLen:size_nat ->
    aaLen:size_t{v aaLen == aLen /\ aLen + aLen < max_size_t} -> a:lbignum aLen ->
    i:size_t{v i <= aLen} ->
    resLen:size_t{v resLen == aLen + aLen} -> res:lbignum (aLen + aLen) -> Stack unit
    (requires (fun h -> live h a /\ live h res /\ disjoint res a))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))

let rec bn_sqr_ #aLen aaLen a i resLen res =
    if (i <. size_decr aaLen) then begin
       bn_mult_by_limb_addj aaLen a a.(i) (size_incr i) i resLen (u64 0) res;
       bn_sqr_ aaLen a (size_incr i) resLen res
    end

val bn_sqr:
    #aLen:size_nat ->
    aaLen:size_t{v aaLen == aLen /\ aLen + aLen < max_size_t} -> a:lbignum aLen ->
    tmp:lbignum (aLen + aLen) -> res:lbignum (aLen + aLen) -> Stack unit
    (requires (fun h -> live h a /\ live h res /\ disjoint res a))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))

let bn_sqr #aLen aaLen a tmp res =
    let resLen = add #SIZE aaLen aaLen in
    fill resLen res (u64 0);
    bn_sqr_ aaLen a (size 0) resLen res;
    bn_add resLen res resLen res res;
    bn_sqr_sqr aaLen a (size 0) tmp;
    bn_add resLen res resLen tmp res

val abs:
    #aLen:size_nat -> #bLen:size_nat ->
    aaLen:size_t{v aaLen == aLen} -> a:lbignum aLen ->
    bbLen:size_t{v bbLen == bLen} -> b:lbignum aLen ->
    res:lbignum aLen -> Stack unit
    (requires (fun h -> live h a /\ live h b /\ live h res /\ disjoint a b))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))

let abs #aLen #bLen aaLen a bbLen b res =
    if (bn_is_less_ds aaLen a bbLen b) then
       //a < b ==> res = b - a
       bn_sub bbLen b aaLen a res
    else bn_sub aaLen a bbLen b res

type sign =
     | Positive : sign
     | Negative : sign

val add_sign:
    #a0Len:size_nat -> #a1Len:size_nat -> #resLen:size_nat ->
    aa0Len:size_t{v aa0Len == a0Len} ->
    aa1Len:size_t{v aa1Len == a1Len} ->
    rresLen:size_t{v rresLen == resLen /\ resLen = a0Len + a0Len + 1 /\ resLen < max_size_t} ->
    c0:lbignum (a0Len + a0Len) -> c1:lbignum (a1Len + a1Len) -> c2:lbignum (a0Len + a0Len) ->
    a0:lbignum a0Len -> a1:lbignum a1Len -> a2:lbignum a0Len ->
    b0:lbignum a0Len -> b1:lbignum a1Len -> b2:lbignum a0Len ->
    res:lbignum (v rresLen) -> Stack unit
    (requires (fun h -> live h c0 /\ live h c1 /\ live h c2 /\ 
                      live h a0 /\ live h a1 /\ live h a2 /\
                      live h b0 /\ live h b1 /\ live h b2 /\
		      live h res /\ disjoint a0 a1 /\ disjoint b0 b1))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))

let add_sign #a0Len #a1Len #resLen aa0Len aa1Len rresLen c0 c1 c2 a0 a1 a2 b0 b1 b2 res =
    let c0Len = add #SIZE aa0Len aa0Len in
    let c1Len = add #SIZE aa1Len aa1Len in
    let sa2 = if (bn_is_less_ds aa0Len a0 aa1Len a1) then Negative else Positive in
    let sb2 = if (bn_is_less_ds aa0Len b0 aa1Len b1) then Negative else Positive in
    bn_add_carry c0Len c0 c1Len c1 res;
    if ((sa2 = Positive && sb2 = Positive) || (sa2 = Negative && sb2 = Negative))
    then bn_sub rresLen res c0Len c2 res
    else bn_add rresLen res c0Len c2 res
    
val karatsuba_:
    #aLen:size_nat ->
    pow2_i:size_t -> iLen:size_t ->
    aaLen:size_t{v aaLen == aLen /\ 4 * v pow2_i < max_size_t /\ aLen + aLen < max_size_t} ->
    a:lbignum aLen -> b:lbignum aLen ->
    tmp:lbignum (4 * v pow2_i) ->
    res:lbignum (aLen + aLen) -> Stack unit
    (requires (fun h -> live h a /\ live h b /\ live h tmp /\ live h res))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1))
    
let rec karatsuba_ #aLen pow2_i iLen aaLen a b tmp res =
    assume (v pow2_i = aLen + v iLen);
    let tmpLen = mul #SIZE (size 4) pow2_i in
    let aaLen2 = add #SIZE aaLen aaLen in
    let pow2_i0 = pow2_i /. (size 2) in
    assume (v pow2_i = v pow2_i0 + v pow2_i0);
    let pow2_i1 = sub #SIZE pow2_i0 iLen in
    
    if (aaLen <. size 32) then
       bn_mul #aLen #aLen aaLen a aaLen b res
    else begin
       let a0 = Buffer.sub #uint64 #aLen #(v pow2_i0) a (size 0) pow2_i0 in
       let a1 = Buffer.sub #uint64 #aLen #(v pow2_i1) a pow2_i0 pow2_i1 in
       let b0 = Buffer.sub #uint64 #aLen #(v pow2_i0) b (size 0) pow2_i0 in
       let b1 = Buffer.sub #uint64 #aLen #(v pow2_i1) b pow2_i0 pow2_i1 in

       let tmp0 = Buffer.sub #uint64 #(v tmpLen) #(4 * v pow2_i0) tmp (size 0) (mul #SIZE (size 4) pow2_i0) in
       let c0 = Buffer.sub #uint64 #(v aaLen2) #(2 * v pow2_i0) res (size 0) (mul #SIZE (size 2) pow2_i0) in
       karatsuba_ #(v pow2_i0) pow2_i0 (size 0) pow2_i0 a0 b0 tmp0 c0; // c0 = a0 * b0

       if (pow2_i1 =. size 1) then begin
          let a1_0 = a1.(size 0) in
          let b1_0 = b1.(size 0) in
          let c1 = mul_wide a1_0 b1_0 in
          let c1_0 = to_u64 #U128 c1 in
          let c1_1 = to_u64 #U128 (shift_right #U128 c1 (u32 64)) in
          let c0Len = mul #SIZE (size 2) pow2_i0 in
          res.(c0Len) <- c1_0;
          res.(add #SIZE c0Len (size 1)) <- c1_1;

          let tmp0 = Buffer.sub #uint64 #(v tmpLen) #(v pow2_i0 + 1) tmp (size 0) (add #SIZE pow2_i0 (size 1)) in //tmp0 = a0 * b1_0
          bn_mul_u64 #(v pow2_i0) pow2_i0 a0 b1_0 tmp0;
          let tmp1 = Buffer.sub #uint64 #(v tmpLen) #(v pow2_i0 + 1) tmp (add #SIZE pow2_i0 (size 1)) (add #SIZE pow2_i0 (size 1)) in //tmp1 = b0 * a1_0
          bn_mul_u64 #(v pow2_i0) pow2_i0 b0 a1_0 tmp1;
          let tmp1Len = add #SIZE pow2_i0 (size 1) in
          let tmp1Len2 = add #SIZE tmp1Len tmp1Len in
          let tmp2Len = add #SIZE pow2_i0 (size 2) in
          let tmp2 = Buffer.sub #uint64 #(v tmpLen) #(v tmp2Len) tmp tmp1Len2 tmp2Len in //tmp2 = tmp0 + tmp1 = a0 * b1_0 + b0 * a1_0
          bn_add_carry #(v tmp1Len) #(v tmp1Len) tmp1Len tmp0 tmp1Len tmp1 tmp2;
	  
          let res1Len = add #SIZE pow2_i0 (size 2) in
          let res1 = Buffer.sub #uint64 #(v aaLen2) #(v res1Len) res pow2_i0 res1Len in
          bn_add res1Len res1 tmp2Len tmp2 res1
          end
       else begin
          let ind = if (pow2_i0 /. (size 2) <=. iLen) then sub #SIZE iLen (pow2_i0 /. (size 2)) else iLen in
          let tmp0 = Buffer.sub #uint64 #(v tmpLen) #(4 * v pow2_i1) tmp (size 0) (mul #SIZE (size 4) pow2_i1) in
          let c1 = Buffer.sub #uint64 #(v aaLen2) #(2 * v pow2_i1) res (mul #SIZE (size 2) pow2_i0) (mul #SIZE (size 2) pow2_i1) in
          karatsuba_ #(v pow2_i1) pow2_i0 iLen pow2_i1 a1 b1 tmp0 c1; // c1 = a1 * b1
	    
          let a2 = Buffer.sub #uint64 #(v tmpLen) #(v pow2_i0) tmp (size 0) pow2_i0 in
          let b2 = Buffer.sub #uint64 #(v tmpLen) #(v pow2_i0) tmp pow2_i0 pow2_i0 in
          abs #(v pow2_i0) #(v pow2_i1) pow2_i0 a0 pow2_i1 a1 a2; // a2 = |a0 - a1|
          abs #(v pow2_i0) #(v pow2_i1) pow2_i0 b0 pow2_i1 b1 b2; // b2 = |b0 - b1|

          let c2 = Buffer.sub #uint64 #(v aaLen2) #(2 * v pow2_i0) tmp (mul #SIZE (size 2) pow2_i0) (mul #SIZE (size 2) pow2_i0) in
          let tmp0 = Buffer.sub #uint64 #(v tmpLen) #(4 * v pow2_i0) tmp (mul #SIZE (size 4) pow2_i0) (mul #SIZE (size 4) pow2_i0) in
          karatsuba_ #(v pow2_i0) pow2_i0 (size 0) pow2_i0 a2 b2 tmp0 c2; // c2 = a2 * b2

          let tmp1Len = add #SIZE pow2_i (size 1) in
          let tmp1 = Buffer.sub #uint64 #(v tmpLen) #(v tmp1Len) tmp (mul #SIZE (size 4) pow2_i0) tmp1Len in
          add_sign #(v pow2_i0) #(v pow2_i1) #(v tmp1Len) pow2_i0 pow2_i1 tmp1Len c0 c1 c2 a0 a1 a2 b0 b1 b2 tmp1; //tmp1 = (c0 + c1) +/- c2

          //res = [c0; c1]
          //tmp = [a2; b2; c2; tmp1; _]
          let res1Len = add #SIZE pow2_i0 (add #SIZE pow2_i1 pow2_i1) in
          let res1 = Buffer.sub #uint64 #(v aaLen2) #(v res1Len) res pow2_i0 res1Len in
          bn_add res1Len res1 tmp1Len tmp1 res1 //FIXME!!!
          end
    end

// aLen + iLen == pow2_i
// iLen is the number of leading zeroes
val karatsuba:
    #aLen:size_nat ->
    pow2_i:size_t -> iLen:size_t ->
    aaLen:size_t{v aaLen == aLen /\ 4 * v pow2_i < max_size_t /\ 2 * aLen < max_size_t} ->
    a:lbignum aLen -> b:lbignum aLen ->
    st_mult:lbignum (4 * v pow2_i) ->
    res:lbignum (aLen + aLen) -> Stack unit
    (requires (fun h -> live h a /\ live h b /\ live h st_mult /\ live h res))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1))
    
let karatsuba #aLen pow2_i iLen aaLen a b st_mult res =
    if (aaLen <. size 32)
    then bn_mul #aLen #aLen aaLen a aaLen b res
    else karatsuba_ pow2_i iLen aaLen a b st_mult res
