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
    [@"c_inline"]
let rec bn_mult_by_limb_addj #aLen aaLen a l i j resLen carry res =
    let ij = add #SIZE i j in
    if (i <. aaLen) then begin
        let res_ij = res.(ij) in
        let (carry', res_ij) = bn_mul_by_limb_addj_f a.(i) l carry res_ij in
        res.(ij) <- res_ij;
        bn_mult_by_limb_addj aaLen a l (size_incr i) j resLen carry' res end
    else res.(ij) <- carry

val bn_mult_:
    #aLen:size_nat -> #bLen:size_nat ->
    aaLen:size_t{v aaLen == aLen} -> a:lbignum aLen ->
    bbLen:size_t{v bbLen == bLen} -> b:lbignum bLen ->
    j:size_t{v j <= bLen} ->
    resLen:size_t{v resLen = aLen + bLen} -> res:lbignum (aLen + bLen) -> Stack unit
    (requires (fun h -> live h a /\ live h b /\ live h res /\ disjoint res a /\ disjoint res b))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
    [@"c_inline"]
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
    [@"c_inline"]
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
    [@"c_inline"]
let bn_mul_u64 #aLen aaLen a b res =
    let resLen = add #SIZE aaLen (size 1) in
    fill resLen res (u64 0);
    bn_mult_by_limb_addj #aLen aaLen a b (size 0) (size 0) resLen (u64 0) res

type sign =
     | Positive : sign
     | Negative : sign

val abs:
    #aLen:size_nat -> #bLen:size_nat ->
    aaLen:size_t{v aaLen == aLen} -> a:lbignum aLen ->
    bbLen:size_t{v bbLen == bLen /\ bLen <= aLen} -> b:lbignum bLen ->
    res:lbignum aLen -> Stack sign
    (requires (fun h -> live h a /\ live h b /\ live h res /\ disjoint a b))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
    [@"c_inline"]
let abs #aLen #bLen aaLen a bbLen b res =
    if (bn_is_less aaLen a bbLen b) //a < b
    then begin
      let a' = Buffer.sub #uint64 #aLen #bLen a (size 0) bbLen in
      let res' = Buffer.sub #uint64 #aLen #bLen res (size 0) bbLen in
      bn_sub bbLen b bbLen a' res';
      Negative end
    else begin
      bn_sub aaLen a bbLen b res;
      Positive end

val add_sign:
    #a0Len:size_nat -> #a1Len:size_nat -> #resLen:size_nat ->
    aa0Len:size_t{v aa0Len == a0Len} ->
    aa1Len:size_t{v aa1Len == a1Len /\ a1Len <= a0Len} ->
    rresLen:size_t{v rresLen == resLen /\ resLen = a0Len + a0Len + 1 /\ resLen < max_size_t} ->
    c0:lbignum (a0Len + a0Len) -> c1:lbignum (a1Len + a1Len) -> c2:lbignum (a0Len + a0Len) ->
    a0:lbignum a0Len -> a1:lbignum a1Len -> a2:lbignum a0Len ->
    b0:lbignum a0Len -> b1:lbignum a1Len -> b2:lbignum a0Len ->
    sa2:sign -> sb2:sign ->
    res:lbignum (v rresLen) -> Stack unit
    (requires (fun h -> live h c0 /\ live h c1 /\ live h c2 /\ 
                      live h a0 /\ live h a1 /\ live h a2 /\
                      live h b0 /\ live h b1 /\ live h b2 /\
		      live h res /\ disjoint a0 a1 /\ disjoint b0 b1))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
    [@"c_inline"]
let add_sign #a0Len #a1Len #resLen aa0Len aa1Len rresLen c0 c1 c2 a0 a1 a2 b0 b1 b2 sa2 sb2 res =
    let c0Len = add #SIZE aa0Len aa0Len in
    let c1Len = add #SIZE aa1Len aa1Len in
    bn_add_carry c0Len c0 c1Len c1 res;
    if ((sa2 = Positive && sb2 = Positive) || (sa2 = Negative && sb2 = Negative))
    then bn_sub rresLen res c0Len c2 res
    else bn_add rresLen res c0Len c2 res

val karatsuba_:
    #aLen:size_nat ->
    pow2_i:size_t{4 * v pow2_i < max_size_t} -> iLen:size_t{v iLen < v pow2_i / 2} ->
    aaLen:size_t{v aaLen == aLen /\ aLen + aLen < max_size_t /\ v iLen + aLen = v pow2_i} ->
    a:lbignum aLen -> b:lbignum aLen -> tmp:lbignum (4 * v pow2_i) -> 
    res:lbignum (aLen + aLen) -> Stack unit
    (requires (fun h -> live h a /\ live h b /\ live h tmp /\ live h res /\ disjoint res tmp
                   /\ disjoint tmp a /\ disjoint tmp b /\ disjoint res a /\ disjoint res b))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies2 res tmp h0 h1))
    #reset-options "--z3rlimit 150 --max_fuel 2"
    [@"c_inline"]
let rec karatsuba_ #aLen pow2_i iLen aaLen a b tmp res =
    let tmpLen = mul #SIZE (size 4) pow2_i in
    let resLen = add #SIZE aaLen aaLen in
    let pow2_i0 = pow2_i /. (size 2) in
    assume (v pow2_i = v pow2_i0 + v pow2_i0);
    
    (if (aaLen <. size 32) then
       bn_mul #aLen #aLen aaLen a aaLen b res
    else begin
       let a0 = Buffer.sub #uint64 #aLen #(v pow2_i0) a (size 0) pow2_i0 in
       let b0 = Buffer.sub #uint64 #aLen #(v pow2_i0) b (size 0) pow2_i0 in

       let tmp0 = Buffer.sub #uint64 #(v tmpLen) #(4 * v pow2_i0) tmp (size 0) (mul #SIZE (size 4) pow2_i0) in
       let c0 = Buffer.sub #uint64 #(v resLen) #(v pow2_i) res (size 0) pow2_i in
       karatsuba_ #(v pow2_i0) pow2_i0 (size 0) pow2_i0 a0 b0 tmp0 c0; // c0 = a0 * b0

       let pow2_i1 = sub #SIZE pow2_i0 iLen in
       if (pow2_i1 =. size 1) then begin
          let a1 = Buffer.sub #uint64 #aLen #1 a pow2_i0 (size 1) in
          let b1 = Buffer.sub #uint64 #aLen #1 b pow2_i0 (size 1) in
          let a1_0 = a1.(size 0) in
          let b1_0 = b1.(size 0) in
	  
          let c1 = mul_wide a1_0 b1_0 in
          res.(pow2_i) <- to_u64 #U128 c1;
          res.(size_incr pow2_i) <- to_u64 #U128 (shift_right #U128 c1 (u32 64));

          let tmp1Len = size_incr pow2_i0 in
          let tmp1Len2 = add #SIZE tmp1Len tmp1Len in
          let tmp2Len = add #SIZE pow2_i0 (size 2) in
	  
          let tmp0 = Buffer.sub #uint64 #(v tmpLen) #(v tmp1Len) tmp (size 0) tmp1Len in
          let tmp1 = Buffer.sub #uint64 #(v tmpLen) #(v tmp1Len) tmp tmp1Len tmp1Len in
          let tmp2 = Buffer.sub #uint64 #(v tmpLen) #(v tmp2Len) tmp tmp1Len2 tmp2Len in
          let res1 = Buffer.sub #uint64 #(v resLen) #(v tmp2Len) res pow2_i0 tmp2Len in
	  
          bn_mul_u64 #(v pow2_i0) pow2_i0 a0 b1_0 tmp0; // tmp0 = a0 * b1_0
          bn_mul_u64 #(v pow2_i0) pow2_i0 b0 a1_0 tmp1; // tmp1 = b0 * a1_0
          bn_add_carry #(v tmp1Len) #(v tmp1Len) tmp1Len tmp0 tmp1Len tmp1 tmp2; // tmp2 = tmp0 + tmp1 = a0 * b1_0 + b0 * a1_0
          bn_add tmp2Len res1 tmp2Len tmp2 res1
          end
       else begin
	  let a1 = Buffer.sub #uint64 #aLen #(v pow2_i1) a pow2_i0 pow2_i1 in
	  let b1 = Buffer.sub #uint64 #aLen #(v pow2_i1) b pow2_i0 pow2_i1 in
          let pow2_i02 = pow2_i0 /. size 2 in
          assume (v pow2_i0 + v pow2_i0 = v pow2_i02);
          let ind = if (pow2_i02 <. iLen) then sub #SIZE iLen pow2_i02 else iLen in
          let tmp0 = Buffer.sub #uint64 #(v tmpLen) #(4 * v pow2_i0) tmp (size 0) (mul #SIZE (size 4) pow2_i0) in
          let c1 = Buffer.sub #uint64 #(v resLen) #(2 * v pow2_i1) res pow2_i (mul #SIZE (size 2) pow2_i1) in
          karatsuba_ #(v pow2_i1) pow2_i0 ind pow2_i1 a1 b1 tmp0 c1; // c1 = a1 * b1

          let a2 = Buffer.sub #uint64 #(v tmpLen) #(v pow2_i0) tmp (size 0) pow2_i0 in
          let b2 = Buffer.sub #uint64 #(v tmpLen) #(v pow2_i0) tmp pow2_i0 pow2_i0 in
          let sa2 =  abs #(v pow2_i0) #(v pow2_i1) pow2_i0 a0 pow2_i1 a1 a2 in // a2 = |a0 - a1|
          let sb2 = abs #(v pow2_i0) #(v pow2_i1) pow2_i0 b0 pow2_i1 b1 b2 in // b2 = |b0 - b1|

          let c2 = Buffer.sub #uint64 #(v tmpLen) #(v pow2_i) tmp pow2_i pow2_i in
          let tmp0 = Buffer.sub #uint64 #(v tmpLen) #(4 * v pow2_i0) tmp (mul #SIZE (size 4) pow2_i0) (mul #SIZE (size 4) pow2_i0) in
          karatsuba_ #(v pow2_i0) pow2_i0 (size 0) pow2_i0 a2 b2 tmp0 c2; // c2 = a2 * b2

          let tmp1Len = size_incr pow2_i in
          let tmp1 = Buffer.sub #uint64 #(v tmpLen) #(v tmp1Len) tmp (mul #SIZE (size 4) pow2_i0) tmp1Len in
          add_sign #(v pow2_i0) #(v pow2_i1) #(v tmp1Len) pow2_i0 pow2_i1 tmp1Len c0 c1 c2 a0 a1 a2 b0 b1 b2 sa2 sb2 tmp1; //tmp1 = (c0 + c1) +/- c2

          //res = [c0; c1]
          //tmp = [a2; b2; c2; tmp1; _]
          let res1Len = add #SIZE pow2_i0 (add #SIZE pow2_i1 pow2_i1) in
          let res1 = Buffer.sub #uint64 #(v resLen) #(v res1Len) res pow2_i0 res1Len in
          bn_add res1Len res1 tmp1Len tmp1 res1
         end
    end); admit()

// aLen + iLen == pow2_i
// iLen is the number of leading zeroes
val karatsuba:
    #aLen:size_nat ->
    pow2_i:size_t{2 * aLen + 4 * v pow2_i < max_size_t} -> iLen:size_t{v iLen < v pow2_i / 2} ->
    aaLen:size_t{v aaLen == aLen /\ aLen + aLen < max_size_t /\ v iLen + aLen = v pow2_i} ->
    a:lbignum aLen -> b:lbignum aLen ->
    st_kara:lbignum (aLen + aLen + 4 * v pow2_i) ->
    Stack unit
    (requires (fun h -> live h a /\ live h b /\ live h st_kara /\
                      disjoint st_kara a /\ disjoint st_kara b))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 st_kara h0 h1))
    [@"c_inline"]
let karatsuba #aLen pow2_i iLen aaLen a b st_kara =
    let stLen = add #SIZE (add #SIZE aaLen aaLen) (mul (size 4) pow2_i) in
    let res = Buffer.sub #uint64 #(v stLen) #(aLen + aLen) st_kara (size 0) (add #SIZE aaLen aaLen) in
    let st_mult = Buffer.sub #uint64 #(v stLen) #(4 * v pow2_i) st_kara (add #SIZE aaLen aaLen) (mul #SIZE (size 4) pow2_i) in
    disjoint_sub_lemma1 st_kara a (size 0) (add #SIZE aaLen aaLen); // disjoint res a
    disjoint_sub_lemma1 st_kara a (add #SIZE aaLen aaLen) (mul #SIZE (size 4) pow2_i); // disjoint st_mult a
    disjoint_sub_lemma1 st_kara b (size 0) (add #SIZE aaLen aaLen); // disjoint res b
    disjoint_sub_lemma1 st_kara b (add #SIZE aaLen aaLen) (mul #SIZE (size 4) pow2_i); // disjoint st_mult b
    let h0 = FStar.HyperStack.ST.get() in
    karatsuba_ pow2_i iLen aaLen a b st_mult res;
    let h1 = FStar.HyperStack.ST.get() in
    assume (modifies1 st_kara h0 h1)

    (*if (aaLen <. size 32)
    then bn_mul #aLen #aLen aaLen a aaLen b res
    else karatsuba_ pow2_i iLen aaLen a b st_mult res*)
