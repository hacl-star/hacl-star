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
  [@"c_inline"]
let bn_mul_by_limb_addj_f a_i l c r_ij =
  assume (uint_v #U64 a_i * uint_v #U64 l + uint_v #U64 c + uint_v #U64 r_ij < pow2 128);
  let res = add #U128 (add #U128 (mul_wide a_i l) (to_u128 #U64 c)) (to_u128 #U64 r_ij) in
  let r = to_u64 res in
  let c' = to_u64 (res >>. u32 64) in
  (c', r)

val bn_mult_by_limb_addj:
  #aLen:size_nat ->
  aaLen:size_t{v aaLen == aLen} -> a:lbignum aLen ->
  l:uint64 -> j:size_t ->
  resLen:size_t{aLen + v j < v resLen} -> res:lbignum (v resLen) ->
  carry:lbignum 1 -> Stack unit
  (requires (fun h -> live h a /\ live h res /\ live h carry /\ disjoint res a))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies2 carry res h0 h1))
  [@ "substitute"]
let bn_mult_by_limb_addj #aLen aaLen a l j resLen res carry =
  let h0 = FStar.HyperStack.ST.get() in
  loop2_simple #h0 #uint64 #uint64 #1 #(v resLen) aaLen carry res
  (fun i ->
    let ij = add #SIZE i j in
    let res_ij = res.(ij) in
    let (c, res_ij) = bn_mul_by_limb_addj_f a.(i) l carry.(size 0) res_ij in
    carry.(size 0) <- c;
    res.(ij) <- res_ij
  );
  res.(add #SIZE aaLen j) <- carry.(size 0)

val bn_mult_:
  #aLen:size_nat -> #bLen:size_nat ->
  aaLen:size_t{v aaLen == aLen} -> a:lbignum aLen ->
  bbLen:size_t{v bbLen == bLen} -> b:lbignum bLen ->
  resLen:size_t{v resLen = aLen + bLen} -> res:lbignum (aLen + bLen) ->
  carry:lbignum 1 -> Stack unit
  (requires (fun h -> live h a /\ live h b /\ live h res /\ live h carry /\ disjoint res a /\ disjoint res b))
  (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies2 carry res h0 h1))
  [@ "substitute"]
let bn_mult_ #aLen #bLen aaLen a bbLen b resLen res carry =
  let h0 = FStar.HyperStack.ST.get() in
  loop2_simple #h0 #uint64 #uint64 #1 #(v resLen) bbLen carry res
  (fun j ->
    carry.(size 0) <- u64 0;
    bn_mult_by_limb_addj aaLen a b.(j) j resLen res carry
  )

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
  alloc #uint64 #unit #1 (size 1) (u64 0) [BufItem a; BufItem b] [BufItem res]
  (fun h0 _ h1 -> True)
  (fun carry ->
    bn_mult_ #aLen #bLen aaLen a bbLen b resLen res carry
  )

type sign =
  | Positive : sign
  | Negative : sign

val abs:
  #aLen:size_nat -> aaLen:size_t{v aaLen == aLen} ->
  a:lbignum aLen -> b:lbignum aLen ->
  res:lbignum aLen -> Stack sign
  (requires (fun h -> live h a /\ live h b /\ live h res /\ disjoint a b))
  (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
  [@"c_inline"]
let abs #aLen aaLen a b res =
  if (bn_is_less aaLen a aaLen b) //a < b
  then begin
    let _ = bn_sub aaLen b aaLen a res in
    Negative end
  else begin
    let _ = bn_sub aaLen a aaLen b res in
    Positive end

val add_sign:
  #a0Len:size_nat -> aa0Len:size_t{v aa0Len == a0Len /\ a0Len + a0Len + 1 < max_size_t} ->
  c0:lbignum (a0Len + a0Len) -> c1:lbignum (a0Len + a0Len) -> c2:lbignum (a0Len + a0Len) ->
  a0:lbignum a0Len -> a1:lbignum a0Len -> a2:lbignum a0Len ->
  b0:lbignum a0Len -> b1:lbignum a0Len -> b2:lbignum a0Len ->
  sa2:sign -> sb2:sign ->
  rresLen:size_t{v rresLen = a0Len + a0Len + 1} -> res:lbignum (v rresLen) -> Stack unit
  (requires (fun h -> live h c0 /\ live h c1 /\ live h c2 /\
                    live h a0 /\ live h a1 /\ live h a2 /\
                    live h b0 /\ live h b1 /\ live h b2 /\
		    live h res /\ disjoint a0 a1 /\ disjoint b0 b1))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
  [@"c_inline"]
let add_sign #a0Len aa0Len c0 c1 c2 a0 a1 a2 b0 b1 b2 sa2 sb2 rresLen res =
  let c0Len = add #SIZE aa0Len aa0Len in
  let res1 = Buffer.sub #uint64 #(v rresLen) #(v c0Len) res (size 0) c0Len in
  let c = bn_add c0Len c0 c0Len c1 res1 in
  res.(c0Len) <- c;
  if ((sa2 = Positive && sb2 = Positive) || (sa2 = Negative && sb2 = Negative))
  then let _ = bn_sub rresLen res c0Len c2 res in ()
  else let _ = bn_add rresLen res c0Len c2 res in ()

#reset-options "--lax"

val karatsuba_:
  #aLen:size_nat ->
  pow2_i:size_t{4 * v pow2_i < max_size_t} ->
  aaLen:size_t{v aaLen == aLen /\ aLen + aLen < max_size_t /\ v pow2_i = aLen} ->
  a:lbignum aLen -> b:lbignum aLen -> tmp:lbignum (4 * v pow2_i) ->
  res:lbignum (aLen + aLen) -> Stack unit
  (requires (fun h -> live h a /\ live h b /\ live h tmp /\ live h res /\ 
                    disjoint res a /\ disjoint res b /\ disjoint res tmp /\
                    disjoint tmp a /\ disjoint tmp b /\ disjoint tmp res))
  (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies2 res tmp h0 h1))
  [@"c_inline"]
let rec karatsuba_ #aLen pow2_i aaLen a b tmp res =
  let tmpLen = mul #SIZE (size 4) pow2_i in
  let resLen = add #SIZE aaLen aaLen in
  let pow2_i0 = pow2_i /. (size 2) in
  assume (v pow2_i = v pow2_i0 + v pow2_i0);

  if (aaLen <. size 32) then
    bn_mul #aLen #aLen aaLen a aaLen b res
  else begin
    let a0 = Buffer.sub #uint64 #aLen #(v pow2_i0) a (size 0) pow2_i0 in
    let b0 = Buffer.sub #uint64 #aLen #(v pow2_i0) b (size 0) pow2_i0 in

    let tmp0 = Buffer.sub #uint64 #(v tmpLen) #(4 * v pow2_i0) tmp (size 0) (mul #SIZE (size 4) pow2_i0) in
    let c0 = Buffer.sub #uint64 #(v resLen) #(v pow2_i) res (size 0) pow2_i in
    karatsuba_ #(v pow2_i0) pow2_i0 pow2_i0 a0 b0 tmp0 c0; // c0 = a0 * b0

    let a1 = Buffer.sub #uint64 #aLen #(v pow2_i0) a pow2_i0 pow2_i0 in
    let b1 = Buffer.sub #uint64 #aLen #(v pow2_i0) b pow2_i0 pow2_i0 in
    let tmp0 = Buffer.sub #uint64 #(v tmpLen) #(4 * v pow2_i0) tmp (size 0) (mul #SIZE (size 4) pow2_i0) in
    let c1 = Buffer.sub #uint64 #(v resLen) #(v pow2_i) res pow2_i pow2_i in
    karatsuba_ #(v pow2_i0) pow2_i0 pow2_i0 a1 b1 tmp0 c1; // c1 = a1 * b1

    let a2 = Buffer.sub #uint64 #(v tmpLen) #(v pow2_i0) tmp (size 0) pow2_i0 in
    let b2 = Buffer.sub #uint64 #(v tmpLen) #(v pow2_i0) tmp pow2_i0 pow2_i0 in
    let sa2 =  abs #(v pow2_i0) pow2_i0 a0 a1 a2 in // a2 = |a0 - a1|
    let sb2 = abs #(v pow2_i0) pow2_i0 b0 b1 b2 in // b2 = |b0 - b1|

    let c2 = Buffer.sub #uint64 #(v tmpLen) #(v pow2_i) tmp pow2_i pow2_i in
    let tmp0 = Buffer.sub #uint64 #(v tmpLen) #(4 * v pow2_i0) tmp (mul #SIZE (size 4) pow2_i0) (mul #SIZE (size 4) pow2_i0) in
    karatsuba_ #(v pow2_i0) pow2_i0 pow2_i0 a2 b2 tmp0 c2; // c2 = a2 * b2

    let tmp1Len = add #SIZE pow2_i (size 1) in
    let tmp1 = Buffer.sub #uint64 #(v tmpLen) #(v tmp1Len) tmp (mul #SIZE (size 4) pow2_i0) tmp1Len in
    add_sign #(v pow2_i0) pow2_i0 c0 c1 c2 a0 a1 a2 b0 b1 b2 sa2 sb2 tmp1Len tmp1; //tmp1 = (c0 + c1) +/- c2

    //res = [c0; c1]
    //tmp = [a2; b2; c2; tmp1; _]
    let res1Len = add #SIZE pow2_i0 pow2_i in
    let res1 = Buffer.sub #uint64 #(v resLen) #(v res1Len) res pow2_i0 res1Len in
    let _ = bn_add res1Len res1 tmp1Len tmp1 res1 in ()
    end

val karatsuba:
  #aLen:size_nat ->
  pow2_i:size_t{2 * aLen + 4 * v pow2_i < max_size_t} ->
  aaLen:size_t{v aaLen == aLen /\ aLen + aLen < max_size_t} ->
  a:lbignum aLen -> b:lbignum aLen ->
  st_kara:lbignum (aLen + aLen + 4 * v pow2_i) ->
  Stack unit
  (requires (fun h -> live h a /\ live h b /\ live h st_kara /\
                    disjoint st_kara a /\ disjoint st_kara b))
  (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 st_kara h0 h1))
  [@"c_inline"]
let karatsuba #aLen pow2_i aaLen a b st_kara =
  let stLen = add #SIZE (add #SIZE aaLen aaLen) (mul (size 4) pow2_i) in
  let res = Buffer.sub #uint64 #(v stLen) #(aLen + aLen) st_kara (size 0) (add #SIZE aaLen aaLen) in
  let st_mult = Buffer.sub #uint64 #(v stLen) #(4 * v pow2_i) st_kara (add #SIZE aaLen aaLen) (mul #SIZE (size 4) pow2_i) in
  if not (pow2_i =. aaLen)
  then bn_mul #aLen #aLen aaLen a aaLen b res
  else karatsuba_ pow2_i aaLen a b st_mult res
