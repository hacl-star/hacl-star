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
  aLen:size_t -> a:lbignum aLen ->
  l:uint64 -> j:size_t ->
  resLen:size_t{v aLen + v j < v resLen} -> res:lbignum resLen ->
  carry:lbignum (size 1) -> Stack unit
  (requires (fun h -> live h a /\ live h res /\ live h carry /\ disjoint res a))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies2 carry res h0 h1))
  [@ "substitute"]
let bn_mult_by_limb_addj aLen a l j resLen res carry =
  let h0 = FStar.HyperStack.ST.get() in
  loop2_simple #h0 aLen carry res
  (fun i ->
    let ij = add #SIZE i j in
    let res_ij = res.(ij) in
    let (c, res_ij) = bn_mul_by_limb_addj_f a.(i) l carry.(size 0) res_ij in
    carry.(size 0) <- c;
    res.(ij) <- res_ij
  )


val bn_mult_:
  aLen:size_t -> a:lbignum aLen ->
  bLen:size_t -> b:lbignum bLen ->
  resLen:size_t{v resLen = v aLen + v bLen} -> res:lbignum resLen ->
  carry:lbignum (size 1) -> Stack unit
  (requires (fun h -> live h a /\ live h b /\ live h res /\ live h carry /\ disjoint res a /\ disjoint res b))
  (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies2 carry res h0 h1))
  [@ "substitute"]
let bn_mult_ aLen a bLen b resLen res carry =
  let h0 = FStar.HyperStack.ST.get() in
  loop2_simple #h0 bLen carry res
  (fun j ->
    carry.(size 0) <- u64 0;
    bn_mult_by_limb_addj aLen a b.(j) j resLen res carry;
    res.(add #SIZE aLen j) <- carry.(size 0)
  )

// res = a * b
val bn_mul:
  aLen:size_t -> a:lbignum aLen ->
  bLen:size_t{v aLen + v bLen < max_size_t} -> b:lbignum bLen ->
  res:lbignum (add #SIZE aLen bLen) -> Stack unit
  (requires (fun h -> live h a /\ live h b /\ live h res /\ disjoint res a /\ disjoint res b))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
  [@"c_inline"]
let bn_mul aLen a bLen b res =
  let resLen = add #SIZE aLen bLen in
  fill resLen res (u64 0);
  let h0 = FStar.HyperStack.ST.get () in
  alloc1 #h0 (size 1) (u64 0) res
  (fun h -> (fun _ r -> True))
  (fun carry ->
    bn_mult_ aLen a bLen b resLen res carry
  )

type sign =
  | Positive : sign
  | Negative : sign

val abs:
  aLen:size_t -> a:lbignum aLen -> b:lbignum aLen ->
  res:lbignum aLen -> Stack sign
  (requires (fun h -> live h a /\ live h b /\ live h res))
  (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
  [@"c_inline"]
let abs aLen a b res =
  if (bn_is_less aLen a aLen b) //a < b
  then begin
    let _ = bn_sub aLen b aLen a res in
    Negative end
  else begin
    let _ = bn_sub aLen a aLen b res in
    Positive end

val add_sign:
  a0Len:size_t{v a0Len + v a0Len + 1 < max_size_t} ->
  c0:lbignum (add #SIZE a0Len a0Len) -> c1:lbignum (add #SIZE a0Len a0Len) -> c2:lbignum (add #SIZE a0Len a0Len) ->
  a0:lbignum a0Len -> a1:lbignum a0Len -> a2:lbignum a0Len ->
  b0:lbignum a0Len -> b1:lbignum a0Len -> b2:lbignum a0Len ->
  sa2:sign -> sb2:sign ->
  resLen:size_t{v resLen = v a0Len + v a0Len + 1} -> res:lbignum resLen -> Stack unit
  (requires (fun h -> live h c0 /\ live h c1 /\ live h c2 /\
                    live h a0 /\ live h a1 /\ live h a2 /\
                    live h b0 /\ live h b1 /\ live h b2 /\
		    live h res))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
  [@"c_inline"]
let add_sign a0Len c0 c1 c2 a0 a1 a2 b0 b1 b2 sa2 sb2 resLen res =
  let c0Len = add #SIZE a0Len a0Len in
  let res1 = Buffer.sub #uint64 #(v resLen) #(v c0Len) res (size 0) c0Len in
  let c = bn_add c0Len c0 c0Len c1 res1 in
  res.(c0Len) <- c;
  if ((sa2 = Positive && sb2 = Positive) || (sa2 = Negative && sb2 = Negative))
  then let _ = bn_sub resLen res c0Len c2 res in ()
  else let _ = bn_add resLen res c0Len c2 res in ()

val karatsuba_:
  pow2_i:size_t{4 * v pow2_i < max_size_t} ->
  aLen:size_t{v aLen + v aLen < max_size_t /\ v pow2_i = v aLen} ->
  a:lbignum aLen -> b:lbignum aLen -> tmp:lbignum (mul #SIZE (size 4) pow2_i) ->
  res:lbignum (add #SIZE aLen aLen) -> Stack unit
  (requires (fun h -> live h a /\ live h b /\ live h tmp /\ live h res /\
                    disjoint res a /\ disjoint res b /\ disjoint res tmp))
  (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies2 res tmp h0 h1))
  #reset-options "--z3rlimit 150 --max_fuel 2"
  [@"c_inline"]
let rec karatsuba_ pow2_i aLen a b tmp res =
  let tmpLen = mul #SIZE (size 4) pow2_i in
  let resLen = add #SIZE aLen aLen in
  let pow2_i0 = pow2_i /. (size 2) in
  assume (v pow2_i = v (add #SIZE pow2_i0 pow2_i0));
  let h0 = FStar.HyperStack.ST.get() in
  if (aLen <. size 32) then begin
    bn_mul aLen a aLen b res;
    let h1 = FStar.HyperStack.ST.get() in
    lemma_modifies1_is_modifies2 res tmp h0 h1 end
  else begin
    let a0 = Buffer.sub a (size 0) pow2_i0 in
    let b0 = Buffer.sub b (size 0) pow2_i0 in

    let tmp0 = Buffer.sub tmp (size 0) (mul #SIZE (size 4) pow2_i0) in
    let c0 = Buffer.sub res (size 0) pow2_i in
    karatsuba_ pow2_i0 pow2_i0 a0 b0 tmp0 c0; // c0 = a0 * b0
    let h1 = FStar.HyperStack.ST.get() in
    assert (modifies2 res tmp h0 h1);

    let a1 = Buffer.sub a pow2_i0 pow2_i0 in
    let b1 = Buffer.sub b pow2_i0 pow2_i0 in
    let tmp0 = Buffer.sub tmp (size 0) (mul #SIZE (size 4) pow2_i0) in
    let c1 = Buffer.sub res pow2_i pow2_i in
    karatsuba_ pow2_i0 pow2_i0 a1 b1 tmp0 c1; // c1 = a1 * b1
    let h2 = FStar.HyperStack.ST.get() in
    assert (modifies2 res tmp h1 h2);

    let a2 = Buffer.sub tmp (size 0) pow2_i0 in
    let b2 = Buffer.sub tmp pow2_i0 pow2_i0 in
    let sa2 = abs pow2_i0 a0 a1 a2 in // a2 = |a0 - a1|
    let h3 = FStar.HyperStack.ST.get() in
    assert (modifies1 tmp h2 h3);
    lemma_modifies1_is_modifies2 res tmp h2 h3;
    let sb2 = abs pow2_i0 b0 b1 b2 in // b2 = |b0 - b1|
    let h4 = FStar.HyperStack.ST.get() in
    assert (modifies1 tmp h3 h4);
    lemma_modifies1_is_modifies2 res tmp h3 h4;

    let c2 = Buffer.sub tmp pow2_i pow2_i in
    let tmp0 = Buffer.sub tmp (mul #SIZE (size 4) pow2_i0) (mul #SIZE (size 4) pow2_i0) in
    karatsuba_ pow2_i0 pow2_i0 a2 b2 tmp0 c2; // c2 = a2 * b2
    let h5 = FStar.HyperStack.ST.get() in
    assert (modifies2 res tmp h4 h5);

    let tmp1Len = add #SIZE pow2_i (size 1) in
    let tmp1 = Buffer.sub tmp (mul #SIZE (size 4) pow2_i0) tmp1Len in
    add_sign pow2_i0 c0 c1 c2 a0 a1 a2 b0 b1 b2 sa2 sb2 tmp1Len tmp1; //tmp1 = (c0 + c1) +/- c2
    let h6 = FStar.HyperStack.ST.get() in
    assert (modifies1 tmp h5 h6);
    lemma_modifies1_is_modifies2 res tmp h5 h6;

    //res = [c0; c1]
    //tmp = [a2; b2; c2; tmp1; _]
    let res1Len = add #SIZE pow2_i0 pow2_i in
    let res1 = Buffer.sub res pow2_i0 res1Len in
    let _ = bn_add res1Len res1 tmp1Len tmp1 res1 in
    let h7 = FStar.HyperStack.ST.get() in
    assert (modifies1 res h6 h7);
    lemma_modifies1_is_modifies2 res tmp h6 h7
    end

val karatsuba:
  pow2_i:size_t ->
  aLen:size_t{v aLen + v aLen + 4 * v pow2_i < max_size_t} ->
  a:lbignum aLen -> b:lbignum aLen ->
  st_kara:lbignum (add #SIZE (add #SIZE aLen aLen) (mul (size 4) pow2_i)) ->
  Stack unit
  (requires (fun h -> live h a /\ live h b /\ live h st_kara /\
                    disjoint st_kara a /\ disjoint st_kara b))
  (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 st_kara h0 h1))
  [@"c_inline"]
let karatsuba pow2_i aLen a b st_kara =
  let stLen = add #SIZE (add #SIZE aLen aLen) (mul (size 4) pow2_i) in
  let res = Buffer.sub st_kara (size 0) (add #SIZE aLen aLen) in
  let st_mult = Buffer.sub #uint64 #(v stLen) #(4 * v pow2_i) st_kara (add #SIZE aLen aLen) (mul #SIZE (size 4) pow2_i) in
  if not (pow2_i =. aLen)
  then bn_mul aLen a aLen b res
  else karatsuba_ pow2_i aLen a b st_mult res
