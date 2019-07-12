module Hacl.Impl.Multiplication

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Lib
open Hacl.Impl.Comparison
open Hacl.Impl.Addition

module ST = FStar.HyperStack.ST

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
val bn_mul_by_limb_addj_f:
    a_i:uint64
  -> l:uint64
  -> c:uint64
  -> r_ij:uint64
  -> uint64 & uint64
let bn_mul_by_limb_addj_f a_i l c r_ij =
  assume (uint_v a_i * uint_v l + uint_v c + uint_v r_ij < pow2 128);
  let res = mul64_wide a_i l +. to_u128 c +. to_u128 r_ij in
  let r = to_u64 res in
  let c' = to_u64 (res >>. 64ul) in
  c', r

//res = res + limb * bn * beta_j
inline_for_extraction noextract
val bn_mult_by_limb_addj_add:
    aLen:size_t
  -> a:lbignum aLen
  -> l:uint64
  -> j:size_t
  -> resLen:size_t{v aLen + v j < v resLen}
  -> res:lbignum resLen
  -> carry:lbignum 1ul
  -> Stack uint64
    (requires fun h -> live h a /\ live h res /\ live h carry /\ disjoint res a)
    (ensures  fun h0 _ h1 -> modifies (loc_union (loc_buffer carry) (loc_buffer res)) h0 h1)
let bn_mult_by_limb_addj_add aLen a l j resLen res carry =
  let h0 = ST.get () in
  let inv h1 i = modifies (loc_union (loc_buffer carry) (loc_buffer res)) h0 h1 in
  Lib.Loops.for 0ul aLen inv
  (fun i ->
    let ij = i +. j in
    let res_ij = res.(ij) in
    let c, res_ij = bn_mul_by_limb_addj_f a.(i) l carry.(0ul) res_ij in
    carry.(0ul) <- c;
    res.(ij) <- res_ij
  );
  let res1Len = resLen -. (aLen +. j) in
  let res1 = sub res (aLen +. j) res1Len in
  bn_add res1Len res1 1ul carry res1

inline_for_extraction noextract
val bn_mult_by_limb_addj:
    aLen:size_t
  -> a:lbignum aLen
  -> l:uint64
  -> j:size_t
  -> resLen:size_t{v aLen + v j < v resLen}
  -> res:lbignum resLen
  -> carry:lbignum 1ul
  -> Stack unit
    (requires fun h -> live h a /\ live h res /\ live h carry /\ disjoint res a)
    (ensures  fun h0 _ h1 -> modifies (loc_union (loc_buffer carry) (loc_buffer res)) h0 h1)
let bn_mult_by_limb_addj aLen a l j resLen res carry =
  let h0 = ST.get() in
  let inv h1 i = modifies (loc_union (loc_buffer carry) (loc_buffer res)) h0 h1 in
  Lib.Loops.for 0ul aLen inv
  (fun i ->
    let ij = i +. j in
    let res_ij = res.(ij) in
    let c, res_ij = bn_mul_by_limb_addj_f a.(i) l carry.(0ul) res_ij in
    carry.(0ul) <- c;
    res.(ij) <- res_ij
  );
  res.(aLen +. j) <- carry.(0ul)

inline_for_extraction noextract
val bn_mult_:
    aLen:size_t
  -> a:lbignum aLen
  -> bLen:size_t
  -> b:lbignum bLen
  -> resLen:size_t{v resLen = v aLen + v bLen}
  -> res:lbignum resLen
  -> carry:lbignum 1ul
  -> Stack unit
    (requires fun h ->
      live h a /\ live h b /\ live h res /\ live h carry /\
      disjoint res a /\ disjoint res b)
    (ensures  fun h0 _ h1 -> modifies (loc_union (loc_buffer carry) (loc_buffer res)) h0 h1)
let bn_mult_ aLen a bLen b resLen res carry =
  let h0 = ST.get() in
  let inv h1 j = modifies (loc_union (loc_buffer carry) (loc_buffer res)) h0 h1 in
  Lib.Loops.for 0ul bLen inv
  (fun j ->
    carry.(0ul) <- u64 0;
    bn_mult_by_limb_addj aLen a b.(j) j resLen res carry
  )

// res = a * b
val bn_mul:
    aLen:size_t
  -> a:lbignum aLen
  -> bLen:size_t{v aLen + v bLen < max_size_t}
  -> b:lbignum bLen
  -> res:lbignum (aLen +. bLen)
  -> Stack unit
    (requires fun h ->
      live h a /\ live h b /\ live h res /\ disjoint res a /\ disjoint res b)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer res) h0 h1)
[@"c_inline"]
let bn_mul aLen a bLen b res =
  push_frame ();
  let resLen = aLen +. bLen in
  memset res (u64 0) resLen;
  let carry = create 1ul (u64 0) in
  bn_mult_ aLen a bLen b resLen res carry;
  pop_frame ()

type sign =
  | Positive : sign
  | Negative : sign

inline_for_extraction noextract
val abs:
    aLen:size_t
  -> a:lbignum aLen
  -> b:lbignum aLen
  -> res:lbignum aLen
  -> Stack sign
    (requires fun h -> live h a /\ live h b /\ live h res)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer res) h0 h1)
let abs aLen a b res =
  if (bn_is_less aLen a aLen b) // a < b
  then begin
    let _ = bn_sub aLen b aLen a res in
    Negative end
  else begin
    let _ = bn_sub aLen a aLen b res in
    Positive end

val add_sign:
    a0Len:size_t{v a0Len + v a0Len + 1 < max_size_t}
  -> c0:lbignum (a0Len +. a0Len)
  -> c1:lbignum (a0Len +. a0Len)
  -> c2:lbignum (a0Len +. a0Len)
  -> a0:lbignum a0Len
  -> a1:lbignum a0Len
  -> a2:lbignum a0Len
  -> b0:lbignum a0Len
  -> b1:lbignum a0Len
  -> b2:lbignum a0Len
  -> sa2:sign
  -> sb2:sign
  -> resLen:size_t{v resLen = v a0Len + v a0Len + 1}
  -> res:lbignum resLen
  -> Stack unit
    (requires fun h ->
      live h c0 /\ live h c1 /\ live h c2 /\
      live h a0 /\ live h a1 /\ live h a2 /\
      live h b0 /\ live h b1 /\ live h b2 /\
      live h res)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer res) h0 h1)
[@"c_inline"]
let add_sign a0Len c0 c1 c2 a0 a1 a2 b0 b1 b2 sa2 sb2 resLen res =
  let c0Len = a0Len +. a0Len in
  let res1 = sub #_ #(v resLen) #(v c0Len) res 0ul c0Len in
  let c = bn_add c0Len c0 c0Len c1 res1 in
  res.(c0Len) <- c;
  if ((sa2 = Positive && sb2 = Positive) || (sa2 = Negative && sb2 = Negative))
  then let _ = bn_sub resLen res c0Len c2 res in ()
  else let _ = bn_add resLen res c0Len c2 res in ()

val karatsuba_:
    pow2_i:size_t{4 * v pow2_i < max_size_t}
  -> aLen:size_t{v aLen + v aLen < max_size_t /\ v pow2_i = v aLen}
  -> a:lbignum aLen
  -> b:lbignum aLen
  -> tmp:lbignum (4ul *. pow2_i)
  -> res:lbignum (aLen +. aLen)
  -> Stack unit
    (requires fun h ->
      live h a /\ live h b /\ live h tmp /\ live h res /\
      disjoint res a /\ disjoint res b /\ disjoint res tmp)
    (ensures  fun h0 _ h1 -> modifies (loc_union (loc_buffer res) (loc_buffer tmp)) h0 h1)
[@"c_inline"]
let rec karatsuba_ pow2_i aLen a b tmp res = admit();
  let tmpLen = 4ul *. pow2_i in
  let resLen = aLen +. aLen in
  let pow2_i0 = pow2_i /. 2ul in
  assume (v pow2_i = v (pow2_i0 +. pow2_i0));
  if aLen <. 32ul then
    bn_mul aLen a aLen b res
  else begin
    let a0 = sub a 0ul pow2_i0 in
    let b0 = sub b 0ul pow2_i0 in

    let tmp0 = sub tmp 0ul (4ul *. pow2_i0) in
    let c0 = sub res 0ul pow2_i in
    karatsuba_ pow2_i0 pow2_i0 a0 b0 tmp0 c0; // c0 = a0 * b0

    let a1 = sub a pow2_i0 pow2_i0 in
    let b1 = sub b pow2_i0 pow2_i0 in
    let tmp0 = sub tmp 0ul (4ul *. pow2_i0) in
    let c1 = sub res pow2_i pow2_i in
    karatsuba_ pow2_i0 pow2_i0 a1 b1 tmp0 c1; // c1 = a1 * b1

    let a2 = sub tmp 0ul pow2_i0 in
    let b2 = sub tmp pow2_i0 pow2_i0 in
    let sa2 = abs pow2_i0 a0 a1 a2 in // a2 = |a0 - a1|
    let sb2 = abs pow2_i0 b0 b1 b2 in // b2 = |b0 - b1|

    let c2 = sub tmp pow2_i pow2_i in
    let tmp0 = sub tmp (4ul *. pow2_i0) (4ul *. pow2_i0) in
    karatsuba_ pow2_i0 pow2_i0 a2 b2 tmp0 c2; // c2 = a2 * b2

    let tmp1Len = pow2_i +. size 1 in
    let tmp1 = sub tmp (4ul *. pow2_i0) tmp1Len in
    add_sign pow2_i0 c0 c1 c2 a0 a1 a2 b0 b1 b2 sa2 sb2 tmp1Len tmp1; //tmp1 = (c0 + c1) +/- c2

    //res = [c0; c1]
    //tmp = [a2; b2; c2; tmp1; _]
    let res1Len = pow2_i0 +. pow2_i in
    let res1 = sub res pow2_i0 res1Len in
    let _ = bn_add res1Len res1 tmp1Len tmp1 res1 in ()
    end

val karatsuba:
    pow2_i:size_t
  -> aLen:size_t{v aLen + v aLen + 4 * v pow2_i < max_size_t}
  -> a:lbignum aLen
  -> b:lbignum aLen
  -> st_kara:lbignum (aLen +. aLen +. 4ul *. pow2_i)
  -> Stack unit
    (requires fun h ->
      live h a /\ live h b /\ live h st_kara /\
      disjoint st_kara a /\ disjoint st_kara b)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer st_kara) h0 h1)
[@"c_inline"]
let karatsuba pow2_i aLen a b st_kara =
  let stLen = aLen +. aLen +. 4ul *. pow2_i in
  let res = sub st_kara 0ul (aLen +. aLen) in
  let st_mult = sub st_kara (aLen +. aLen) (4ul *. pow2_i) in
  if not (pow2_i =. aLen)
  then bn_mul aLen a aLen b res
  else karatsuba_ pow2_i aLen a b st_mult res
