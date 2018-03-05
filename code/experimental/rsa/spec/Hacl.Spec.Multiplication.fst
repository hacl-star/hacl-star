module Hacl.Spec.Multiplication

open FStar.Mul
open FStar.Math.Lemmas

open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Spec.Lib.IntSeq.Lemmas
open Spec.Lib.RawIntTypes

open Hacl.Spec.Lib
open Hacl.Spec.Addition
open Hacl.Spec.Comparison

val mul_wide: a:uint64 -> b:uint64 -> Tot uint128
let mul_wide a b = u128_from_UInt128 (FStar.UInt128.mul_wide (u64_to_UInt64 a) (u64_to_UInt64 b))

val bn_mul_by_limb_addj_f: a_i:uint64 -> l:uint64 -> c:uint64 -> r_ij:uint64 -> Tot (tuple2 uint64 uint64)
let bn_mul_by_limb_addj_f a_i l c r_ij =
  assume (uint_v a_i * uint_v l + uint_v c + uint_v r_ij < pow2 128);
  let res = mul_wide a_i l +! to_u128 c +! to_u128 r_ij in
  let r = to_u64 res in
  let c' = to_u64 (res >>. u32 64) in
  (c', r)

val bn_mult_by_limb_addj:
  aLen:size_nat{aLen > 0} -> a:lseqbn aLen ->
  l:uint64 -> i:size_nat{i <= aLen} -> j:size_nat ->
  resLen:size_nat{aLen + j < resLen} ->
  carry:uint64 -> res:lseqbn resLen -> Tot (lseqbn resLen)
  (decreases (aLen - i))
let rec bn_mult_by_limb_addj aLen a l i j resLen carry res =
  if (i < aLen) then begin
    let (carry', res_ij) = bn_mul_by_limb_addj_f a.[i] l carry res.[i + j] in
    let res' = res.[i + j] <- res_ij in
    bn_mult_by_limb_addj aLen a l (i + 1) j resLen carry' res' end
  else res.[i + j] <- carry

val bn_mult_:
  aLen:size_nat{aLen > 0} -> a:lseqbn aLen ->
  bLen:size_nat{bLen > 0} -> b:lseqbn bLen ->
  j:size_nat{j <= bLen} ->
  resLen:size_nat{resLen = aLen + bLen} -> res:lseqbn resLen -> Tot (lseqbn resLen)
  (decreases (bLen - j))
let rec bn_mult_ aLen a bLen b j resLen res =
  if (j < bLen) then begin
    let res' = bn_mult_by_limb_addj aLen a b.[j] 0 j resLen (u64 0) res in
    bn_mult_ aLen a bLen b (j + 1) resLen res' end
  else res

// res = a * b
val bn_mul:
  aLen:size_nat{aLen > 0} -> a:lseqbn aLen ->
  bLen:size_nat{bLen > 0 /\ aLen + bLen < max_size_t} -> b:lseqbn bLen ->
  res:lseqbn (aLen + bLen) -> Tot (lseqbn (aLen + bLen))
let bn_mul aLen a bLen b res =
  let resLen = aLen + bLen in
  let res = create resLen (u64 0) in
  bn_mult_ aLen a bLen b 0 resLen res

val bn_mul_u64:
  aLen:size_nat{0 < aLen /\ aLen + 1 < max_size_t} ->
  a:lseqbn aLen -> b:uint64 -> res:lseqbn (aLen + 1) -> Tot (lseqbn (aLen + 1))
let bn_mul_u64 aLen a b res =
  let resLen = aLen + 1 in
  let res = create resLen (u64 0) in
  bn_mult_by_limb_addj aLen a b 0 0 resLen (u64 0) res

(* Karatsuba's multiplication *)
type sign =
     | Positive : sign
     | Negative : sign

val abs:
  aLen:size_nat -> a:lseqbn aLen ->
  bLen:size_nat{0 < bLen /\ bLen <= aLen} -> b:lseqbn bLen ->
  res:lseqbn aLen -> Tot (tuple2 sign (lseqbn aLen))
let abs aLen a bLen b res =
  if (bn_is_less aLen a bLen b) //a < b
  then begin
    let a' = sub a 0 bLen in
    let res' = sub res 0 bLen in
    let res' = bn_sub bLen b bLen a' res' in
    let res = update_sub res 0 bLen res' in 
    (Negative, res) end
  else begin
    let res = bn_sub aLen a bLen b res in
    (Positive, res) end

val add_sign:
  a0Len:size_nat ->
  a1Len:size_nat{0 < a1Len /\ a1Len <= a0Len} ->
  resLen:size_nat{resLen = a0Len + a0Len + 1 /\ resLen < max_size_t} ->
  c0:lseqbn (a0Len + a0Len) -> c1:lseqbn (a1Len + a1Len) -> c2:lseqbn (a0Len + a0Len) ->
  a0:lseqbn a0Len -> a1:lseqbn a1Len -> a2:lseqbn a0Len ->
  b0:lseqbn a0Len -> b1:lseqbn a1Len -> b2:lseqbn a0Len ->
  sa2:sign -> sb2:sign ->
  res:lseqbn resLen -> Tot (lseqbn resLen)
let add_sign a0Len a1Len resLen c0 c1 c2 a0 a1 a2 b0 b1 b2 sa2 sb2 res =
  let c0Len = a0Len + a0Len in
  let c1Len = a1Len + a1Len in
  let res = bn_add_carry c0Len c0 c1Len c1 res in
  if ((sa2 = Positive && sb2 = Positive) || (sa2 = Negative && sb2 = Negative))
  then bn_sub resLen res c0Len c2 res
  else bn_add resLen res c0Len c2 res

val karatsuba_:
  pow2_i:size_nat{4 * pow2_i < max_size_t} -> iLen:size_nat{iLen < pow2_i / 2} ->
  aLen:size_nat{0 < aLen /\ aLen + aLen < max_size_t /\ iLen + aLen = pow2_i} ->
  a:lseqbn aLen -> b:lseqbn aLen ->
  tmp:lseqbn (4 * pow2_i) ->
  res:lseqbn (aLen + aLen) -> Tot (lseqbn (aLen + aLen))
  (decreases pow2_i)

#reset-options "--z3rlimit 50 --max_fuel 2"
let rec karatsuba_ pow2_i iLen aLen a b tmp res =
  let tmpLen = 4 * pow2_i in
  let pow2_i0 = pow2_i / 2 in
  assume (pow2_i = pow2_i0 + pow2_i0);
    
  if (aLen < 32) then
    bn_mul aLen a aLen b res
  else begin    
    let a0 = sub a 0 pow2_i0 in
    let b0 = sub b 0 pow2_i0 in

    let tmp0 = sub tmp 0 (4 * pow2_i0) in
    let c0 = sub res 0 pow2_i in
    let c0 = karatsuba_ pow2_i0 0 pow2_i0 a0 b0 tmp0 c0 in // c0 = a0 * b0
    let res = update_sub res 0 pow2_i c0 in
       
    let pow2_i1 = pow2_i0 - iLen in
    if (pow2_i1 = 1) then begin
      let a1 = sub a pow2_i0 1 in
      let b1 = sub b pow2_i0 1 in
	         
      let c1 = mul_wide a1.[0] b1.[0] in
      let res = res.[pow2_i] <- to_u64 c1 in
      let res = res.[pow2_i + 1] <- to_u64 (c1 >>. u32 64) in

      let tmp1Len = pow2_i0 + 1 in
      let tmp1Len2 = tmp1Len + tmp1Len in
      let tmp2Len = pow2_i0 + 2 in
	  
      let tmp0 = sub tmp 0 tmp1Len in
      let tmp1 = sub tmp tmp1Len tmp1Len in
      let tmp2 = sub tmp tmp1Len2 tmp2Len in
      let res1 = sub res pow2_i0 tmp2Len in
	  
      let tmp0 = bn_mul_u64 pow2_i0 a0 b1.[0] tmp0 in // tmp0 = a0 * b1_0
      let tmp1 = bn_mul_u64 pow2_i0 b0 a1.[0] tmp1 in // tmp1 = b0 * a1_0
      let tmp2 = bn_add_carry tmp1Len tmp0 tmp1Len tmp1 tmp2 in // tmp2 = tmp0 + tmp1
      let res1 = bn_add tmp2Len res1 tmp2Len tmp2 res1 in
      update_sub res pow2_i0 tmp2Len res1 end
    else begin
      let a1 = sub a pow2_i0 pow2_i1 in
      let b1 = sub b pow2_i0 pow2_i1 in
      let pow2_i02 = pow2_i0 / 2 in
      assume (pow2_i0 + pow2_i0 = pow2_i02);
      let ind = if (pow2_i02 < iLen) then iLen - pow2_i02 else iLen in
      let tmp0 = sub tmp 0 (4 * pow2_i0) in
      let c1 = sub res pow2_i (2 * pow2_i1) in
      let c1 = karatsuba_ pow2_i0 ind pow2_i1 a1 b1 tmp0 c1 in // c1 = a1 * b1

      let a2 = sub tmp 0 pow2_i0 in
      let b2 = sub tmp pow2_i0 pow2_i0 in
      let (sa2, a2) = abs pow2_i0 a0 pow2_i1 a1 a2 in // a2 = |a0 - a1|
      let (sb2, b2) = abs pow2_i0 b0 pow2_i1 b1 b2 in // b2 = |b0 - b1|

      let c2 = sub tmp pow2_i pow2_i in
      let tmp0 = sub tmp (4 * pow2_i0) (4 * pow2_i0) in
      let c2 = karatsuba_ pow2_i0 0 pow2_i0 a2 b2 tmp0 c2 in // c2 = a2 * b2

      let tmp1Len = pow2_i + 1 in
      let tmp1 = sub tmp (4 * pow2_i0) tmp1Len in
      let tmp1 = add_sign pow2_i0 pow2_i1 tmp1Len c0 c1 c2 a0 a1 a2 b0 b1 b2 sa2 sb2 tmp1 in //tmp1 = (c0 + c1) +/- c2

      //res = [c0; c1]
      //tmp = [a2; b2; c2; tmp1; _]
      let res1Len = pow2_i0 + pow2_i1 + pow2_i1 in
      let res1 = sub res pow2_i0 res1Len in
      let res1 = bn_add res1Len res1 tmp1Len tmp1 res1 in
      update_sub res pow2_i0 res1Len res1 end
  end

// aLen + iLen == pow2_i
// iLen is the number of leading zeroes
val karatsuba:
  pow2_i:size_nat{4 * pow2_i < max_size_t} -> iLen:size_nat{iLen < pow2_i / 2} ->
  aLen:size_nat{0 < aLen /\ aLen + aLen < max_size_t /\ iLen + aLen = pow2_i} ->
  a:lseqbn aLen -> b:lseqbn aLen ->
  st_mult:lseqbn (4 * pow2_i) ->
  res:lseqbn (aLen + aLen) -> Tot (lseqbn (aLen + aLen))

let karatsuba pow2_i iLen aLen a b st_mult res =
  if (aLen < 32)
  then bn_mul aLen a aLen b res
  else karatsuba_ pow2_i iLen aLen a b st_mult res
