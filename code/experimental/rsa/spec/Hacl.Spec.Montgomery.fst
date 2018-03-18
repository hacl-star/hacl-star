module Hacl.Spec.Montgomery

open FStar.Mul
open FStar.Math.Lemmas

open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Spec.Lib.IntSeq.Lemmas
open Hacl.Spec.Lib

open Hacl.Spec.Addition
open Hacl.Spec.Comparison
open Hacl.Spec.Multiplication
open Hacl.Spec.Shift

val bn_pow2_mod_n_:
  rLen:size_nat{0 < rLen} -> a:lseqbn rLen ->
  i:size_nat -> p:size_nat ->
  res:lseqbn rLen -> Tot (lseqbn rLen)
  (decreases (p - i))
  
let rec bn_pow2_mod_n_ rLen a i p res =
  if (i < p) then begin
    let res = bn_lshift1 rLen res res in
    let res =
      if not (bn_is_less rLen res rLen a)
      then bn_sub rLen res rLen a res
      else res in
    bn_pow2_mod_n_ rLen a (i + 1) p res end
  else res

// res = 2 ^^ p % a
val bn_pow2_mod_n:
  aBits:size_nat -> rLen:size_nat{0 < rLen /\ aBits / 64 < rLen} ->
  a:lseqbn rLen -> p:size_nat{aBits < p} ->
  res:lseqbn rLen -> Tot (lseqbn rLen)

let bn_pow2_mod_n aBits rLen a p res =
  let res = bn_set_bit rLen res aBits in
  let res = bn_sub rLen res rLen a res in // res = res - a
  bn_pow2_mod_n_ rLen a aBits p res

val mod_inv_u64_:
  alpha:uint64 -> beta:uint64 -> ub:uint64 -> vb:uint64 -> i:size_nat{i <= 64} -> Tot uint64
  (decreases (64 - i))
let rec mod_inv_u64_ alpha beta ub vb i =
  if (i < 64) then begin
    let u_is_odd = u64 0 -. (ub &. u64 1) in
    let beta_if_u_is_odd = beta &. u_is_odd in
    let ub = ((ub ^. beta_if_u_is_odd) >>. (u32 1)) +. (ub &. beta_if_u_is_odd) in

    let alpha_if_u_is_odd = alpha &. u_is_odd in
    let vb = (shift_right #U64 vb (u32 1)) +. alpha_if_u_is_odd in
    mod_inv_u64_ alpha beta ub vb (i + 1) end 
  else vb

val mod_inv_u64: n0:uint64 -> Tot uint64
let mod_inv_u64 n0 =
  let alpha = shift_left #U64 (u64 1) (u32 63) in
  let beta = n0 in

  let ub = u64 1 in
  let vb = u64 0 in
  mod_inv_u64_ alpha beta ub vb 0

val bn_mult_by_limb_addj_carry:
  aLen:size_nat{aLen > 0} -> a:lseqbn aLen ->
  l:uint64 -> carry:uint64 -> i:size_nat{i <= aLen} -> j:size_nat ->
  resLen:size_nat{aLen + j < resLen} -> res:lseqbn resLen -> Tot (tuple2 uint64 (lseqbn resLen))
  (decreases (aLen - i))
let rec bn_mult_by_limb_addj_carry aLen a l carry i j resLen res =
  let ij = i + j in
  if (i < aLen) then begin
    let res_ij = res.[ij] in
    let (carry', res_ij) = bn_mul_by_limb_addj_f a.[i] l carry res_ij in
    let res = res.[ij] <- res_ij in
    bn_mult_by_limb_addj_carry aLen a l carry' (i + 1) j resLen res end
  else begin
    let res_ij = res.[ij] in
    let (c', res_ij) = addcarry_u64 (u64 0) res_ij carry in
    let res = res.[ij] <- res_ij in
    (c', res) end

val mont_reduction_:
  rLen:size_nat{0 < rLen /\ rLen + rLen < max_size_t} ->
  c:lseqbn (rLen + rLen) -> n:lseqbn rLen -> nInv_u64:uint64 ->
  i:size_nat -> carry':uint64 -> Tot (lseqbn (rLen + rLen))
  (decreases (rLen - i))
let rec mont_reduction_ rLen c n nInv_u64 i carry' =
  if (i < rLen) then begin
    let ci = c.[i] in
    let qi = nInv_u64 *. ci in
    let (carry', c) = bn_mult_by_limb_addj_carry rLen n qi carry' 0 i (rLen + rLen) c in
    mont_reduction_ rLen c n nInv_u64 (i + 1) carry'
  end else c

val mont_reduction:
  rLen:size_nat{0 < rLen /\ rLen + rLen < max_size_t} ->
  n:lseqbn rLen -> nInv_u64:uint64 ->
  c:lseqbn (rLen + rLen) -> tmp:lseqbn (rLen + rLen) -> res:lseqbn rLen -> Tot (lseqbn rLen)
let mont_reduction rLen n nInv_u64 c tmp res =
  let rLen2:size_nat = rLen + rLen in
  let tmp = update_sub tmp 0 rLen2 c in
  let tmp = mont_reduction_ rLen tmp n nInv_u64 0 (u64 0) in
  //bn_rshift rLen2 tmp (mul #SIZE (size 64) rrLen) tmp; // tmp = tmp / r
  let tmp' = sub tmp rLen rLen in
  update_sub res 0 rLen tmp'

val to_mont:
  rLen:size_nat{0 < rLen} ->
  pow2_i:size_nat{2 * rLen + 4 * pow2_i < max_size_t /\ rLen < pow2_i} ->
  iLen:size_nat{iLen < pow2_i / 2 /\ iLen + rLen = pow2_i} ->
  n:lseqbn rLen -> nInv_u64:uint64 ->
  r2:lseqbn rLen -> a:lseqbn rLen ->
  st_kara:lseqbn (2 * rLen + 4 * pow2_i) -> aM:lseqbn rLen -> Tot (lseqbn rLen)
let to_mont rLen pow2_i iLen n nInv_u64 r2 a st_kara aM =
  let cLen = rLen + rLen in
  let stLen = cLen + 4 * pow2_i in
  let c = sub st_kara 0 cLen in 
  let c = karatsuba pow2_i iLen rLen a r2 st_kara in // c = a * r2
  mont_reduction rLen n nInv_u64 c c aM // aM = c % n

val from_mont:
  rLen:size_nat{0 < rLen} ->
  pow2_i:size_nat{2 * rLen + 4 * pow2_i < max_size_t /\ rLen < pow2_i} -> 
  iLen:size_nat{iLen < pow2_i / 2 /\ iLen + rLen = pow2_i} ->
  n:lseqbn rLen -> nInv_u64:uint64 ->
  aM:lseqbn rLen -> st:lseqbn (rLen + rLen) -> a:lseqbn rLen -> Tot (lseqbn rLen)
let from_mont rLen pow2_i iLen n nInv_u64 aM st a =
  let rLen2:size_nat = rLen + rLen in
  let st = create rLen2 (u64 0) in
  let st = update_sub st 0 rLen aM in
  mont_reduction rLen n nInv_u64 st st a // a = aM % n
