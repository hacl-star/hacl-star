module Spec.RSA.Bignum

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Spec.Lib.RawIntTypes

open FStar.Math.Lemmas
open Spec.RSA.Lemmas
open Spec.Bignum.Basic

val mod_inv_u64: n0:uint64 -> Tot uint64
let mod_inv_u64 n0 =
  let alpha = shift_left #U64 (u64 1) (u32 63) in
  let beta = n0 in
  let (ub, vb) =
    repeati 64
    (fun i (ub, vb) ->
      let u_is_odd = u64 0 -. (ub &. u64 1) in
      let beta_if_u_is_odd = beta &. u_is_odd in
      let ub = ((ub ^. beta_if_u_is_odd) >>. (u32 1)) +. (ub &. beta_if_u_is_odd) in

      let alpha_if_u_is_odd = alpha &. u_is_odd in
      let vb = (shift_right #U64 vb (u32 1)) +. alpha_if_u_is_odd in
      (ub, vb)) (u64 1, u64 0) in
  vb

(* Montgomery's arithmetic *)
val mont_reduction_f:
  #nBits:size_pos -> #cBits:size_pos ->
  rBits:size_pos{nBits < rBits /\ nBits+1+rBits < max_size_t} ->
  nInv_u64:bignum 64 -> n:bignum nBits ->
  c:bignum cBits ->
  i:size_nat{64 * (i+1) <= rBits} -> res:bignum (nBits + 1 + rBits) ->
  Tot (res:bignum (nBits + 1 + rBits))
  #reset-options "--z3rlimit 30 --max_fuel 0"
let mont_reduction_f #nBits #cBits rBits nInv_u64 n c i res =
  let res_i = bn_get_bits res (i * 64) ((i + 1)*64) in
  let qi = bn_get_bits (bn_mul nInv_u64 res_i) 0 64 in
  let (c, res1) = bn_lshift_mul_add n (64*i) qi res in
  assert (bn_v res1 + uint_v c * pow2 (nBits + 1 + rBits) == bn_v res + (bn_v n) * pow2 (64*i) * (bn_v qi));
  assume (bn_v res + (bn_v n) * pow2 (64*i) * (bn_v qi) < pow2 (nBits + 1 + rBits));
  assert (uint_v c == 0);
  res1

val mont_reduction_:
  #nBits:size_pos -> #cBits:size_pos ->
  rBits:size_pos{nBits < rBits /\ nBits + 1 + rBits < max_size_t /\ rBits % 64 == 0} ->
  nInv_u64:bignum 64 -> n:bignum nBits ->
  c:bignum cBits{cBits < nBits + 1 + rBits} ->
  Tot (res:bignum (nBits + 1 + rBits))

let mont_reduction_ #nBits #cBits rBits nInv_u64 n c =
  assume (bn_v c < pow2 (nBits + 1 + rBits));
  let tmp = bn_cast_gt (nBits + 1 + rBits) c in
  let rLen = rBits / 64 in
  repeati rLen
  (fun i res ->
    mont_reduction_f rBits nInv_u64 n c i res) tmp

val mont_reduction:
  #nBits:size_pos -> #cBits:size_pos ->
  rBits:size_pos{nBits < rBits /\ nBits + 1 + rBits < max_size_t /\ rBits % 64 == 0} ->
  nInv_u64:bignum 64 -> n:bignum nBits ->
  c:bignum cBits{cBits < nBits + 1 + rBits} -> Tot (res:bignum (nBits+1))

let mont_reduction #nBits #cBits rBits nInv_u64 n c =
  let tmp = mont_reduction_ rBits nInv_u64 n c in
  let res = bn_rshift tmp rBits in
  res

val mul_mod_mont:
  nBits:size_pos ->
  rBits:size_pos{nBits + 1 < rBits /\ nBits + rBits + 1 < max_size_t /\ rBits % 64 == 0} ->
  nInv_u64:bignum 64 -> n:bignum nBits ->
  a:bignum (nBits+1) -> b:bignum (nBits+1) -> Tot (res:bignum (nBits+1))
let mul_mod_mont nBits rBits nInv_u64 n a b =
  let c = bn_mul a b in
  mont_reduction rBits nInv_u64 n c

val to_mont:
  #aBits:size_pos -> nBits:size_pos ->
  rBits:size_pos{nBits < rBits /\ nBits + rBits + 1 < max_size_t /\ rBits % 64 == 0} ->
  nInv_u64:bignum 64 -> n:bignum nBits ->
  r2:bignum nBits -> a:bignum aBits{aBits <= nBits} -> Tot (res:bignum (nBits+1))
let to_mont #aBits nBits rBits nInv_u64 n r2 a =
  let c = bn_mul a r2 in
  let res = mont_reduction rBits nInv_u64 n c in
  res

val from_mont:
  nBits:size_pos ->
  rBits:size_pos{nBits < rBits /\ nBits + rBits + 1 < max_size_t /\ rBits % 64 == 0} ->
  nInv_u64:bignum 64 -> n:bignum nBits ->
  a_r:bignum (nBits+1) -> Tot (res:bignum nBits)

let from_mont nBits rBits nInv_u64 n a_r =
  let tmp = mont_reduction_ rBits nInv_u64 n a_r in
  let res = bn_rshift tmp rBits in
  assume (bn_v res < pow2 nBits);
  let res = bn_cast_le nBits res in
  res

val mod_exp_:
  nBits:size_pos ->
  rBits:size_pos{nBits + 1 < rBits /\ nBits + rBits + 1 < max_size_t /\ rBits % 64 == 0} ->
  nInv_u64:bignum 64 -> n:bignum nBits ->
  a:bignum (nBits+1) ->
  bBits:size_pos -> b:bignum bBits ->
  acc:bignum (nBits+1) -> Tot (res:bignum (nBits+1))
let mod_exp_ nBits rBits nInv_u64 n a bBits b acc =
  let (a, acc) =
    repeati bBits
    (fun i (a, acc) ->
      let acc = if (bn_get_bit b i = 1) then mul_mod_mont nBits rBits nInv_u64 n a acc else acc in
      let a = mul_mod_mont nBits rBits nInv_u64 n a a in
      (a, acc)
    ) (a, acc) in
  acc

val mod_exp:
  #aBits:size_pos ->
  nBits:size_pos{64 <= nBits /\ 2 * 64 * (blocks nBits 64 + 1) < max_size_t} ->
  n:bignum nBits{0 < bn_v n} -> a:bignum aBits{aBits <= nBits} ->
  bBits:size_pos -> b:bignum bBits -> Tot (res:bignum nBits)
let mod_exp #aBits nBits n a bBits b =
  let nLen = blocks nBits 64 in
  let rBits = 64 * (nLen + 1) in
  let r2 = bn_pow2_r_mod n (rBits * 2) in
  let n0 = bn_get_bits n 0 64 in
  let nInv_u64 = bn_from_u64 (mod_inv_u64 (bn_to_u64 n0)) in
  let a_r = to_mont nBits rBits nInv_u64 n r2 a in
  let acc_r = to_mont nBits rBits nInv_u64 n r2 (bn_const_1 #nBits) in
  let res_r = mod_exp_ nBits rBits nInv_u64 n a_r bBits b acc_r in
  let res = from_mont nBits rBits nInv_u64 n res_r in
  res

val rsa_blinding:
  #mBits:size_pos ->
  nBits:size_pos{64 <= nBits /\ 2 * 64 * (blocks nBits 64 + 1) < max_size_t} -> n:bignum nBits{0 < bn_v n} ->
  pBits:size_pos -> p:bignum pBits{0 < bn_v p} ->
  qBits:size_pos{pBits + qBits + 64 < max_size_t} -> q:bignum qBits{0 < bn_v q /\ bn_v n == bn_v p * bn_v q} ->
  m:bignum mBits{mBits <= nBits} ->
  dBits:size_pos{dBits < pBits + qBits + 64} -> d:bignum dBits ->
  rBlind:bignum 64 -> Tot (s:bignum nBits)
let rsa_blinding #mBits nBits n pBits p qBits q m dBits d rBlind =
  let bn_1 = bn_const_1 #1 in
  let p1 = bn_sub p bn_1 in
  let q1 = bn_sub q bn_1 in
  let phi_n = bn_mul p1 q1 in
  let d1 = bn_mul phi_n rBlind in
  let (c, d2) = bn_add d1 d in
  assert (bn_v d2 + uint_v c * pow2 (pBits + qBits + 64) == bn_v d1 + bn_v d);
  assume (bn_v d1 + bn_v d < pow2 (pBits + qBits + 64));
  assert (uint_v c == 0);
  let s = mod_exp nBits n m (pBits + qBits + 64) d2 in
  s
