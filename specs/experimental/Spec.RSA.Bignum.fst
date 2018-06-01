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
  #nBits:size_nat ->
  rBits:size_nat{nBits < rBits /\ nBits + rBits + 1 < max_size_t} ->
  nInv_u64:bignum 64 -> n:bignum nBits ->
  c:bignum (nBits + rBits) ->
  i:size_nat{64 * (i + 1) <= rBits} -> res:bignum (nBits + rBits) ->
  Tot (res:bignum (nBits + rBits))
  #reset-options "--z3rlimit 30 --max_fuel 0"
let mont_reduction_f #nBits rBits nInv_u64 n c i res =
  let res_i = bn_get_bits res (i * 64) ((i + 1)*64) in
  let qi = bn_get_bits (bn_mul nInv_u64 res_i) 0 64 in
  let res1 = bn_lshift_mul_add #nBits #(nBits + rBits) n (64*i) qi res in
  assume (bn_v res1 < pow2 (nBits + rBits));
  let res1 = bn_cast #(nBits + rBits + 1) (nBits + rBits) res1 in
  res1

val mont_reduction_:
  #nBits:size_nat ->
  rBits:size_nat{nBits < rBits /\ nBits + rBits + 1 < max_size_t /\ rBits % 64 == 0} ->
  nInv_u64:bignum 64 -> n:bignum nBits ->
  c:bignum (nBits + rBits) ->
  Tot (res:bignum (nBits + rBits))

let mont_reduction_ #nBits rBits nInv_u64 n c =
  let rLen = rBits / 64 in
  repeati rLen
  (fun i res ->
    mont_reduction_f #nBits rBits nInv_u64 n c i res) c

val mont_reduction:
  #nBits:size_nat{nBits > 0} ->
  rBits:size_nat{nBits < rBits /\ nBits + rBits + 1 < max_size_t /\ rBits % 64 == 0} ->
  nInv_u64:bignum 64 -> n:bignum nBits ->
  c:bignum (nBits + rBits) -> Tot (res:bignum nBits)

let mont_reduction #nBits rBits nInv_u64 n c =
  let tmp = mont_reduction_ #nBits rBits nInv_u64 n c in
  let res = bn_rshift tmp rBits in
  res

val mul_mod_mont:
  #nBits:size_nat{nBits > 0} ->
  rBits:size_nat{nBits < rBits /\ nBits + rBits + 1 < max_size_t /\ rBits % 64 == 0} ->
  nInv_u64:bignum 64 -> n:bignum nBits ->
  a:bignum nBits -> b:bignum nBits -> Tot (res:bignum nBits)
let mul_mod_mont #nBits rBits nInv_u64 n a b =
  let c = bn_mul a b in
  assume (bn_v c < pow2 (nBits + rBits));
  let c = bn_cast #(nBits + nBits) (nBits + rBits) c in
  mont_reduction #nBits rBits nInv_u64 n c

val to_mont:
  #nBits:size_nat{nBits > 0} ->
  rBits:size_nat{nBits < rBits /\ nBits + rBits + 1 < max_size_t /\ rBits % 64 == 0} ->
  nInv_u64:bignum 64 -> n:bignum nBits ->
  r2:bignum nBits -> a:bignum nBits -> Tot (res:bignum nBits)
let to_mont #nBits rBits nInv_u64 n r2 a =
  let c = bn_mul a r2 in
  assume (bn_v c < pow2 (nBits + rBits));
  let c = bn_cast #(nBits + nBits) (nBits + rBits) c in
  let res = mont_reduction #nBits rBits nInv_u64 n c in
  res

val from_mont:
  #nBits:size_nat{nBits > 0} ->
  rBits:size_nat{nBits < rBits /\ nBits + rBits + 1 < max_size_t /\ rBits % 64 == 0} ->
  nInv_u64:bignum 64 -> n:bignum nBits ->
  a_r:bignum nBits -> Tot (res:bignum nBits)

let from_mont #nBits rBits nInv_u64 n a_r =
  assume (bn_v a_r < pow2 (nBits + rBits));
  let a_r = bn_cast #nBits (nBits + rBits) a_r in
  let tmp = mont_reduction_ #nBits rBits nInv_u64 n a_r in
  let res = bn_rshift tmp rBits in
  res

val mod_exp_:
  #nBits:size_nat{nBits > 0} ->
  rBits:size_nat{nBits < rBits /\ nBits + rBits + 1 < max_size_t /\ rBits % 64 == 0} ->
  nInv_u64:bignum 64 -> n:bignum nBits ->
  a:bignum nBits ->
  bBits:size_nat -> b:bignum bBits ->
  acc:bignum nBits -> Tot (res:bignum nBits)
let mod_exp_ #nBits rBits nInv_u64 n a bBits b acc =
  let (a, acc) =
    repeati bBits
    (fun i (a, acc) ->
      let acc = if (bn_get_bit #bBits b i = 1) then mul_mod_mont #nBits rBits nInv_u64 n a acc else acc in
      let a = mul_mod_mont #nBits rBits nInv_u64 n a a in
      (a, acc)
    ) (a, acc) in
  acc

val mod_exp:
  #nBits:size_nat{64 <= nBits /\ 2 * 64 * (blocks nBits 64 + 1) < max_size_t} ->
  n:bignum nBits{0 < bn_v n} -> a:bignum nBits ->
  bBits:size_nat -> b:bignum bBits -> Tot (res:bignum nBits)
let mod_exp #nBits n a bBits b =
  let nLen = blocks nBits 64 in
  let rBits = 64 * (nLen + 1) in
  let r2 = bn_pow2_r_mod n (rBits * 2) in
  let n0 = bn_get_bits n 0 64 in
  let nInv_u64 = bn_from_u64 (mod_inv_u64 (bn_to_u64 n0)) in
  let a_r = to_mont #nBits rBits nInv_u64 n r2 a in
  let acc_r = to_mont #nBits rBits nInv_u64 n r2 (bn #nBits 1) in
  let res_r = mod_exp_ #nBits rBits nInv_u64 n a_r bBits b acc_r in
  let res = from_mont #nBits rBits nInv_u64 n res_r in
  res

val rsa_blinding:
  #nBits:size_nat{64 <= nBits /\ 2 * 64 * (blocks nBits 64 + 1) < max_size_t} ->
  #pBits:size_nat{0 < pBits} -> #qBits:size_nat{0 < qBits /\ pBits + qBits + 64 < max_size_t} ->
  n:bignum nBits{0 < bn_v n} ->
  p:bignum pBits{0 < bn_v p} -> q:bignum qBits{0 < bn_v q /\ bn_v n == bn_v p * bn_v q} ->
  m:bignum nBits ->
  dBits:size_nat{dBits < pBits + qBits + 64} -> d:bignum dBits ->
  rBlind:bignum 63 -> Tot (s:bignum nBits)
let rsa_blinding #nBits #pBits #qBits n p q m dBits d rBlind =
  let bn_1 = bn #1 1 in
  let p1 = bn_sub p bn_1 in
  let q1 = bn_sub q bn_1 in
  let phi_n = bn_mul p1 q1 in
  let d1 = bn_mul phi_n rBlind in
  let d1 = bn_add d1 d in
  //let d1 = bn_lshift_mul_add phi_n 0 rBlind d
  let s = mod_exp #nBits n m (pBits + qBits + 64) d1 in
  s
