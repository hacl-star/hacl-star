module Hacl.Spec.Bignum.Montgomery

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.LoopCombinators

open Hacl.Spec.Bignum
open Hacl.Spec.Bignum.Base
open Hacl.Spec.Bignum.Addition
open Hacl.Spec.Bignum.Multiplication


(**
https://members.loria.fr/PZimmermann/mca/mca-cup-0.5.9.pdf
https://eprint.iacr.org/2017/1057.pdf *)

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"


val mod_inv_u64: n0:uint64 -> uint64
let mod_inv_u64 n0 =
  let alpha = u64 1 <<. 63ul in
  let beta = n0 in
  let (u, v) = repeati 64
  (fun i (ub, vb) ->
    let u_is_odd = u64 0 -. (ub &. u64 1) in
    let beta_if_u_is_odd = beta &. u_is_odd in
    let u = ((ub ^. beta_if_u_is_odd) >>. 1ul) +. (ub &. beta_if_u_is_odd) in

    let alpha_if_u_is_odd = alpha &. u_is_odd in
    let v = (vb >>. 1ul) +. alpha_if_u_is_odd in
    (u, v)) (u64 1, u64 0) in
  v


val mont_reduction_:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> nInv_u64:uint64
  -> j:size_nat{j < rLen}
  -> res:lbignum (rLen + rLen) ->
  lbignum (rLen + rLen)

let mont_reduction_ #nLen #rLen n nInv_u64 j res =
  let qj = nInv_u64 *. res.[j] in
  let res' = sub res j nLen in
  let c, res' = bn_mul_by_limb_addj #nLen n qj res' in
  let res = update_sub res j nLen res' in

  let res' = sub res (j + nLen) (rLen + rLen - j - nLen) in
  let _, res' = bn_add res' (create 1 c) in
  update_sub res (j + nLen) (rLen + rLen - j - nLen) res'


val mont_reduction:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> nInv_u64:uint64
  -> c:lbignum (rLen + rLen) ->
  lbignum rLen

let mont_reduction #nLen #rLen n nInv_u64 c =
  let c = repeati rLen (mont_reduction_ #nLen #rLen n nInv_u64) c in
  sub c rLen rLen


val to_mont:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> nInv_u64:uint64
  -> r2:lbignum nLen
  -> a:lbignum nLen ->
  aM:lbignum rLen

let to_mont #nLen #rLen n nInv_u64 r2 a =
  let c = bn_mul a r2 in // c = a * r2
  let tmp = create (rLen + rLen) (u64 0) in
  let tmp = update_sub tmp 0 (nLen + nLen) c in
  mont_reduction #nLen #rLen n nInv_u64 tmp // aM = c % n


val from_mont:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> nInv_u64:uint64
  -> aM:lbignum rLen ->
  a:lbignum nLen

let from_mont #nLen #rLen n nInv_u64 aM =
  let tmp = create (rLen + rLen) (u64 0) in
  let tmp = update_sub tmp 0 rLen aM in
  let a' = mont_reduction #nLen #rLen n nInv_u64 tmp in
  sub a' 0 nLen
