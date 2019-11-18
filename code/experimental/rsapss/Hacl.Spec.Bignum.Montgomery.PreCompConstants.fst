module Hacl.Spec.Bignum.Montgomery.PreCompConstants

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.LoopCombinators

open Hacl.Spec.Bignum
open Hacl.Spec.Bignum.Base
open Hacl.Spec.Bignum.Addition
open Hacl.Spec.Bignum.Multiplication


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"


val mod_inv_u64_f:
    alpha:uint64
  -> beta:uint64
  -> i:nat{i < 64}
  -> tuple2 uint64 uint64 ->
  tuple2 uint64 uint64

let mod_inv_u64_f alpha beta i (ub, vb) =
  let u_is_odd = u64 0 -. (ub &. u64 1) in
  let beta_if_u_is_odd = beta &. u_is_odd in
  let u = ((ub ^. beta_if_u_is_odd) >>. 1ul) +. (ub &. beta_if_u_is_odd) in

  let alpha_if_u_is_odd = alpha &. u_is_odd in
  let v = (vb >>. 1ul) +. alpha_if_u_is_odd in
  (u, v)

let mod_inv_u64_t (i:nat{i <= 64}) = tuple2 uint64 uint64

val mod_inv_u64: n0:uint64 -> uint64
let mod_inv_u64 n0 =
  let alpha = u64 1 <<. 63ul in
  let beta = n0 in
  let (u, v) = repeat_gen 64 mod_inv_u64_t (mod_inv_u64_f alpha beta) (u64 1, u64 0) in
  v


val mod_inv_u64_lemma: n0:uint64 -> Lemma
  (requires v n0 % 2 == 1)
  (ensures (let mu = mod_inv_u64 n0 in (1 + v n0 * v mu) % pow2 64 == 0))

let mod_inv_u64_lemma n0 = admit()


///
///  TODO: compute constant R2 == R * R % N, where R = pow2 (64 * rLen)
///
