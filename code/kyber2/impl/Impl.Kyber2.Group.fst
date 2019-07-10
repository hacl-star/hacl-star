module Impl.Kyber2.Group

open Lib.Arithmetic.Group
open Lib.IntTypes
open FStar.Math.Lemmas
open Lib.ModularArithmetic.Lemmas
open FStar.Mul
open Spec.Kyber2.Params
open Spec.Kyber2.Reduce

module Group = Spec.Kyber2.Group

#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --print_universes --using_facts_from '* -FStar.Seq'"

type t = Group.t

inline_for_extraction
let zero_t = Group.zero_t

inline_for_extraction
let one_t = Group.one_t

let int16_to_t (x:int16) : Pure t (requires True) (ensures fun r -> Group.v r == sint_v x % params_q) = Group.int16_to_t x

let uint16_to_t (x:uint16) : Pure t (requires True) (ensures fun r -> Group.v r == uint_v x % params_q) = Group.uint16_to_t x

let plus_t (x:t) (y:t) : Pure t (requires True) (ensures fun r -> r == op #t #Group.monoid_plus_t x y) = Group.plus_t x y

let mul_t (x:t) (y:t) : Pure t (requires True) (ensures fun r -> r == op #t #Group.monoid_mul_t x y) = Group.mul_t x y

let opp_t (x:t) : Pure t (requires True) (ensures fun r -> r == sym #t #Group.group_t x) = Group.opp_t x

let rec exp_t (x:t) (n:size_t) : Pure t (requires True) (ensures fun r -> r == repeat_op #t #Group.monoid_mul_t x (v n)) (decreases (v n)) =
  if (n =. (size 0)) then one_t
  else let b = exp_t x (n /. (size 2)) in
  let b2 = mul_t b b in
  if (n %. (size 2) =. (size 0)) then b2 else mul_t x b2

