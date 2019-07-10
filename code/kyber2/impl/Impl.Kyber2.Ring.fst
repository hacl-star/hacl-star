module Impl.Kyber2.Ring

open Lib.Arithmetic.Group
open Lib.Arithmetic.Ring
open Lib.IntTypes
open FStar.Math.Lemmas
open Lib.ModularArithmetic.Lemmas
open FStar.Mul
open Spec.Kyber2.Params
open Spec.Kyber2.Reduce

module Group = Spec.Kyber2.Group
module Ring = Spec.Kyber2.Ring

#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --print_universes --using_facts_from '* -FStar.Seq'"

type t = Group.t

let zero_t : (x:t{x == zero #t #Ring.ring_t}) = Group.zero_t

let one_t : (x:t{x == one #t #Ring.ring_t}) = Group.one_t

let plus_t (x:t) (y:t) : Pure t (requires True) (ensures fun r -> r == plus #t #Ring.ring_t x y) = Group.plus_t x y

let opp_t (x:t) : Pure t (requires True) (ensures fun r -> r == opp #t #Ring.ring_t x) = Group.opp_t x

let minus_t (x:t) (y:t) : Pure t (requires True) (ensures fun r -> r == minus #t #Ring.ring_t x y) =
  assert_norm (range params_q S16);
  assert_norm (range (Group.v x + (params_q - Group.v y)) S16);
  csubq_int16 (Lib.IntTypes.add x (Lib.IntTypes.sub (i16 params_q) y))

let mul_t (x:t) (y:t) : Pure t (requires True) (ensures fun r -> r == Lib.Arithmetic.Ring.mul #t #Ring.ring_t x y) = Group.mul_t x y

let exp_t (x:t) (n:size_t) : Pure t (requires True) (ensures fun r -> r == exp #t #Ring.ring_t x (v n)) = Impl.Kyber2.Group.exp_t x n

