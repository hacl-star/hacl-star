module Hacl.Spec.Bignum.Field

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul
open Hacl.Bignum.Constants


#set-options "--z3rlimit 10"

(** Type of elements of the commutative field Z/pZ where p is prime **)
type elem = e:int{e >= 0 /\ e < prime}

val zero: elem
let zero = 0

val one:elem
let one = 1

let addition (a:elem) (b:elem) : Tot elem = (a + b) % prime
let multiplication (a:elem) (b:elem) : Tot elem = (a * b) % prime
let opposite (a:elem) : Tot elem = (prime - a - 1)

let rec scalarmult (a:elem) (b:nat) : Tot elem =
  if b = 0 then 0 else addition a (scalarmult a (b-1))
let rec exp (a:elem) (b:nat) : Tot elem =
  if b = 0 then 1 else multiplication a (exp a (b-1))

let inverse (a:elem) : Tot elem = exp a (prime - 2)

val lemma_addition_is_commutative: a:elem -> b:elem -> Lemma (addition a b = addition b a)
let lemma_addition_is_commutative a b = ()
val lemma_multiplication_is_commutative: a:elem -> b:elem -> Lemma (multiplication a b = multiplication b a)
let lemma_multiplication_is_commutative a b = ()

assume val lemma_addition_associativity: a:elem -> b:elem -> c:elem ->
  Lemma (addition (addition a b) c = addition a (addition b c))
assume val lemma_multiplication_associativity: a:elem -> b:elem -> c:elem ->
  Lemma (multiplication (multiplication a b) c = multiplication a (multiplication b c))

val lemma_addition_neutral_element: a:elem ->
  Lemma (addition a zero = a)
let lemma_addition_neutral_element a = ()
val lemma_multiplication_neutral_element: a:elem ->
  Lemma (multiplication a one = a)
let lemma_multiplication_neutral_element a = ()

assume val lemma_addition_symmetry: a:elem ->
  Lemma (addition (opposite a) a = zero)
assume val lemma_multiplication_symmetry: a:elem ->
  Lemma (multiplication (inverse a) a = one)

inline_for_extraction let op_At_Plus a b = addition a b
inline_for_extraction let op_At_Star a b = multiplication a b
inline_for_extraction let op_At_Plus_Plus a b = scalarmult b a
inline_for_extraction let op_At_Star_Star a b = exp b a
