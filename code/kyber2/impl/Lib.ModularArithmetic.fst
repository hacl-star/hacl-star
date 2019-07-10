module Lib.ModularArithmetic

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open FStar.Mul
open FStar.Math.Lemmas
open FStar.Classical
open FStar.Tactics

module Seq = Lib.Sequence
module Loops = Lib.LoopCombinators


#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"


type field q = x:nat{x<q}

(** modular_addition *)

inline_for_extraction
val modular_add:
  #q:nat
  -> x:field q
  -> y:field q
  -> Tot (z:field q)

let modular_add #q x y =
  (x + y) % q

inline_for_extraction
let (+%) #q = modular_add #q

inline_for_extraction
val modular_add_lemma:
  #q:nat
  -> x:field q
  -> y:field q
  -> Lemma (ensures (modular_add x y = (x + y) % q))
  [SMTPat (modular_add x y)]

let modular_add_lemma #q x y = ()

(**modular_substraction *)

inline_for_extraction
val modular_sub:
  #q:nat
  -> x:field q
  -> y:field q
  -> Tot (z:field q)

let modular_sub #q x y =
  (x +(q - y)) % q

inline_for_extraction
let (-%) #q = modular_sub #q

inline_for_extraction
val modular_sub_lemma:
  #q:nat
  -> x:field q
  -> y:field q
  -> Lemma (ensures (modular_sub x y = (x - y) % q))
 [SMTPat (modular_sub x y)]

let modular_sub_lemma #q x y = ()

(** modular_multiplication *)

inline_for_extraction
val modular_mul:
  #q:nat
  -> x:field q
  -> y:field q
  -> Tot (z:field q)

let modular_mul #q x y =
  (x * y) % q

inline_for_extraction
let ( *% ) #q = modular_mul #q


inline_for_extraction
val modular_mul_lemma:
  #q:nat
  -> x:field q
  -> y:field q
  -> Lemma (ensures (modular_mul x y = (x * y) % q))
  [SMTPat (modular_mul x y)]

let modular_mul_lemma #q x y = ()


(** modular_exponentiation *)


inline_for_extraction
val modular_exp:
  #q:nat{q>1}
  -> x:field q
  -> n:nat
  -> Tot (z:field q) (decreases n)

let rec modular_exp # q x n =
  if n=0 then 1 else x *% (modular_exp x (n-1))

let (^%) #q = modular_exp #q

val extended_gcd: x:pos -> y:nat -> Tot (res:(int & int & pos){let (u, v, g) = res in u * x + v * y = g}) (decreases y)

let rec extended_gcd x y =
  if y = 0 then (1,0,x)
  else
    let q = x / y in
    let (u, v, g) = extended_gcd y (x - q * y) in
    (v, u - q * v, g)

val gcd: x:pos -> y:nat -> Tot (g:pos)

let gcd x y = let (_,_,g) = extended_gcd x y in g
#reset-options "--z3rlimit 200 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"


val is_invertible: #q:nat{q>1} -> x:field q -> Type0

let is_invertible #q x =
  exists (y:field q). x *% y = 1

#reset-options "--z3rlimit 300 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

val is_prime: q:nat{q>1} -> Type0

let is_prime q = forall (p:field q{p>0}). (q % p = 0 ==> p = 1)
