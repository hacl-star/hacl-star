module Lib.ModularArithmetic.Lemmas

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open FStar.Mul
open FStar.Math.Lemmas
open FStar.Classical
open FStar.Tactics

open Lib.ModularArithmetic

module Seq = Lib.Sequence
module Loops = Lib.LoopCombinators


type set n q = p:lseq (field q) n

inline_for_extraction
val modular_add_associativity_lemma: 
  #q:nat
  -> x:field q
  -> y:field q
  -> z:field q
  -> Lemma (ensures modular_add (modular_add x y) z = modular_add x (modular_add y z)) 
  (*[SMTPat (modular_add x (modular_add y z))]*)

inline_for_extraction
val modular_add_swap_lemma:
  #q:nat
  -> x:field q
  -> y:field q
  -> Lemma (ensures modular_add x y = modular_add y x)
  
inline_for_extraction
val modular_mul_one_lemma: #q:nat{q>1} -> x:field q -> Lemma (ensures (modular_mul 1 x = x))

inline_for_extraction
val modular_mul_associativity_lemma: 
  #q:nat 
  -> x:field q 
  -> y:field q 
  -> z:field q 
  -> Lemma (ensures modular_mul (modular_mul x y) z = modular_mul x (modular_mul y z)) 
  (*[SMTPat (modular_mul x (modular_mul y z))]*)

inline_for_extraction
val modular_mul_swap_lemma:
  #q:nat
  -> x:field q
  -> y:field q
  -> Lemma (ensures modular_mul x y = modular_mul y x)

inline_for_extraction
val modular_mul_add_distrib_lemma: 
  #q:nat 
  -> x:field q 
  -> y:field q 
  -> z:field q 
  -> Lemma ((x+%y)*%z = x*%z +% y*%z)

inline_for_extraction
val modular_mul_add_distrib_left_lemma: 
  #q:nat 
  -> x:field q 
  -> y:field q 
  -> z:field q 
  -> Lemma (x*%(y+%z) = x*%y +% x*%z)

val modular_exp_lemma_zero: 
  #q:nat{q>1} 
  -> x:field q 
  -> Lemma (ensures modular_exp x 0 = 1)

inline_for_extraction
val modular_exp_lemma_expand: 
  #q:nat{q>1} 
  -> x:field q 
  -> y:field q 
  -> n:nat 
  -> Lemma (ensures modular_exp (x *% y) n = (modular_exp x n) *% (modular_exp y n)) (decreases n)
  (*[SMTPat (modular_exp (x*%y) n)]*)

val modular_exp_morphism_lemma: 
  #q:nat{q>1}
  -> x:field q
  -> n:nat 
  -> m:nat 
  -> Lemma (ensures modular_exp x (n+m) = modular_mul (modular_exp x n) (modular_exp x m)) 
	  (decreases m)

inline_for_extraction
val modular_exp_lemma_one1: 
  #q:nat{q>1} 
  -> x:field q 
  -> Lemma (ensures ((modular_exp x 1) = x))

inline_for_extraction
val modular_exp_lemma_one2: 
  #q:nat{q>1}
  -> n:nat 
  -> Lemma (ensures ((modular_exp #q 1 n) = 1)) 
	  (decreases n)

inline_for_extraction
val modular_exp_lemma_inv: 
  #q:nat{q>1} 
  -> x:field q 
  -> y:field q{x*%y = 1} 
  -> n:nat 
  -> Lemma (ensures ((modular_exp x n) *% (modular_exp y n) = 1)) 
  [SMTPat ((modular_exp x n) *% (modular_exp y n))]

val modular_exp_exp_lemma: 
  #q:nat{q>1} 
  -> x:field q 
  -> n:nat 
  -> m:nat 
  -> Lemma (ensures modular_exp x (n*m) = modular_exp (modular_exp x n) m)
	  (decreases m)


inline_for_extraction
val modular_sum_n: 
  #n:size_nat 
  -> #q:pos 
  -> l:set n q 
  -> Tot (s:field q) (decreases n) 


inline_for_extraction 
val modular_sum_n_mult_distrib_l_lemma: 
  #n:size_nat 
  -> #q:nat 
  -> l:set n q
  -> k:field q
  -> Lemma (ensures k *% modular_sum_n l = modular_sum_n (Seq.map (fun x -> k*%x) l))
	  (decreases n)

inline_for_extraction 
val modular_sum_n_mult_distrib_r_lemma: 
  #n:size_nat 
  -> #q:nat 
  -> l:set n q
  -> k:field q
  -> Lemma (ensures (modular_sum_n l) *% k = modular_sum_n (Seq.map (fun x -> x *% k) l)) 
	  (decreases n)

val modular_sum_n_all_zero:
  #n:size_nat 
  -> #q:nat{q>0}
  -> l:set n q{forall (k:nat{k<n}). l.[k] = 0} 
  -> Lemma (ensures (modular_sum_n l = 0)) 
	  (decreases n)


val modular_sum_n_one_non_zero_coeff:
  #n:size_nat{n>=0} 
  -> #q:nat{q>0} 
  -> k:nat{k<n}
  -> l:set n q{forall (d:nat{d<n}). d <> k ==> l.[d] = 0} 
  -> Lemma (ensures modular_sum_n l = l.[k]) (decreases k)

val modular_sum_n_all_1_is_n_mod_q: 
  #n:size_nat{n>=0} 
  -> #q:nat{q > 1} 
  -> l:set n q{forall(d:nat{d<n}). l.[d] = 1} 
  -> Lemma (ensures modular_sum_n l = (n % q)) (decreases n)

inline_for_extraction
val modular_fubini_lemma: 
  #n1:size_nat 
  -> #n2:size_nat 
  -> #q1:nat 
  -> #q2:nat 
  -> #q3:pos
  -> f: (field q1 -> field q2 -> field q3) 
  -> l1: set n1 q1 
  -> l2: set n2 q2 
  -> s1: set n1 q3 
  -> s2: set n2 q3 
  -> Lemma (requires s1 == Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) l2)) l1 /\ s2 == Seq.map (fun y -> modular_sum_n (Seq.map (fun x -> f x y) l1)) l2) 
	  (ensures modular_sum_n s1 = modular_sum_n s2) 
	  (decreases n2)

val gcd_lemma: 
  x:pos 
  -> y:nat 
  -> p:pos{x % p = 0 /\ y % p = 0} 
  -> Lemma (ensures (gcd x y) % p = 0) 
  (decreases y)

val gcd_lemma2: 
  x:pos 
  -> y:nat 
  -> Lemma (ensures (let g = gcd x y in x % g = 0 /\ y % g = 0))
	  (decreases y)

val gcd_lemma3: x:pos -> y:nat -> u:int -> v:int -> w:pos{x*u + y*v = w} -> Lemma (ensures (let g = gcd x y in w % g = 0))

val gcd_lemma_invertible: #q:nat{q>1} -> x:field q -> Lemma (gcd q x = 1 <==> is_invertible x)

val lemma_invertible_witness: #q:nat{q>1} -> x:field q -> y:field q {x *% y = 1} -> Lemma (is_invertible x)

val invert_mod: #q:nat{q>1} -> x:field q{is_invertible x} -> y:field q{x *% y = 1}

val lemma_invert_unicity: #q:nat{q>1} -> x:field q -> y:field q{x *% y = 1} -> Lemma (y = invert_mod x)

val lemma_q_prime_zq_field: q:nat{q>1} -> Lemma (is_prime q <==> (forall (x:field q{x>0}). is_invertible x))
