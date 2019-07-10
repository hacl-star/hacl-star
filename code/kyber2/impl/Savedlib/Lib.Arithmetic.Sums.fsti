module Lib.Arithmetic.Sums

open FStar.Math.Lemmas
open FStar.Mul


open Lib.IntTypes
open Lib.Sequence
//open Lib.ModularArithmetic.Lemmas
//open Lib.ModularArithmetic
open Lib.Arithmetic.Ring


open FStar.Tactics.Typeclasses

module Seq = Lib.Sequence
module Loops = Lib.LoopCombinators

inline_for_extraction
val sum_n:
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat 
  -> l:lseq a n 
  -> Tot (s:a) (decreases n) 


inline_for_extraction 
val sum_n_mul_distrib_l_lemma:
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat
  -> l:lseq a n
  -> k:a
  -> Lemma (ensures mul k (sum_n l) == sum_n (Seq.map (fun x -> mul k x) l))
	  (decreases n)

inline_for_extraction 
val sum_n_mul_distrib_r_lemma: 
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat
  -> l:lseq a n
  -> k:a
  -> Lemma (ensures mul (sum_n l) k == sum_n (Seq.map (fun x -> mul x k) l)) 
	  (decreases n)

val sum_n_all_zero:
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat
  -> l:lseq a n{forall (k:nat{k<n}). l.[k] == r.zero} 
  -> Lemma (ensures (sum_n l == r.zero)) 
	  (decreases n)

val sum_n_one_non_zero_coeff:
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat
  -> k:nat{k<n}
  -> l:lseq a n{forall (d:nat{d<n}). d <> k ==> l.[d] == r.zero} 
  -> Lemma (ensures sum_n l == l.[k]) (decreases k)

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
  -> Lemma (ensures (let s1 = Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) l2)) l1 in let s2 = Seq.map (fun y -> modular_sum_n (Seq.map (fun x -> f x y) l1)) l2 in modular_sum_n s1 = modular_sum_n s2)) 
	  (decreases n2)
