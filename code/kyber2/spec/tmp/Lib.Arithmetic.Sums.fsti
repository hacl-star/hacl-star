module Lib.Arithmetic.Sums

open Lib.IntTypes
open Lib.Sequence

open Lib.Arithmetic.Group
open Lib.Arithmetic.Ring


open FStar.Tactics.Typeclasses

module Seq = Lib.Sequence
module Loops = Lib.LoopCombinators

inline_for_extraction
val sum_n:
  #a:Type0
  -> #[tcresolve ()] m: monoid a
  -> #n:size_nat 
  -> l:lseq a n 
  -> Tot (s:a) (decreases n) 

val sum_n_zero_elements_is_id:
  #a:Type0
  -> #[tcresolve ()] m: monoid a
  -> p:lseq a 0
  -> Lemma (ensures sum_n p == id)

inline_for_extraction
val sum_n_simple_lemma1: 
  #a:Type0
  -> #[FStar.Tactics.Typeclasses.tcresolve ()] r:monoid a
  -> #n:size_nat{n>=1}
  -> l:lseq a n 
  -> Lemma (ensures sum_n l == op l.[0] (sum_n (sub l 1 (n-1))))
	  (decreases n)

inline_for_extraction
val sum_n_simple_lemma2: 
  #a:Type0
  -> #[FStar.Tactics.Typeclasses.tcresolve ()] r:monoid a
  -> #n:size_nat{n>=1}
  -> l:lseq a n 
  -> Lemma (ensures sum_n l == op (sum_n (sub l 0 (n-1))) (l.[n-1])) 
	  (decreases n)

inline_for_extraction 
val sum_n_mul_distrib_l_lemma:
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat
  -> l:lseq a n
  -> k:a
  -> Lemma (ensures mul k (sum_n #a #add_ag.g.m l) == sum_n #a #add_ag.g.m (Seq.map (fun x -> mul k x) l))
	  (decreases n)

inline_for_extraction 
val sum_n_mul_distrib_r_lemma: 
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat
  -> l:lseq a n
  -> k:a
  -> Lemma (ensures mul (sum_n #a #add_ag.g.m l) k == sum_n #a #add_ag.g.m (Seq.map (fun x -> mul x k) l)) 
	  (decreases n)

val sum_n_all_id:
  #a:Type0
  -> #[tcresolve ()] m:monoid a
  -> #n:size_nat
  -> l:lseq a n{forall (k:nat{k<n}). l.[k] == id #a} 
  -> Lemma (ensures (sum_n l == id #a)) 
	  (decreases n)

val sum_n_one_non_id_coeff:
  #a:Type0
  -> #[tcresolve ()] m:monoid a
  -> #n:size_nat
  -> k:nat{k<n}
  -> l:lseq a n{forall (d:nat{d<n}). d <> k ==> l.[d] == id #a} 
  -> Lemma (ensures sum_n l == l.[k]) (decreases k)

val sum_n_all_c_is_repeat_c_n:
  #a:Type0
  -> #[tcresolve ()] m:monoid a
  -> #n:size_nat{n>=0} 
  -> c:a
  -> l:lseq a n{forall(d:nat{d<n}). l.[d] == c} 
  -> Lemma (ensures sum_n l == repeat_op c n) (decreases n)

inline_for_extraction
val sum_n_fubini: 
  #a:Type0
  -> #b:Type0
  -> #c:Type0
  -> #[tcresolve ()] cm: commutative_monoid c
  -> #n1:size_nat 
  -> #n2:size_nat 
  -> f: (a -> b -> c) 
  -> l1: lseq a n1 
  -> l2: lseq b n2 
  //-> s1: lseq c n1
  //-> s2: lseq c n2
  -> Lemma (*(requires (let m = add_ag.g.m in s1 == Seq.map (fun x -> sum_n (Seq.map (fun y -> f x y) l2)) l1 /\ s2 == Seq.map (fun y -> sum_n (Seq.map (fun x -> f x y) l1)) l2))*) (ensures (let m = bm in let s1 = Seq.map (fun x -> sum_n (Seq.map (fun y -> f x y) l2)) l1 in let s2 = Seq.map (fun y -> sum_n (Seq.map (fun x -> f x y) l1)) l2 in sum_n s1 == sum_n s2)) 
	  (decreases n2)

inline_for_extraction
val sum_n_fubini_ring: 
  #a:Type0
  -> #b:Type0
  -> #c:Type0
  -> #[tcresolve ()] r: ring c
  -> #n1:size_nat 
  -> #n2:size_nat 
  -> f: (a -> b -> c) 
  -> l1: lseq a n1 
  -> l2: lseq b n2 
  //-> s1: lseq c n1
  //-> s2: lseq c n2
  -> Lemma (*(requires (let m = add_ag.g.m in s1 == Seq.map (fun x -> sum_n (Seq.map (fun y -> f x y) l2)) l1 /\ s2 == Seq.map (fun y -> sum_n (Seq.map (fun x -> f x y) l1)) l2))*) (ensures (let m = add_ag.g.m in let s1 = Seq.map (fun x -> sum_n (Seq.map (fun y -> f x y) l2)) l1 in let s2 = Seq.map (fun y -> sum_n (Seq.map (fun x -> f x y) l1)) l2 in sum_n s1 == sum_n s2)) 
	  (decreases n2)
