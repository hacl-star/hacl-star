module Lib.Arithmetic.Sums

open Lib.IntTypes
open Lib.Sequence

open Lib.Arithmetic.Group
open Lib.Arithmetic.Ring

open FStar.Mul
open Spec.Powtwo.Lemmas

open FStar.Tactics.Typeclasses

module Seq = Lib.Sequence
module Loops = Lib.LoopCombinators

#reset-options "--z3rlimit 200 --max_fuel 1 --max_ifuel 1"

val br: i:size_nat -> x:nat{x<pow2 i} -> y:nat{y<pow2 i}

val br_lemma_rec: i:size_nat{i < max_size_t} -> x:nat{x<pow2 i} ->
  Lemma (br (i+1) x = 2 * br i x)

val br_lemma_rec_p: i:size_nat -> p:nat{i+p <= max_size_t} -> x:nat{x<pow2 i} ->
  Lemma (ensures x < pow2 (i+p) /\ br (i+p) x = (pow2 p) * br i x) (decreases p)

val br_lemma_zero: i:size_nat -> Lemma (ensures br i 0 = 0) (decreases i)

val br_lemma_one: (i:size_nat{i>0}) -> Lemma (ensures br i 1 = pow2 (i-1)) (decreases i)

val br_lemma_n2_1: i:size_nat{i < max_size_t} -> x:nat{x<pow2 i} ->
  Lemma (br (i+1) (x+pow2 i) == (br (i+1) x) + 1)

#reset-options "--z3rlimit 200 --max_fuel 1 --max_ifuel 1"

val br_involutive: i:size_nat -> x:nat{x<pow2 i} -> Lemma (br i (br i x) = x)

val br_lemma_n2_2: i:size_nat{i < max_size_t} -> x:nat{x < pow2 (i+1) /\ x%2 = 0} ->
  Lemma (br (i+1) (x+1) == (br (i+1) x) + pow2 i)

val br_lemma_mul: i:size_nat{i>0} -> x:nat{x < pow2 (i-1)} ->
  Lemma (br i x == (2 * br i (2*x)) % pow2 i)

val br_lemma_div: i:size_nat{i>0} -> x:nat{x < pow2 i} ->
  Lemma (br i (x/2) == (2 * br i x) % pow2 i)


val reorg: #a:Type0 -> #n:size_nat -> i:size_nat{n = pow2 i} -> p:lseq a n -> lseq a n

val reorg_lemma: #a:Type0 -> #n:size_nat -> i:size_nat{n = pow2 i} -> p:lseq a n -> k:size_nat{k<n} -> Lemma ((reorg i p).[k] == p.[br i k] /\ (reorg i p).[br i k] == p.[k])

val reorg_involutive: #a:Type0 -> #n:size_nat -> i:size_nat{n = pow2 i} -> p:lseq a n -> Lemma (reorg i (reorg i p) == p)

val split_seq:
   #a:Type0
   -> #n:size_nat{n%2=0}
   -> p:lseq a n
   -> Tot (p':((lseq a (n / 2)) & (lseq a (n / 2))){let (peven,podd)=p' in forall(k:nat{k < n / 2}). peven.[k] == p.[2*k] /\ podd.[k] == p.[2*k+1]})

val join_seq:
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat{n%2=0}
  -> peven:lseq a (n/2)
  -> podd:lseq a (n/2)
  -> p:lseq a n{forall(k:nat{k<n/2}). p.[2*k] == peven.[k] /\ p.[2*k+1] == podd.[k]}


val lemma_split_join:
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat{n%2=0}
  -> p:lseq a n
  -> Lemma (let peven,podd = split_seq p in join_seq peven podd == p)


val lemma_join_split:
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat{n%2=0}
  -> p1:lseq a (n/2)
  -> p2:lseq a (n/2)
  -> Lemma (let peven,podd = split_seq (join_seq p1 p2) in peven == p1 /\ podd == p2)

#reset-options "--z3rlimit 1000 --max_fuel 2 --max_ifuel 2 "

val recursive_split_seq:
   #a:Type0
   -> #n:size_nat
   -> p:lseq a n
   -> i:size_nat
   -> pow:size_nat{pow = pow2 i}
   -> Ghost (lseq (lseq a (n/pow)) pow) (requires n % pow == 0) (ensures fun p' -> forall (k:nat{k<n}). (k/pow < n/pow) /\ index #a #(n/pow) (p'.[br i (k % pow)]) (k/pow) == p.[k]) (decreases i)

val recursive_split_seq_step_lemma:
  #a:Type0
  -> #n:size_nat
  -> i:size_nat{i < max_size_t}
  -> pow:size_nat{pow = pow2 i /\ 2 * pow = pow2 (i+1) /\ n % pow == 0 /\ n % (2 * pow) = 0 /\ (n / (2*pow) == (n/pow)/2) /\ 2 * pow <= max_size_t}
  -> p:lseq a n
  -> p1:lseq (lseq a (n/pow)) pow
  -> p2:lseq (lseq a (n/(2*pow))) (2*pow)
  -> k:size_nat{k<pow}
  -> Lemma (requires p1 == recursive_split_seq p i pow /\ p2 == recursive_split_seq p (i+1) (2*pow)) (ensures (let l1:lseq a ((n/pow)/2) = p2.[br (i+1) k] in let l2 = p2.[br (i+1) (k + pow)] in (l1, l2) == split_seq (p1.[br i k])))

val recursive_split_seq_base_lemma:
  #a:Type0
  -> #n:size_nat{n % 2 == 0}
  -> p:lseq a n
  -> p':lseq (lseq a (n/2)) 2
  -> Lemma (requires p' == recursive_split_seq p 1 2) (ensures (let l1:lseq a (n/2) = p'.[0] in let l2 = p'.[1] in (l1,l2) == split_seq p))

#reset-options "--z3rlimit 500 --max_fuel 0 --max_ifuel 0"

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

val sum_n_simple_lemma2:
  #a:Type0
  -> #[FStar.Tactics.Typeclasses.tcresolve ()] r:monoid a
  -> #n:size_nat{n>=1}
  -> l:lseq a n
  -> Lemma (ensures sum_n l == op (sum_n (Seq.sub l 0 (n-1))) (l.[n-1]))
	  (decreases n)


val sum_n_simple_lemma1:
  #a:Type0
  -> #[FStar.Tactics.Typeclasses.tcresolve ()] r:monoid a
  -> #n:size_nat{n>=1}
  -> l:lseq a n
  -> Lemma (ensures sum_n l == op l.[0] (sum_n (Seq.sub l 1 (n-1))))
	  (decreases n)

val sum_n_split_lemma:
  #a:Type0
  -> #[FStar.Tactics.Typeclasses.tcresolve ()] r:ring a
  -> #n:size_nat{n%2 = 0}
  -> l:lseq a n
  -> leven:lseq a (n/2)
  -> lodd:lseq a (n/2)
  -> Lemma (requires (leven,lodd) == split_seq l) (ensures sum_n #a #add_ag.g.m l == plus (sum_n #a #add_ag.g.m leven) (sum_n #a #add_ag.g.m lodd))
	  (decreases n)

val sum_n_mul_distrib_l_lemma:
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat
  -> l:lseq a n
  -> k:a
  -> Lemma (ensures mul k (sum_n #a #add_ag.g.m l) == sum_n #a #add_ag.g.m (Seq.map (fun x -> mul k x) l))
	  (decreases n)

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
  -> Lemma (*(requires (let m = add_ag.g.m in s1 == Seq.map (fun x -> sum_n (Seq.map (fun y -> f x y) l2)) l1 /\ s2 == Seq.map (fun y -> sum_n (Seq.map (fun x -> f x y) l1)) l2))*) (ensures (let m = bm #c in let s1 = Seq.map (fun x -> sum_n (Seq.map (fun y -> f x y) l2)) l1 in let s2 = Seq.map (fun y -> sum_n (Seq.map (fun x -> f x y) l1)) l2 in sum_n s1 == sum_n s2))
	  (decreases n2)

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
  -> Lemma (*(requires (let m = add_ag.g.m in s1 == Seq.map (fun x -> sum_n (Seq.map (fun y -> f x y) l2)) l1 /\ s2 == Seq.map (fun y -> sum_n (Seq.map (fun x -> f x y) l1)) l2))*) (ensures (let m = (add_ag #c).g.m in let s1 = Seq.map (fun x -> sum_n (Seq.map (fun y -> f x y) l2)) l1 in let s2 = Seq.map (fun y -> sum_n (Seq.map (fun x -> f x y) l1)) l2 in sum_n s1 == sum_n s2))
	  (decreases n2)
