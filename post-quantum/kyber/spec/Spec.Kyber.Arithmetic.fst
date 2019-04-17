module Spec.Kyber.Arithmetic

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open FStar.Mul
open FStar.Math.Lemmas
open FStar.Classical
open FStar.Tactics

open Spec.Kyber.Params
open Spec.Kyber.Lemmas
open Spec.Powtwo.Lemmas

module Seq = Lib.Sequence
module Loops = Lib.LoopCombinators


#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"


type field q = x:nat{x<q}
type set n q = p:lseq (field q) n

inline_for_extraction
val modular_add: #q:nat -> x:field q -> y:field q -> z:field q

let modular_add #q x y =
  (x + y) % q

inline_for_extraction
let (+%) #q = modular_add #q

inline_for_extraction
val modular_add_lemma: #q:nat -> x:field q-> y:field q-> Lemma (ensures (modular_add x y = (x + y) % q))
  [SMTPat (modular_add x y)]

let modular_add_lemma #q x y = ()

inline_for_extraction
val modular_add_associativity_lemma: #q:nat -> x:field q -> y:field q -> z:field q -> Lemma (ensures modular_add (modular_add x y) z = modular_add x (modular_add y z)) (*[SMTPat (modular_add x (modular_add y z))]*)

let modular_add_associativity_lemma #q x y z =
  lemma_mod_add_distr z (x+y) q;
  lemma_mod_add_distr x (y+z) q


inline_for_extraction
val modular_sub: #q:nat -> x:field q -> y:field q -> z:field q

let modular_sub #q x y =
  (x +(q - y)) % q


inline_for_extraction
let (-%) #q = modular_sub #q

inline_for_extraction
val modular_sub_lemma: #q:nat -> x:field q -> y:field q -> Lemma (ensures (modular_sub x y = (x - y) % q))
 [SMTPat (modular_sub x y)]

let modular_sub_lemma #q x y = ()

inline_for_extraction
val modular_mul: #q:nat -> x:field q -> y:field q -> z:field q

let modular_mul #q x y =
  (x * y) % q

inline_for_extraction
let ( *% ) #q = modular_mul #q

inline_for_extraction
val modular_mul_lemma: #q:nat -> x:field q -> y:field q-> Lemma (ensures (modular_mul x y = (x * y) % q))
  [SMTPat (modular_mul x y)]

let modular_mul_lemma #q x y = ()

inline_for_extraction
val modular_mul_one_lemma: #q:nat{q>1} -> x:field q -> Lemma (ensures (modular_mul 1 x = x))

let modular_mul_one_lemma #q x = ()
#reset-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

inline_for_extraction
val modular_mul_associativity_lemma: #q:nat -> x:field q -> y:field q -> z:field q -> Lemma (ensures modular_mul (modular_mul x y) z = modular_mul x (modular_mul y z)) (*[SMTPat (modular_mul x (modular_mul y z))]*)

let modular_mul_associativity_lemma #q x y z =
  lemma_mod_mul_distr_l (x*y) z q;
  paren_mul_right x y z;
  lemma_mod_mul_distr_r x (y*z) q

inline_for_extraction
val modular_mul_add_distrib_lemma: #q:nat -> x:field q -> y:field q -> z:field q -> Lemma ((x+%y)*%z = x*%z +% y*%z)

let modular_mul_add_distrib_lemma #q x y z =
  calc (==) {
    (x+%y)*%z;
      = {lemma_mod_mul_distr_l (x+y) z q}
    ((x+y)*z) % q;
      = {distributivity_add_left x y z; ()}
    (x*z + y*z) % q;
      = {lemma_mod_add_distr (x*z) (y*z) q; lemma_mod_add_distr (y*%z) (x*z) q}
    ((x*z) %q) +% ((y*z)%q);
    }


inline_for_extraction
val modular_exp: #q:nat{q>1} -> x:field q-> n:nat -> Tot (z:field q) (decreases n)

let rec modular_exp # q x n =
  if n=0 then 1 else x *% (modular_exp x (n-1))

let (^%) #q = modular_exp #q


#reset-options "--z3rlimit 200 --max_fuel 2 --max_ifuel 2 --using_facts_from '* -FStar.Seq'"

inline_for_extraction
val modular_exp_lemma_expand: #q:nat{q>1} -> x:field q -> y:field q -> n:nat -> Lemma (ensures modular_exp (x *% y) n = (modular_exp x n) *% (modular_exp y n)) (decreases n) (*[SMTPat (modular_exp (x*%y) n)]
*)

val modular_exp_lemma_zero: #q:nat{q>1} -> x:field q -> Lemma (ensures modular_exp x 0 = 1)

let modular_exp_lemma_zero #q x = 
  assert_norm(modular_exp x 0 = 1)

let rec modular_exp_lemma_expand #q x y n = 
  if n = 0 then
    ()
  else
    (modular_exp_lemma_expand x y (n-1);
     assert((x *% y) ^% n = (x *% y) *% ((x *% y) ^% (n-1)));
     assert(x ^% n = x *% (x ^% (n-1)));
     assert(y ^% n = y *% (y ^% (n-1)));
     calc (==) {
       (x *% y) ^% n;
	 = {}
	(x *% y) *% ((x ^% (n-1)) *% (y ^% (n-1)));
	= {modular_mul_associativity_lemma (x *% y) (x ^% (n-1)) (y ^% (n-1))}
	((x *% y) *% (x ^% (n-1))) *% (y ^% (n-1));
	= {modular_mul_associativity_lemma y x (x ^% (n-1)); ()}
	((x *% (x ^% (n-1))) *% y) *% (y ^% (n-1));
	= {modular_mul_associativity_lemma (x *% (x ^% (n-1))) y (y ^% (n-1))}
	(x *% (x ^% (n-1))) *% (y *% (y ^% (n-1)));
	})


#reset-options "--z3rlimit 200 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

val modular_exp_morphism_lemma: #q:nat{q>1} -> x:field q -> n:nat -> m:nat -> Lemma (ensures modular_exp x (n+m) = modular_mul (modular_exp x n) (modular_exp x m)) (decreases m)

let rec modular_exp_morphism_lemma #q x n m =
  if (m=0) then ()
  else (
    calc (==) {
      x ^% (n+m);
      = {}
      x ^% ((n+1)+(m-1));
      = {modular_exp_morphism_lemma #q x (n+1) (m-1)}
      (x ^% (n+1)) *% (x ^% (m-1));
      = {}
      (x *% (x ^% n)) *% (x ^% (m-1));
      = {modular_mul_associativity_lemma (x^%n) x (x^%(m-1)); ()}
      (x ^% n) *% (x *% (x ^% (m-1)));
      = {assert( x ^% m = x *% (x^% (m-1))); ()}
      (x ^% n) *% (x ^% m);
    })


#reset-options "--z3rlimit 200 --max_fuel 2 --max_ifuel 2 --using_facts_from '* -FStar.Seq'"    

inline_for_extraction
val modular_exp_lemma_one1: #q:nat{q>1} -> x:field q -> Lemma (ensures ((modular_exp x 1) = x))

let modular_exp_lemma_one1 #q x = 
  assert(x *% 1 = x);
  assert(modular_exp x 1 = x *% modular_exp #q x 0);
  modular_exp_lemma_zero #q x;
  assert( x *% modular_exp x 0 = x *% 1);
  assert(modular_exp #q x 1 = x)

inline_for_extraction
val modular_exp_lemma_one2: #q:nat{q>1} -> n:nat -> Lemma (ensures ((modular_exp #q 1 n) = 1)) (decreases n)

let rec modular_exp_lemma_one2 #q n = 
  if n=0 then modular_exp_lemma_zero #q 1
  else(
    modular_exp_lemma_one2 #q (n-1);
  assert(modular_exp #q 1 n = 1 *% modular_exp 1 (n-1));
  assert(modular_exp #q 1 n = modular_mul #q 1 1);
  assert(modular_mul #q 1 1 = 1 % q);
  modulo_lemma 1 q
  )

#reset-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"    

inline_for_extraction
val modular_exp_lemma_inv: #q:nat{q>1} -> x:field q -> y:field q{x*%y = 1} -> n:nat -> Lemma (ensures ((modular_exp x n) *% (modular_exp y n) = 1)) [SMTPat ((modular_exp x n) *% (modular_exp y n))]


let modular_exp_lemma_inv #q x y n = 
  modular_exp_lemma_expand x y n;
  modular_exp_lemma_one2 #q n

#reset-options "--z3rlimit 200 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"    

val modular_exp_exp_lemma: #q:nat{q>1} -> x:field q -> n:nat -> m:nat -> Lemma (ensures modular_exp x (n*m) = modular_exp (modular_exp x n) m) (decreases m)

let rec modular_exp_exp_lemma #q x n m =
  if m = 0 then ()
  else 
    calc (==) {
      x ^% (n*m);
	= {}
      x ^% (n + n*(m-1));
	= {modular_exp_morphism_lemma x n (n*(m-1))}
      (x ^% n) *% (x^% (n*(m-1)));
	= {modular_exp_exp_lemma x n (m-1); ()}
       (x ^% n) *% ((x^% n) ^% (m-1));
	= {}
      modular_exp (x^%n) m;
      }


inline_for_extraction
val modular_sum_n: #n:size_nat -> #q:pos -> l:set n q -> Tot (s:field q) (decreases n) 

let rec modular_sum_n #n #q l =
  if n=0 then 0
  else
  let s=modular_sum_n (sub l 1 (n-1)) in
  l.[0] +% s

 
#reset-options "--z3rlimit 200 --max_fuel 2 --max_ifuel 2 --using_facts_from '* -FStar.Seq'"    

inline_for_extraction
val simpl_seq_sub_sub_lemma: #a:Type -> #len:size_nat -> l:lseq a len -> start1:size_nat -> n1:size_nat{start1+n1<=len} -> start2:size_nat -> n2:size_nat{start2+n2<=n1} -> Lemma(sub (sub l start1 n1) start2 n2 == sub l (start1+start2) n2) 

let simpl_seq_sub_sub_lemma #a #len l start1 n1 start2 n2 =
  let s = sub (sub l start1 n1) start2 n2 in
  assert ((forall (k:nat{k<n2}). index s k == index (sub l start1 n1) (k+start2)));
  assert ((forall (k:nat{k<n2}). index s k == index l (start1+start2+k)));
  eq_intro s (sub l (start1+start2) n2);
  eq_elim s (sub l (start1+start2) n2)

inline_for_extraction
val modular_sum_n_simple_lemma: #n:size_nat{n>=1} -> #q:nat{q>0} -> l:set n q -> Lemma(ensures modular_sum_n l = modular_sum_n (sub l 0 (n-1)) +% l.[n-1]) (decreases n)

let rec modular_sum_n_simple_lemma #n #q l =
  if n = 1 then ()
  else 
    calc (==) {
      modular_sum_n l;
	= {}
      l.[0] +% modular_sum_n (sub l 1 (n-1));
	= {modular_sum_n_simple_lemma (sub l 1 (n-1)); ()}
      l.[0] +% ((modular_sum_n (sub (sub l 1 (n-1)) 0 (n-2))) +% (sub l 1 (n-1)).[n-2]);
	= {simpl_seq_sub_sub_lemma l 1 (n-1) 0 (n-2); assert((sub l 1 (n-1)).[n-2] = l.[n-1]); ()}
      l.[0] +% ((modular_sum_n (sub l 1 (n-2))) +% l.[n-1]);
	= {modular_add_associativity_lemma l.[0] (modular_sum_n (sub l 1 (n-2))) l.[n-1]; ()}
      (l.[0] +% (modular_sum_n (sub l 1 (n-2)))) +% l.[n-1];
	= {simpl_seq_sub_sub_lemma l 0 (n-1) 1 (n-2); ()}
      ((sub l 0 (n-1)).[0] +% (modular_sum_n (sub (sub l 0 (n-1)) 1 (n-2)))) +% l.[n-1]; 
	= {}
      modular_sum_n (sub l 0 (n-1)) +% l.[n-1];
    }

inline_for_extraction
val map_sub_commutativity_lemma: #n:size_nat -> #q1:nat -> #q2:nat -> l:set n q1 -> f:(field q1 -> field q2) -> i:size_nat -> len:size_nat{i+len<=n} ->Lemma (ensures sub (Seq.map f l) i len == Seq.map f (sub l i len))

let rec map_sub_commutativity_lemma #n #q1 #q2 l f i len =
  assert(forall (k:nat{k<len}). (sub (Seq.map f l) i len).[k] = (Seq.map f l).[i+k]);
  assert(forall (k:nat{k<len}). (sub (Seq.map f l) i len).[k] = f l.[i+k]);
  assert(forall (k:nat{k<len}). (sub (Seq.map f l) i len).[k] = f (sub l i len).[k]);
  assert(forall (k:nat{k<len}). f (sub l i len).[k] = (Seq.map f (sub l i len)).[k]);
  eq_intro (sub (Seq.map f l) i len) (Seq.map f (sub l i len));
  eq_elim (sub (Seq.map f l) i len) (Seq.map f (sub l i len))
  

inline_for_extraction 
val modular_sum_n_mult_distrib_l_lemma: #n:size_nat -> #q:nat -> l:set n q-> k:field q-> Lemma (ensures k *% modular_sum_n l = modular_sum_n (Seq.map (fun x -> k*%x) l)) (decreases n)

let rec modular_sum_n_mult_distrib_l_lemma #n #q l k =
  if n=0 then ()
  else 
    calc (==) {
	k *% modular_sum_n l;
	  = {}
	k *% (l.[0] +% modular_sum_n (sub l 1 (n-1)));
	  = {modular_mul_add_distrib_lemma l.[0] (modular_sum_n (sub l 1 (n-1))) k}
	k *% l.[0] +% k *% modular_sum_n (sub l 1 (n-1));
	  = {modular_sum_n_mult_distrib_l_lemma (sub l 1 (n-1)) k; assert ((Seq.map (fun x -> k *% x) l).[0] = k *% l.[0]);()}
	(Seq.map (fun x -> k *% x) l).[0] +% modular_sum_n (Seq.map (fun x -> k *% x) (sub l 1 (n-1)));
          =  {map_sub_commutativity_lemma l (fun x -> k *% x) 1 (n-1); ()}
	(Seq.map (fun x -> k *% x) l).[0] +% (modular_sum_n (sub (Seq.map (fun x -> k *% x) l) 1 (n-1)));
	  = {}
	modular_sum_n (Seq.map (fun x -> k *% x) l);
	}

#reset-options "--z3rlimit 200 --max_fuel 2 --max_ifuel 2 --using_facts_from '* -FStar.Seq'"    


inline_for_extraction 
val modular_sum_n_mult_distrib_r_lemma: #n:size_nat -> #q:nat -> l:set n q-> k:field q-> Lemma (ensures (modular_sum_n l) *% k = modular_sum_n (Seq.map (fun x -> x *% k) l)) (decreases n)

let rec modular_sum_n_mult_distrib_r_lemma #n #q l k =
  if n=0 then ()
  else 
    calc (==) {
	(modular_sum_n l) *% k;
	  = {}
	(l.[0] +% modular_sum_n (sub l 1 (n-1))) *% k;
	  = {modular_mul_add_distrib_lemma l.[0] (modular_sum_n (sub l 1 (n-1))) k}
	l.[0] *% k +% (modular_sum_n (sub l 1 (n-1))) *% k;
	  = {modular_sum_n_mult_distrib_r_lemma (sub l 1 (n-1)) k; assert ((Seq.map (fun x -> k *% x) l).[0] = k *% l.[0]);()}
	(Seq.map (fun x -> x *% k) l).[0] +% modular_sum_n (Seq.map (fun x -> x *% k) (sub l 1 (n-1)));
          =  {map_sub_commutativity_lemma l (fun x -> x *% k) 1 (n-1); ()}
	(Seq.map (fun x -> x *% k) l).[0] +% (modular_sum_n (sub (Seq.map (fun x -> x *% k) l) 1 (n-1)));
	  = {}
	modular_sum_n (Seq.map (fun x -> x *% k) l);
	}


#reset-options "--z3rlimit 200 --max_fuel 2 --max_ifuel 2 --using_facts_from '* -FStar.Seq'"    

val modular_fubini_lemma_: #n1:size_nat -> #n2:size_nat -> #q:nat{q>0} -> l1: set n1 q -> l2: set n2 q -> Lemma (ensures modular_sum_n (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> x *% y) l2)) l1) = modular_sum_n (Seq.map (fun y -> modular_sum_n (Seq.map (fun x -> x *% y) l1)) l2))

let modular_fubini_lemma_ #n1 #n2 #q l1 l2 =
  let s1 = Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> x *% y) l2)) l1 in
  assert(forall (k:nat{k<n1}). s1.[k] = modular_sum_n (Seq.map (fun y -> l1.[k] *% y) l2));
  let customprop1 (k:nat{k<n1}) : GTot Type0 =
    l1.[k] *% modular_sum_n l2 = modular_sum_n (Seq.map (fun y -> l1.[k]*%y) l2)
  in
  let g1 (k:nat{k<n1}) : Lemma (customprop1 k) =
    modular_sum_n_mult_distrib_l_lemma l2 l1.[k]
  in 
  FStar.Classical.forall_intro g1;
  assert(forall (k:nat{k<n1}). s1.[k] = l1.[k] *% modular_sum_n l2);
  eq_intro s1 (Seq.map (fun x -> x *% (modular_sum_n l2)) l1);
  eq_elim s1 (Seq.map (fun x -> x *% (modular_sum_n l2)) l1);
  modular_sum_n_mult_distrib_r_lemma l1 (modular_sum_n l2);
  assert (modular_sum_n s1 = modular_sum_n l1 *% (modular_sum_n l2));
  
  let s2 = Seq.map (fun y -> modular_sum_n (Seq.map (fun x -> x *% y) l1)) l2 in
  let customprop2 (k:nat{k<n2}) : GTot Type0 =
    (modular_sum_n l1) *% l2.[k] = modular_sum_n (Seq.map (fun x -> x *% l2.[k]) l1)
  in
  let g2 (k:nat{k<n2}) : Lemma (customprop2 k) =
    modular_sum_n_mult_distrib_r_lemma l1 l2.[k]
  in
  FStar.Classical.forall_intro g2;
  eq_intro s2 (Seq.map (fun y -> (modular_sum_n l1) *% y) l2);
  eq_elim s2 (Seq.map (fun y -> (modular_sum_n l1) *% y) l2);
  modular_sum_n_mult_distrib_l_lemma l2 (modular_sum_n l1);
  assert (modular_sum_n s2 = modular_sum_n l1 *% (modular_sum_n l2))


#reset-options "--z3rlimit 200 --max_fuel 2 --max_ifuel 2 --using_facts_from '* -FStar.Seq'"    

val dummy_modular_fubini_sublemma: #n:size_nat{n>0} -> #q1:nat -> #q2:nat -> g:(field q1 -> field q2) -> l:set n q1 -> Lemma((Seq.map g l).[0] = g l.[0])

let dummy_modular_fubini_sublemma #n #q1 #q2 g l = 
  ()
 
#reset-options "--z3rlimit 200 --max_fuel 2 --max_ifuel 2 --using_facts_from '* -FStar.Seq'"    

val modular_fubini_sublemma0: #n1:size_nat{n1>0} -> #n2:size_nat{n2>0} -> #q1:nat -> #q2:nat -> #q3:pos -> f: (field q1 -> field q2 -> field q3) -> l1: set n1 q1 -> l2: set n2 q2 -> Lemma(ensures (modular_sum_n (Seq.map (fun y -> f l1.[0] y) l2)) +% (modular_sum_n (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) (sub l1 1 (n1-1))) +% modular_sum_n (Seq.map (fun x -> f x l2.[0]) (sub l1 1 (n1-1)))) = (modular_sum_n (Seq.map (fun y -> f l1.[0] y) (sub l2 1 (n2-1))) +% modular_sum_n (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) (sub l1 1 (n1-1)))) +% (f l1.[0] l2.[0] +% modular_sum_n (Seq.map (fun x -> f x l2.[0]) (sub l1 1 (n1-1))))) 

let modular_fubini_sublemma0 #n1 #n2 #q1 #q2 #q3 f l1 l2 = 
  calc (==) {
    (modular_sum_n (Seq.map (fun y -> f l1.[0] y) l2)) +% (modular_sum_n (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) (sub l1 1 (n1-1))) +% modular_sum_n (Seq.map (fun x -> f x l2.[0]) (sub l1 1 (n1-1))));
    = {}
       ((Seq.map (fun y -> f l1.[0] y) l2).[0] +% modular_sum_n (sub (Seq.map (fun y -> f l1.[0] y) l2) 1 (n2-1))) +% (modular_sum_n (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) (sub l1 1 (n1-1))) +% modular_sum_n (Seq.map (fun x -> f x l2.[0]) (sub l1 1 (n1-1))));
       = {dummy_modular_fubini_sublemma (fun y -> f l1.[0] y) l2; ()}
       f l1.[0] l2.[0] +% modular_sum_n (sub (Seq.map (fun y -> f l1.[0] y) l2) 1 (n2-1)) +% (modular_sum_n (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) (sub l1 1 (n1-1))) +% modular_sum_n (Seq.map (fun x -> f x l2.[0]) (sub l1 1 (n1-1))));
       = {modular_add_associativity_lemma (modular_sum_n (sub (Seq.map (fun y -> f l1.[0] y) l2) 1 (n2-1))) (f l1.[0] l2.[0]) (modular_sum_n (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) (sub l1 1 (n1-1))) +% modular_sum_n (Seq.map (fun x -> f x l2.[0]) (sub l1 1 (n1-1))));
	 modular_add_associativity_lemma (f l1.[0] l2.[0]) (modular_sum_n (Seq.map (fun x -> f x l2.[0]) (sub l1 1 (n1-1)))) (modular_sum_n (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) (sub l1 1 (n1-1))));
	 modular_add_associativity_lemma (modular_sum_n (sub (Seq.map (fun y -> f l1.[0] y) l2) 1 (n2-1))) (modular_sum_n (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) (sub l1 1 (n1-1)))) (f l1.[0] l2.[0] +% modular_sum_n (Seq.map (fun x -> f x l2.[0]) (sub l1 1 (n1-1)))); ()}
    (modular_sum_n (sub (Seq.map (fun y -> f l1.[0] y) l2) 1 (n2-1)) +% modular_sum_n (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) (sub l1 1 (n1-1)))) +% (f l1.[0] l2.[0] +% modular_sum_n (Seq.map (fun x -> f x l2.[0]) (sub l1 1 (n1-1))));
      = {map_sub_commutativity_lemma l2 (fun y -> f l1.[0] y) 1 (n2-1); ()}
    (modular_sum_n (Seq.map (fun y -> f l1.[0] y) (sub l2 1 (n2-1))) +% modular_sum_n (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) (sub l1 1 (n1-1)))) +% (f l1.[0] l2.[0] +% modular_sum_n (Seq.map (fun x -> f x l2.[0]) (sub l1 1 (n1-1))));
  }



#reset-options "--z3rlimit 200 --max_fuel 2 --max_ifuel 2 --using_facts_from '* -FStar.Seq'"    


val modular_fubini_sublemma1: #n1:size_nat -> #n2:size_nat{n2>0} -> #q1:nat -> #q2:nat -> #q3:pos -> f: (field q1 -> field q2 -> field q3) -> l1: set n1 q1 -> l2: set n2 q2 -> Lemma(ensures modular_sum_n (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) l2)) l1) = modular_sum_n (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) l1) +% modular_sum_n (Seq.map (fun x -> f x l2.[0]) l1)) (decreases n1)



let rec modular_fubini_sublemma1 #n1 #n2 #q1 #q2 #q3 f l1 l2 (*:
Lemma(ensures modular_sum_n (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) l2)) l1) = modular_sum_n (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) l1) +% modular_sum_n (Seq.map (fun x -> f x l2.[0]) l1)) (decreases n1)
by (tadmit ())*)
=
  let s = modular_sum_n (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) l2)) l1) in
  if n1 = 0 then ()
  else
    begin
    calc (==) {
      s;
	= {}
      (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) l2)) l1).[0] +% modular_sum_n (sub (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) l2)) l1) 1 (n1-1));
	= {map_sub_commutativity_lemma l1 (fun x -> modular_sum_n (Seq.map (fun y -> f x y) l2)) 1 (n1-1); ()}
      (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) l2)) l1).[0] +% modular_sum_n (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) l2)) (sub l1 1 (n1-1)));
	= {modular_fubini_sublemma1 f (sub l1 1 (n1-1)) l2; dummy_modular_fubini_sublemma (fun x -> modular_sum_n (Seq.map (fun y -> f x y) l2)) l1; ()}
      (modular_sum_n (Seq.map (fun y -> f l1.[0] y) l2)) +% (modular_sum_n (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) (sub l1 1 (n1-1))) +% modular_sum_n (Seq.map (fun x -> f x l2.[0]) (sub l1 1 (n1-1))));
       // = {}
       // ((Seq.map (fun y -> f l1.[0] y) l2).[0] +% modular_sum_n (sub (Seq.map (fun y -> f l1.[0] y) l2) 1 (n2-1))) +% (modular_sum_n (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) (sub l1 1 (n1-1))) +% modular_sum_n (Seq.map (fun x -> f x l2.[0]) (sub l1 1 (n1-1))));
    //    = {dummy_modular_fubini_sublemma (fun y -> f l1.[0] y) l2; ()}
    //    f l1.[0] l2.[0] +% modular_sum_n (sub (Seq.map (fun y -> f l1.[0] y) l2) 1 (n2-1)) +% (modular_sum_n (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) (sub l1 1 (n1-1))) +% modular_sum_n (Seq.map (fun x -> f x l2.[0]) (sub l1 1 (n1-1))));
    //    = {modular_add_associativity_lemma (modular_sum_n (sub (Seq.map (fun y -> f l1.[0] y) l2) 1 (n2-1))) (f l1.[0] l2.[0]) (modular_sum_n (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) (sub l1 1 (n1-1))) +% modular_sum_n (Seq.map (fun x -> f x l2.[0]) (sub l1 1 (n1-1))));
    // 	 modular_add_associativity_lemma (f l1.[0] l2.[0]) (modular_sum_n (Seq.map (fun x -> f x l2.[0]) (sub l1 1 (n1-1)))) (modular_sum_n (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) (sub l1 1 (n1-1))));
    // 	 modular_add_associativity_lemma (modular_sum_n (sub (Seq.map (fun y -> f l1.[0] y) l2) 1 (n2-1))) (modular_sum_n (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) (sub l1 1 (n1-1)))) (f l1.[0] l2.[0] +% modular_sum_n (Seq.map (fun x -> f x l2.[0]) (sub l1 1 (n1-1)))); ()}
    // (modular_sum_n (sub (Seq.map (fun y -> f l1.[0] y) l2) 1 (n2-1)) +% modular_sum_n (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) (sub l1 1 (n1-1)))) +% (f l1.[0] l2.[0] +% modular_sum_n (Seq.map (fun x -> f x l2.[0]) (sub l1 1 (n1-1))));
    //   = {map_sub_commutativity_lemma l2 (fun y -> f l1.[0] y) 1 (n2-1); ()}
      = {modular_fubini_sublemma0 f l1 l2} 
     (modular_sum_n (Seq.map (fun y -> f l1.[0] y) (sub l2 1 (n2-1))) +% modular_sum_n (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) (sub l1 1 (n1-1)))) +% (f l1.[0] l2.[0] +% modular_sum_n (Seq.map (fun x -> f x l2.[0]) (sub l1 1 (n1-1))));
    
       = {dummy_modular_fubini_sublemma (fun x -> modular_sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) l1; ()}    
     ((Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) l1).[0] +% modular_sum_n (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) (sub l1 1 (n1-1)))) +% (f l1.[0] l2.[0] +% modular_sum_n (Seq.map (fun x -> f x l2.[0]) (sub l1 1 (n1-1))));
       = {map_sub_commutativity_lemma l1  (fun x -> modular_sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) 1 (n1-1); ()}
    ((Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) l1).[0] +% modular_sum_n (sub (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) l1) 1 (n1-1))) +% (f l1.[0] l2.[0] +% modular_sum_n (Seq.map (fun x -> f x l2.[0]) (sub l1 1 (n1-1))));
     = {}
    modular_sum_n (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) l1) +% (f l1.[0] l2.[0] +% modular_sum_n (Seq.map (fun x -> f x l2.[0]) (sub l1 1 (n1-1))));
      = {dummy_modular_fubini_sublemma (fun x -> f x l2.[0]) l1; ()}
    modular_sum_n (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) l1) +% ((Seq.map (fun x -> f x l2.[0]) l1).[0] +% modular_sum_n (Seq.map (fun x -> f x l2.[0]) (sub l1 1 (n1-1))));
	= {map_sub_commutativity_lemma l1 (fun x -> f x l2.[0]) 1 (n1-1); ()}
    modular_sum_n (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) l1) +% ((Seq.map (fun x -> f x l2.[0]) l1).[0] +% modular_sum_n (sub (Seq.map (fun x -> f x l2.[0]) l1) 1 (n1-1)));
	= {}
       modular_sum_n (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) l1) +% modular_sum_n (Seq.map (fun x -> f x l2.[0]) l1);
     }
     end
     
    
val modular_sum_n_all_zero: #n:size_nat -> #q:nat{q>0} -> l:set n q{forall (k:nat{k<n}). l.[k] = 0} -> Lemma (ensures (modular_sum_n l = 0)) (decreases n)

let rec modular_sum_n_all_zero #n #q l =
  if n = 0 then ()
  else (
    assert(modular_sum_n l = l.[0] +% modular_sum_n (sub l 1 (n-1)));
    modular_sum_n_all_zero (Lib.Sequence.sub l 1 (n-1));
    assert(modular_sum_n l = l.[0] +% 0))


  

#reset-options "--z3rlimit 200 --max_fuel 2 --max_ifuel 2 --using_facts_from '* -FStar.Seq'"    
inline_for_extraction
val modular_fubini_lemma: #n1:size_nat -> #n2:size_nat -> #q1:nat -> #q2:nat -> #q3:pos -> f: (field q1 -> field q2 -> field q3) -> l1: set n1 q1 -> l2: set n2 q2 -> s1: set n1 q3 -> s2: set n2 q3 -> Lemma (requires s1 == Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) l2)) l1 /\ s2 == Seq.map (fun y -> modular_sum_n (Seq.map (fun x -> f x y) l1)) l2) (ensures modular_sum_n s1 = modular_sum_n s2) (decreases n2)

let rec modular_fubini_lemma #n1 #n2 #q1 #q2 #q3 f l1 l2 s1 s2 =
 (* let s1 = Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) l2)) l1 in
  let s2 = Seq.map (fun y -> modular_sum_n (Seq.map (fun x -> f x y) l1)) l2 in*)
  if n2 = 0 then begin
    assert (forall (k:nat{k<n1}). s1.[k] = modular_sum_n (Seq.map (fun y -> f l1.[k] y) l2));
    assert (forall (k:nat{k<n1}). length (Seq.map (fun y -> f l1.[k] y) l2) = 0);
    assert (forall (k:nat{k<n1}). s1.[k] = 0);
    modular_sum_n_all_zero s1;
    assert (modular_sum_n s2 = 0)
    end
  else begin
  modular_fubini_sublemma1 f l1 l2;
  assert(modular_sum_n s1 = modular_sum_n (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) l1) +% modular_sum_n (Seq.map (fun x -> f x l2.[0]) l1));
  modular_fubini_lemma f l1 (sub l2 1 (n2-1)) (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) l1) (Seq.map (fun y -> modular_sum_n (Seq.map (fun x -> f x y) l1)) (sub l2 1 (n2-1)));
  assert(modular_sum_n s1 = modular_sum_n (Seq.map (fun y -> modular_sum_n (Seq.map (fun x -> f x y) l1)) (sub l2 1 (n2-1))) +% (fun y -> modular_sum_n (Seq.map (fun x -> f x y) l1)) l2.[0]);  
  map_sub_commutativity_lemma l2 (fun y -> modular_sum_n (Seq.map (fun x -> f x y) l1)) 1 (n2-1);
  dummy_modular_fubini_sublemma (fun y -> modular_sum_n (Seq.map (fun x -> f x y) l1)) l2;
  assert(modular_sum_n s1 = modular_sum_n (sub (Seq.map (fun y -> modular_sum_n (Seq.map (fun x -> f x y) l1)) l2) 1 (n2-1)) +% (Seq.map (fun y -> modular_sum_n (Seq.map (fun x -> f x y) l1)) l2).[0])
  end

#reset-options "--z3rlimit 200 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"    
	
  
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


val extended_gcd_simple_lemma: x:pos -> y:pos -> Lemma (let (u1,v1,g1) = extended_gcd x y in let (u2,v2,g2)= extended_gcd y (x%y) in (u1,v1,g1) == (v2, u2 - (x/y) * v2, g2))

let extended_gcd_simple_lemma x y = ()

#reset-options "--z3rlimit 200 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"    

val gcd_lemma: x:pos -> y:nat -> p:pos{x % p = 0 /\ y % p = 0} -> Lemma (ensures (gcd x y) % p = 0) (decreases y)

let rec gcd_lemma x y p =
  if y = 0 then ()
  else begin
    assert (x = (x/y) * y + (x%y));
    assert ((x%y) = x - (x/y) * y);
    assert (x = (x/p) * p);
    assert (y = (y/p) * p);
    assert ((x%y) = ((x/p) * p ) - (x/y)*((y/p)*p));
    paren_mul_right (x/y) (y/p) p;
    paren_mul_left (x/y) (y/p) p;
    assert ((x%y) = ((x/p) * p ) - ((x/y)*(y/p))*p);
    distributivity_sub_left (x/p) ((x/y)*(y/p)) p;
    assert ((x%y) = (x/p - (x/y) *(y/p))*p);
    lemma_mod_plus 0 (x/p - (x/y) *(y/p)) p;
    gcd_lemma y (x%y) p;
    extended_gcd_simple_lemma x y
    end

#reset-options "--z3rlimit 200 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"    

val gcd_lemma2: x:pos -> y:nat -> Lemma (ensures (let g = gcd x y in x % g = 0 /\ y % g = 0)) (decreases y)

let rec gcd_lemma2 x y =
  let g = gcd x y in
  if (y=0) then ()
  else
    begin
    gcd_lemma2 y (x%y);
    extended_gcd_simple_lemma x y;
    assert(y % g = 0 /\ (x%y) %g = 0);
    lemma_mod_mul_distr_r (x/y) y g;
    modulo_distributivity ((x/y) * y) (x%y) g
    end

val gcd_lemma3: x:pos -> y:nat -> u:int -> v:int -> w:pos{x*u + y*v = w} -> Lemma (ensures (let g = gcd x y in w % g = 0))

let gcd_lemma3 x y u v w =
  let g = gcd x y in
  gcd_lemma2 x y;
  modulo_distributivity (x*u) (y*v) g;
  lemma_mod_mul_distr_l x u g;
  lemma_mod_mul_distr_l y v g


#reset-options "--z3rlimit 300 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"    

val is_invertible: #q:nat{q>1} -> x:field q -> Type0

let is_invertible #q x =
  exists (y:field q). x *% y = 1

#reset-options "--z3rlimit 300 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"    

val gcd_lemma_invertible_1:#q:nat{q>1} -> x:field q{gcd q x = 1} -> Lemma (is_invertible x)

let gcd_lemma_invertible_1 #q x =
  let (u,v,g) = extended_gcd q x in
  assert(g=gcd q x);
  assert(u*q+v*x=1);
  lemma_mod_plus (v*x) u q;
  assert((v*x)%q = 1);
  lemma_mod_mul_distr_l v x q;
  assert ((v%q)*%x =1)
    


val gcd_lemma_invertible_:#q:nat{q>1} -> x:field q -> y:field q{x*%y=1} -> GTot (squash (gcd q x = 1))

let gcd_lemma_invertible_ #q x y =
    let g = gcd q x in
    assert((x*y)%q = 1);
    assert(x*y = ((x*y)/q)*q + (x*y)%q);
    assert(x*y - ((x*y)/q)*q = 1); 
    swap_add_plus_minus 0 (x*y) (((x*y)/q)*q);
    assert((-(((x*y)/q)*q)) + x*y = 1);
    swap_mul ((x*y)/q) q;
    neg_mul_right q ((x*y)/q); 
    assert(q*(-((x*y)/q)) + x*y = 1);
    gcd_lemma3 q x (-((x*y)/q)) y 1


val gcd_lemma_invertible_2: #q:nat{q>1} -> x:field q{is_invertible x} -> Lemma (gcd q x = 1)

let gcd_lemma_invertible_2 #q x =
  let unref (a:Type) (phi : a -> Type) (x : a {phi x}) : squash (phi x) = () in
  assert(gcd q x = 1) by (
	     let b = pose (quote (unref _ _ x)) in
	     apply_lemma (`(exists_elim _ (`#(binder_to_term b))));
	     exact (quote(gcd_lemma_invertible_ x)))
  
  //let customp (y:field q) : Type0 = (x *% y = 1) in
  //let g = gcd q x in
  //let a = assert(exists (y:field q). customp y) in
    //exists_elim (gcd q x = 1) #(field q) #customp a (gcd_lemma_invertible_ #q x)    
  
#reset-options "--z3rlimit 300 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"    

val gcd_lemma_invertible: #q:nat{q>1} -> x:field q -> Lemma (gcd q x = 1 <==> is_invertible x)


//let split_lemma (p : squash 'a) (q : squash 'b) : Lemma ('a /\ 'b) = ()


let gcd_lemma_invertible #q x =   
  //assert (let g = Mktuple3?._3 (extended_gcd q x) in (g = 1 <==> is_invertible x)) by (apply_lemma (`split_lemma); dump""
  let split_lemma (p : squash 'a) (q : squash 'b) : Lemma ('a /\ 'b) = () in
  assert(gcd q x = 1 <==> is_invertible x) by (apply_lemma (quote(split_lemma)); let _ = implies_intro () in apply_lemma(`gcd_lemma_invertible_1); let _ = implies_intro () in apply_lemma(`gcd_lemma_invertible_2); qed())


val invert_mod: #q:nat{q>1} -> x:field q{is_invertible x} -> y:field q{x *% y = 1}

let invert_mod #q x =
  let (u, v, _) = extended_gcd q x in
  gcd_lemma_invertible x;
  assert(u * q + v * x = 1);
  lemma_mod_plus (v*x) u q;
  assert ((v * x) % q = 1);
  lemma_mod_mul_distr_l v x q;
  v % q

val is_prime: q:nat{q>1} -> Type0

let is_prime q = forall (p:field q{p>0}). (q % p = 0 ==> p = 1)

#reset-options "--z3rlimit 300 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"    


val lemma_q_prime_zq_field_1: q:nat{q>1 /\ is_prime q} -> Lemma (forall (x:field q{x>0}). is_invertible x)

let lemma_q_prime_zq_field_1 q =
  let customlemma (x:field q{x>0}) : Lemma (is_invertible x) =
    let (_,_,g) = extended_gcd q x in
    gcd_lemma2 q x;
    assert(q % g = 0);
    assert(g = 1);
    gcd_lemma_invertible x
  in
  assert((forall (x:field q{x>0}). is_invertible x)) by (let _ = forall_intro () in apply_lemma(quote(customlemma)); qed()) 

val lemma_q_prime_zq_field_2: q:nat{q>1 /\ (forall (x:field q{x>0}). is_invertible x)} -> Lemma (is_prime q)

let lemma_q_prime_zq_field_2_ (q:nat{q>1 /\ (forall (x:field q{x>0}). is_invertible x)}) (p:field q{p>0 /\ q % p = 0}) : Lemma (p = 1) =
      assert(is_invertible p);
      gcd_lemma_invertible p;
      assert(q % p = 0 /\ p % p = 0);
      gcd_lemma q p p;
      assert (p=1)

let lemma_q_prime_zq_field_2 q =
  let customprop (p:field q{p>0}) : Type0 = (q % p = 0 ==> p = 1) in
  let customlemma (p:field q{p>0}) : Lemma (customprop p) =
    assert( q % p = 0 ==> p = 1) by (let _ = FStar.Tactics.Logic.implies_intro () in apply_lemma(`lemma_q_prime_zq_field_2_))
    in FStar.Classical.forall_intro customlemma

#reset-options "--z3rlimit 300 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"    

val lemma_q_prime_zq_field: q:nat{q>1} -> Lemma (is_prime q <==> (forall (x:field q{x>0}). is_invertible x))


let lemma_q_prime_zq_field q =
  assert(is_prime q ==> (forall (x:field q{x>0}). is_invertible x)) by (let _ = FStar.Tactics.implies_intro () in apply_lemma (`lemma_q_prime_zq_field_1));
  assert((forall (x:field q{x>0}). is_invertible x) ==> is_prime q) by (let _ = FStar.Tactics.implies_intro () in apply_lemma (`lemma_q_prime_zq_field_2))

val lemma_is_prime_params_q: unit -> Lemma (is_prime params_q)

let lemma_is_prime_params_q () =
  let customprop (p:field params_q{p>1}) = (params_q % p <> 0) in
  let f (p:field params_q{p>1}) : Lemma (customprop p) =
    assert(params_q % p <> 0) in
  FStar.Classical.forall_intro f  


