module Lib.Arithmetic.Sums

open FStar.Math.Lemmas
open FStar.Mul
open FStar.Tactics.Typeclasses
//open Lib.ModularArithmetic.Lemmas
//open Lib.ModularArithmetic

open Lib.Arithmetic.Ring

module Seq = Lib.Sequence
module Loops = Lib.LoopCombinators

#reset-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"    

let rec sum_n #a [|ring a|] #n l =
  if n=0 then zero
  else
  let s=sum_n (sub l 1 (n-1)) in
  plus l.[0] s

 
inline_for_extraction
val simpl_seq_sub_sub_lemma: 
  #a:Type
  -> #len:size_nat 
  -> l:lseq a len 
  -> start1:size_nat 
  -> n1:size_nat{start1+n1<=len} 
  -> start2:size_nat 
  -> n2:size_nat{start2+n2<=n1} 
  -> Lemma(sub (sub l start1 n1) start2 n2 == sub l (start1+start2) n2) 

let simpl_seq_sub_sub_lemma #a #len l start1 n1 start2 n2 =
  let s = sub (sub l start1 n1) start2 n2 in
  assert ((forall (k:nat{k<n2}). index s k == index (sub l start1 n1) (k+start2)));
  assert ((forall (k:nat{k<n2}). index s k == index l (start1+start2+k)));
  eq_intro s (sub l (start1+start2) n2);
  eq_elim s (sub l (start1+start2) n2)

#reset-options "--z3rlimit 200 --max_fuel 2 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"    

inline_for_extraction
val sum_n_simple_lemma: 
  #a:Type0
  -> #[FStar.Tactics.Typeclasses.tcresolve ()] r:ring a
  -> #n:size_nat{n>=1}
  -> l:lseq a n 
  -> Lemma (ensures sum_n l == plus (sum_n (sub l 0 (n-1))) (l.[n-1])) 
	  (decreases n)

let rec sum_n_simple_lemma #a #r #n l =
  if n = 1 then (lemma_zero1 #a l.[0]; lemma_zero2 #a l.[0])
  else
    calc (==) {
      sum_n l;
	== {}
      plus l.[0]  (sum_n (sub l 1 (n-1)));
	== {sum_n_simple_lemma (sub l 1 (n-1)); ()}
      plus l.[0] (plus (sum_n (sub (sub l 1 (n-1)) 0 (n-2))) (sub l 1 (n-1)).[n-2]);
	== {simpl_seq_sub_sub_lemma l 1 (n-1) 0 (n-2); assert((sub l 1 (n-1)).[n-2] == l.[n-1]); ()}
      plus l.[0] (plus (sum_n (sub l 1 (n-2))) l.[n-1]);
	== {lemma_plus_assoc l.[0] (sum_n (sub l 1 (n-2))) l.[n-1]; ()}
      plus (plus l.[0] (sum_n (sub l 1 (n-2)))) l.[n-1];
	== {simpl_seq_sub_sub_lemma l 0 (n-1) 1 (n-2); ()}
      plus (plus (sub l 0 (n-1)).[0] (sum_n (sub (sub l 0 (n-1)) 1 (n-2)))) l.[n-1]; 
	== {}
      plus (sum_n (sub l 0 (n-1))) (l.[n-1]);
    }

inline_for_extraction
val map_sub_commutativity_lemma: 
  #a:Type0
  -> #b:Type0
  -> #n:size_nat 
  -> l:lseq a n
  -> f:(a -> b) 
  -> i:size_nat 
  -> len:size_nat{i+len<=n} 
  -> Lemma (ensures sub (Seq.map f l) i len == Seq.map f (sub l i len))

#reset-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"    

let rec map_sub_commutativity_lemma #a #b #n l f i len =
  assert(forall (k:nat{k<len}). (sub (Seq.map f l) i len).[k] == (Seq.map f l).[i+k]);
  assert(forall (k:nat{k<len}). (sub (Seq.map f l) i len).[k] == f l.[i+k]);
  assert(forall (k:nat{k<len}). (sub (Seq.map f l) i len).[k] == f (sub l i len).[k]);
  assert(forall (k:nat{k<len}). f (sub l i len).[k] == (Seq.map f (sub l i len)).[k]);
  eq_intro (sub (Seq.map f l) i len) (Seq.map f (sub l i len));
  eq_elim (sub (Seq.map f l) i len) (Seq.map f (sub l i len))
  
#reset-options "--z3rlimit 200 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"    

let rec sum_n_mul_distrib_l_lemma #a [|ring a|] #n l k =
  if n=0 then lemma_zero_absorb2 k
  else begin
    assert(mul k (sum_n l) == mul k (plus l.[0] (sum_n (sub l 1 (n-1)))));
    lemma_distr_left k l.[0] (sum_n (sub l 1 (n-1)));
    assert(mul k (sum_n l) == plus (mul k l.[0]) (mul k (sum_n (sub l 1 (n-1)))));
    sum_n_mul_distrib_l_lemma (sub l 1 (n-1)) k;
    assert((Seq.map (fun x -> mul k x) l).[0] == mul k l.[0]);
    assert (mul k (sum_n l) == plus (Seq.map (fun x -> mul k x) l).[0] (sum_n (Seq.map (fun x -> mul k x) (sub l 1 (n-1)))));
    map_sub_commutativity_lemma l (fun x -> mul k x) 1 (n-1);
    assert (mul k (sum_n l) == plus (Seq.map (fun x -> mul k x) l).[0] (sum_n (sub (Seq.map (fun x -> mul k x) l) 1 (n-1))))
  end



let rec sum_n_mul_distrib_r_lemma #a [|ring a|] #n l k =
  if n=0 then lemma_zero_absorb1 k
  else begin
    assert(mul (sum_n l) k == mul (plus l.[0] (sum_n (sub l 1 (n-1)))) k);
    admit();
    lemma_distr_right k l.[0] (sum_n (sub l 1 (n-1)));
    assert(mul (sum_n l) k == plus (mul l.[0] k) (mul (sum_n (sub l 1 (n-1))) k));
    sum_n_mul_distrib_r_lemma (sub l 1 (n-1)) k;
    assert((Seq.map (fun x -> mul x k) l).[0] == mul l.[0] k);
    assert (mul (sum_n l) k == plus (Seq.map (fun x -> mul x k) l).[0] (sum_n (Seq.map (fun x -> mul x k) (sub l 1 (n-1)))));
    map_sub_commutativity_lemma l (fun x -> mul x k) 1 (n-1);
    assert (mul (sum_n l) k == plus (Seq.map (fun x -> mul x k) l).[0] (sum_n (sub (Seq.map (fun x -> mul x k) l) 1 (n-1))))
  end

#reset-options "--z3rlimit 200 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

let rec sum_n_all_zero #a #r #n l =
  if n = 0 then ()
  else(
    assert(sum_n l == plus l.[0] (sum_n (sub l 1 (n-1))));
    sum_n_all_zero (Lib.Sequence.sub l 1 (n-1));
    assert(sum_n l == r.plus l.[0] r.zero);
    r.lemma_zero2 l.[0])


let rec modular_sum_n_one_non_zero_coeff #n #q k l =
  if k = 0 then begin
    modular_sum_n_all_zero (sub l 1 (n-1));
    assert (modular_sum_n l = l.[0] +% modular_sum_n (sub l 1 (n-1)));
    assert (modular_sum_n l = l.[0]) end
  else begin
    assert(modular_sum_n l = l.[0] +% modular_sum_n (sub l 1 (n-1)));
    assert(l.[0]=0);
    modular_sum_n_one_non_zero_coeff (k-1) (sub l 1 (n-1));
    assert(modular_sum_n (sub l 1 (n-1)) = l.[k]);
    assert(modular_sum_n l = 0 +% l.[k]);
    modulo_distributivity 0 l.[k] q
  end
  

let rec modular_sum_n_all_1_is_n_mod_q #n #q l =
  let _lemma (a:pos) : Lemma ((1+(a-1)) % q = a % q) =
    ()
  in
  if n = 0 then () 
  else begin
    assert(modular_sum_n #n #q l = l.[0] +% (modular_sum_n #(n-1) #q (sub l 1 (n-1))));
    modular_sum_n_all_1_is_n_mod_q #(n-1) #q (sub l 1 (n-1));
    assert(1%q = 1);
    assert(modular_sum_n l = (1%q) +% ((n-1) % q));
    modulo_distributivity 1 (n-1) q;
    assert(modular_sum_n l = (1 + (n-1)) %q);
    _lemma n;
    assert(modular_sum_n l = n % q)
  end



#reset-options "--z3rlimit 200 --max_fuel 2 --max_ifuel 2 --using_facts_from '* -FStar.Seq'"    

(**fubini lemma *)

val modular_fubini_lemma_: 
  #n1:size_nat 
  -> #n2:size_nat 
  -> #q:nat{q>0} 
  -> l1: set n1 q 
  -> l2: set n2 q
  -> Lemma (ensures modular_sum_n (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> x *% y) l2)) l1) = modular_sum_n (Seq.map (fun y -> modular_sum_n (Seq.map (fun x -> x *% y) l1)) l2))

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

val dummy_modular_fubini_sublemma: 
  #n:size_nat{n>0} 
  -> #q1:nat 
  -> #q2:nat 
  -> g:(field q1 -> field q2) 
  -> l:set n q1 
  -> Lemma((Seq.map g l).[0] = g l.[0])

let dummy_modular_fubini_sublemma #n #q1 #q2 g l = 
  ()
 
#reset-options "--z3rlimit 200 --max_fuel 2 --max_ifuel 2 --using_facts_from '* -FStar.Seq'"    

val modular_fubini_sublemma0: 
  #n1:size_nat{n1>0} 
  -> #n2:size_nat{n2>0} 
  -> #q1:nat 
  -> #q2:nat
  -> #q3:pos
  -> f: (field q1 -> field q2 -> field q3) 
  -> l1: set n1 q1 
  -> l2: set n2 q2 
  -> Lemma(ensures (modular_sum_n (Seq.map (fun y -> f l1.[0] y) l2)) +% (modular_sum_n (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) (sub l1 1 (n1-1))) +% modular_sum_n (Seq.map (fun x -> f x l2.[0]) (sub l1 1 (n1-1)))) = (modular_sum_n (Seq.map (fun y -> f l1.[0] y) (sub l2 1 (n2-1))) +% modular_sum_n (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) (sub l1 1 (n1-1)))) +% (f l1.[0] l2.[0] +% modular_sum_n (Seq.map (fun x -> f x l2.[0]) (sub l1 1 (n1-1))))) 

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


val modular_fubini_sublemma1: 
  #n1:size_nat 
  -> #n2:size_nat{n2>0} 
  -> #q1:nat 
  -> #q2:nat 
  -> #q3:pos
  -> f: (field q1 -> field q2 -> field q3)
  -> l1: set n1 q1
  -> l2: set n2 q2
  -> Lemma(ensures modular_sum_n (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) l2)) l1) = modular_sum_n (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) l1) +% modular_sum_n (Seq.map (fun x -> f x l2.[0]) l1)) (decreases n1)



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
     

#reset-options "--z3rlimit 200 --max_fuel 2 --max_ifuel 2 --using_facts_from '* -FStar.Seq'"    

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
