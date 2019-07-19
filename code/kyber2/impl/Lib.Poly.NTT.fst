module Lib.Poly.NTT

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open FStar.Mul
open FStar.Math.Lemmas
open FStar.Classical
open FStar.Tactics

open Lib.Arithmetic.Group
open Lib.Arithmetic.Ring
open Lib.Arithmetic.Sums
//open Lib.ModularArithmetic
//open Lib.ModularArithmetic.Lemmas

//friend Lib.ModularArithmetic.Lemmas

module Seq = Lib.Sequence
module Loops = Lib.LoopCombinators


#reset-options "--z3rlimit 100 --max_fuel 2 --max_ifuel 2 --using_facts_from '* -FStar.Seq'"


let powers #a [|ring a|] n o =
  createi n (fun i -> exp o i)

val sum_nth_root_unity_lemma_:
  #a: Type0
  -> #[tcresolve ()] r: ring a
  -> n:size_nat
  -> o:a{exp o n == one /\ ~(o==one)}
  -> Lemma (sum_n #a #add_ag.g.m (powers n o) == mul #a o (sum_n #a #add_ag.g.m (powers n o)))

let sum_nth_root_unity_lemma_ #a [| ring a |] n o =
  let m = (add_ag #a).g.m in
  let p = powers #a n o in
  let s = sum_n p in
  let p' = Seq.map (fun x -> mul #a o x) p in
  let s' = sum_n p' in
  sum_n_mul_distrib_l_lemma p o;
  assert (s'== mul #a o s);
  assert (forall(k:nat{k<n-1}). exp #a o (k+1) == mul #a o (exp #a o k)) by (let _ = FStar.Tactics.forall_intro () in apply_lemma(`lemma_exp_succ1));
  assert (forall(k:nat{k<n-1}). p'.[k] == p.[k+1]);
  assert (forall(k:nat{k<n-1}). (sub p' 0 (n-1)).[k] == (sub p 1 (n-1)).[k]);
  if (n=0) then (sum_n_zero_elements_is_id p; sum_n_zero_elements_is_id p'; lemma_zero_absorb2 #a o)
  else begin
  eq_intro (sub p' 0 (n-1)) (sub p 1 (n-1));
  eq_elim (sub p' 0 (n-1)) (sub p 1 (n-1));
  sum_n_simple_lemma2 p';
  lemma_exp_succ1 #a o (n-1);
  assert(p'.[n-1] == exp #a o n);
  lemma_exp_zero #a o;
  assert(p'.[n-1] == p.[0]);
  sum_n_simple_lemma2 p';
  lemma_plus_swap (sum_n (sub p 1 (n-1))) p.[0];
  sum_n_simple_lemma1 p
  end

#reset-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

let sum_nth_root_unity_lemma #a [| ring a |] n o =
  let m = (add_ag #a).g.m in
  let p = powers #a n o in
  let s = sum_n p in

  sum_nth_root_unity_lemma_ n o;
  assert (s == mul #a o s);
  lemma_plus_opp1 s;
  lemma_one1 s;
  lemma_minus_mul_distr_right s o one;
  assert (mul (minus #a o one) s == zero);
  lemma_zero_absorb2 (minus #a o one);
  lemma_mul_eq1_m #a (minus #a o one) s zero

#reset-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

let lib_ntt_sequence #a [| ring a |] #n omega psi p k =
  mapi (fun j g -> mul (exp psi j) (mul g (exp omega (k*j)))) p

let lib_ntt_sequence_instantiate #a [| ring a |] #n omega psi p p' k j =
  ()

let lib_ntt #a [| ring a |] #n omega psi p =
  let m = (add_ag #a).g.m in
  createi n (fun k -> sum_n (mapi (fun j g -> mul (exp psi j) (mul g (exp omega (k*j)))) p))

let lib_ntt_lemma_instantiate #a [| ring a |] #n omega psi p p' k = ()

let lib_ntt_lemma #a [| ring a |] #n omega psi p p' = ()

let lib_nttinv_sequence #a [| ring a |] #n omegainv p k =
  mapi (fun j g -> mul #a g (exp omegainv (k*j))) p

let lib_nttinv_sequence_instantiate #a [| ring a |] #n omegainv p p' k j = ()

let lib_nttinv #a [| ring a |] #n ninv omegainv psiinv p =
  let m = (add_ag #a).g.m in
  createi n (fun k -> mul ninv (mul (exp psiinv k) (sum_n (mapi (fun j g -> mul g (exp omegainv (k*j))) p))))

let lib_nttinv_lemma_instantiate #a [| ring a |] #n ninv omegainv psiinv p p' k = ()

let lib_nttinv_lemma #a [| ring a |] #n ninv omegainv psiinv p p' = ()

#reset-options "--z3rlimit 1000 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val lib_ntt_inversion1_sublemma_kj:
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat
  -> omega:a
  -> omegainv :a
  -> psi:a
  -> p:lib_poly a n
  -> k:nat{k<n}
  -> j:nat{j<n} ->
  Lemma(let pntt = lib_ntt omega psi p in
	let sk = mapi (fun l g -> mul g (exp omegainv (k*l))) pntt in let l = createi n (fun x -> x) in let f = (fun (x:nat{x<n}) (y:nat{y<n}) -> mul (exp psi y) (mul p.[y] (mul (exp omega (x*y)) (exp omegainv (k*x))))) in sk.[j] == sum_n #a #add_ag.g.m (Seq.map (fun y -> f j y) l))


let lib_ntt_inversion1_sublemma_kj #a [| ring a |] #n omega omegainv psi p k j =
  let m = (add_ag #a).g.m in
  let pntt = lib_ntt omega psi p in
  let sk = mapi (fun l g -> mul g (exp omegainv (k*l))) pntt in
  let l = createi n (fun x -> x) in
  let f = (fun (x:nat{x<n}) (y:nat{y<n}) -> mul (exp psi y) (mul p.[y] (mul (exp omega (x*y)) (exp omegainv (k*x))))) in
  let s' = mapi (fun i g -> mul (exp psi i) (mul g (exp omega (j*i)))) p in
  let s = Seq.map (fun y -> mul y (exp omegainv (k*j))) s' in
  //assert(sk.[j] == mul #a pntt.[j] (exp omegainv (k*j)));
  //assert(pntt.[j] == sum_n (mapi (fun i g -> mul (exp psi i) (mul g (exp omega (j*i)))) p));
  //assert(sk.[j] == (mul (sum_n (mapi (fun i g -> mul (exp psi i) (mul g (exp omega (j*i)))) p)) (exp omegainv (k*j))));
  sum_n_mul_distrib_r_lemma (mapi (fun i g -> mul (exp psi i) (mul g (exp omega (j*i)))) p) (exp omegainv (k*j));
  //assert(sk.[j] == sum_n s);
  //assert(forall (d:nat{d<n}). s.[d] == mul #a (mul (exp psi d) (mul p.[d] (exp omega (j*d)))) (exp omegainv (k*j)));
  let customprop (d:nat{d<n}) : GTot Type0 =
    s.[d] == f j d in
  let customlemma (d:nat{d<n}) : Lemma (customprop d) =
    lemma_mul_assoc (exp psi d) (mul p.[d] (exp omega (j*d))) (exp omegainv (k*j));
    lemma_mul_assoc p.[d] (exp omega (j*d)) (exp omegainv (k*j))
  in
  FStar.Classical.forall_intro customlemma;
  eq_intro s (Seq.map (fun y -> f j y) l);
  eq_elim s (Seq.map (fun y -> f j y) l)

#reset-options "--z3rlimit 300 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val lib_ntt_inversion1_sublemma_kjd':
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat
  -> omega:a{exp omega n == one}
  -> omegainv: a{mul omega omegainv == one}
  -> psi:a
  -> p:lib_poly a n
  -> k:nat{k<n}
  -> j:nat{j<n}
  -> d:nat{d<n}
  -> Lemma(let l = createi n (fun x -> x) in
	  let f = (fun (x:nat{x<n}) (y:nat{y<n}) -> mul (exp psi y) (mul p.[y] (mul (exp omega (x*y)) (exp #a omegainv (k*x))))) in
	  let s = Seq.map (fun x -> f x j) l in
	  s.[d] == mul #a (mul #a (exp psi j) p.[j]) (exp (exp omega ((j-k)%n)) d))


#reset-options "--z3rlimit 300 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

let lib_ntt_inversion1_sublemma_kjd' #a [| ring a |] #n omega omegainv psi p k j d =
  let l = createi n (fun x -> x) in
  let f = (fun (x:nat{x<n}) (y:nat{y<n}) -> mul (exp psi y) (mul p.[y] (mul (exp omega (x*y)) (exp #a omegainv (k*x))))) in
  let s = Seq.map (fun x -> f x j) l in
  assert(s.[d] == f d j);
  assert(s.[d] == mul #a (exp psi j) (mul p.[j] (mul (exp omega (d*j)) (exp #a omegainv (k*d)))));
  lemma_simpl_exp_with_inv1 #a omega omegainv n (d*j) (k*d);
  assert(s.[d] == mul #a (exp psi j) (mul p.[j] (exp #a omega ((d*j-k*d)%n))));
  lemma_mul_sub_distr d j k;
  assert(s.[d] == mul #a (exp psi j) (mul p.[j] (exp #a omega (((j-k)*d)%n))));
  lemma_mod_mul_distr_l (j-k) d n;
  lemma_simpl_exp #a omega n (((j-k)%n)*d);
  lemma_exp_exp #a omega ((j-k)%n) d;
  lemma_exp_exp #a omegainv k d;
  lemma_mul_assoc #a (exp psi j) p.[j] (exp (exp #a omega ((j-k)%n)) d)


#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

val lib_ntt_inversion1_sublemma_kj'_:
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat
  -> omega:a{exp omega n == one}
  -> omegainv:a{mul omega omegainv == one}
  -> psi:a
  -> p:lib_poly a n
  -> k:nat{k<n}
  -> j:nat{j<n}
  -> Lemma(let l = createi n (fun x -> x) in
	  let f : (x:nat{x<n}) -> (y:nat{y<n}) -> a = (fun x y -> mul (exp psi y) (mul p.[y] (mul (exp omega (x*y)) (exp omegainv (k*x))))) in
	  let sk' = Seq.map (fun y -> sum_n #a #add_ag.g.m (Seq.map (fun x -> f x y) l)) l in
	  let pows = powers n (exp omega ((j-k)%n)) in
	  sk'.[j] == mul #a (mul (exp psi j) p.[j]) (sum_n #a #add_ag.g.m pows))

let lib_ntt_inversion1_sublemma_kj'_ #a [| ring a |] #n omega omegainv psi p k j =
  let m = (add_ag #a).g.m in
  let l = createi n (fun x -> x) in
  let f : (x:nat{x<n}) -> (y:nat{y<n}) -> a = (fun x y -> mul (exp psi y) (mul p.[y] (mul (exp omega (x*y)) (exp omegainv (k*x))))) in
  let sk' = Seq.map (fun y -> sum_n (Seq.map (fun x -> f x y) l)) l in
  assert (sk'.[j] == sum_n (Seq.map (fun x -> f x j) l));
  let s = Seq.map (fun x -> f x j) l in
  let pows = powers n (exp omega ((j-k) % n)) in
  assert (sk'.[j] == sum_n s);
  let customprop (d:nat{d<n}) : Type0 =
    s.[d] == mul #a (mul (exp psi j) p.[j]) pows.[d] in
  let customlemma (d:nat{d<n}) : Lemma (customprop d) =
    lib_ntt_inversion1_sublemma_kjd' omega omegainv psi p k j d in
  FStar.Classical.forall_intro customlemma;
  eq_intro s (Seq.map (fun y -> mul (mul (exp psi j) p.[j]) y) pows);
  eq_elim s (Seq.map (fun y -> mul (mul (exp psi j) p.[j]) y) pows);
  sum_n_mul_distrib_l_lemma pows (mul (exp psi j) p.[j]);
  assert( sum_n s == mul (mul (exp psi j) p.[j]) (sum_n pows));
  assert(sk'.[j] == mul (mul (exp psi j) p.[j]) (sum_n pows))

#reset-options "--z3rlimit 300 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

val lib_ntt_inversion1_sublemma_kj':
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat
  -> omega:a{exp omega n == one /\ (forall (nn:nat{nn<n}). (exp omega nn == one ==> nn = 0) /\ (~(is_invertible(minus (exp omega nn) one)) ==> nn = 0))}
  -> omegainv:a{mul omega omegainv == one}
  -> psi:a
  -> p:lib_poly a n
  -> k:nat{k<n}
  -> j:nat{j<n /\ j <>k}
  -> Lemma(let l = createi n (fun x -> x) in
	  let f : (y:nat{y<n}) -> (y:nat{y<n}) -> a = (fun x y -> mul (exp psi y) (mul p.[y] (mul (exp omega (x*y)) (exp omegainv (k*x))))) in
	  let sk' = Seq.map (fun y -> sum_n #a #add_ag.g.m (Seq.map (fun x -> f x y) l)) l in
	  let pows = powers #a n (exp omega ((j-k)%n)) in
	  sk'.[j] == zero #a)

#reset-options "--z3rlimit 500 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

let lib_ntt_inversion1_sublemma_kj' #a [| ring a |] #n omega omegainv psi p k j =
    let m = (add_ag #a).g.m in
    let l = createi n (fun x -> x) in
    let f : (y:nat{y<n}) -> (y:nat{y<n}) -> a = (fun x y -> mul (exp psi y) (mul p.[y] (mul (exp omega (x*y)) (exp omegainv (k*x))))) in
    let sk' = Seq.map (fun y -> sum_n #a #add_ag.g.m (Seq.map (fun x -> f x y) l)) l in
    let h = ((j-k)%n) in
    let pows = powers #a n (exp omega h) in
    lib_ntt_inversion1_sublemma_kj'_ omega omegainv psi p k j;
    if(j>k) then (modulo_lemma (j-k) n; assert(h<>0))
    else (modulo_addition_lemma (j-k) 1 n; modulo_lemma ((j-k)+n) n; assert(h<>0));
    assert(h <> 0);
    lemma_exp_exp #a omega h n;
    lemma_exp_exp #a omega n h;
    assert (exp #a (exp omega h) n == exp #a (exp omega n) h);
    lemma_exp_one #a h;
    let o = (exp #a omega h) in
    sum_nth_root_unity_lemma n o;
    assert (sum_n pows == zero);
    lemma_zero_absorb2 #a (mul (exp psi j) p.[j])

#reset-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val lib_ntt_inversion1_sublemma_kk':
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat
  -> omega:a{exp omega n == one}
  -> omegainv:a{mul omega omegainv == one}
  -> psi:a
  -> p:lib_poly a n
  -> k:nat{k<n}
  -> Lemma(let l = createi n (fun x -> x) in
	  let f : (x:nat{x<n}) -> (y:nat{y<n}) -> a = (fun x y -> mul (exp psi y) (mul p.[y] (mul (exp omega (x*y)) (exp omegainv (k*x))))) in
	  let sk' = Seq.map (fun y -> sum_n #a #add_ag.g.m (Seq.map (fun x -> f x y) l)) l in
	  sk'.[k] == mul #a (mul (exp psi k) (repeat_plus one n)) p.[k])

let lib_ntt_inversion1_sublemma_kk' #a [|ring a|] #n omega omegainv psi p k =
  let m = (add_ag #a).g.m in
  let l = createi n (fun x -> x) in
  let f : (x:nat{x<n}) -> (y:nat{y<n}) -> a = (fun x y -> mul (exp psi y) (mul p.[y] (mul (exp omega (x*y)) (exp omegainv (k*x))))) in
  let sk' = Seq.map (fun y -> sum_n #a (Seq.map (fun x -> f x y) l)) l in
  let h = ((k-k)%n) in
  let pows = powers #a n (exp omega ((k-k) % n)) in
  lib_ntt_inversion1_sublemma_kj'_ omega omegainv psi p k k;
  let customprop' (d:nat{d<n}) : Type0 = (pows.[d] == one #a) in
  let customlemma' (d:nat{d<n}) : Lemma (customprop' d) =
    assert ((k-k)%n = 0);
    lemma_exp_zero #a omega;
    lemma_exp_one #a d
    in
  FStar.Classical.forall_intro customlemma';
  sum_n_all_c_is_repeat_c_n one pows;
  lemma_mul_assoc (exp psi k) p.[k] (repeat_plus #a one n);
  lemma_one1 #a p.[k];
  lemma_one2 #a p.[k];
  lemma_repeat_plus_swap_mul #a one p.[k] n;
  lemma_mul_assoc (exp psi k) (repeat_plus #a one n) p.[k]


#reset-options "--z3rlimit 500 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val lib_ntt_inversion1_fubini_k:
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat
  -> ninv: a//{mul (repeat_plus one n) ninv == one}
  -> omega:a
  -> omegainv:a//{mul omega omegainv == 1}
  -> psi:a
  -> psiinv:a//{mul psiinv psi == 1}
  -> p:lib_poly a n
  -> k:nat{k<n}
  -> Lemma(let p' = lib_nttinv ninv omegainv psiinv (lib_ntt omega psi p) in
	  let l = createi n (fun x -> x) in
	  let f (x:nat{x<n}) (y:nat{y<n}) : a = mul (exp psi y) (mul p.[y] (mul (exp omega (x*y)) (exp omegainv (k*x)))) in
	  let sk' = Seq.map (fun y -> sum_n #a #add_ag.g.m (Seq.map (fun x -> f x y) l)) l in
	  p'.[k] == mul #a (mul ninv (exp psiinv k)) (sum_n #a #add_ag.g.m sk'))


let lib_ntt_inversion1_fubini_k #a [| ring a |] #n ninv omega omegainv psi psiinv p k =
  let m = (add_ag #a).g.m in
  let pntt = lib_ntt omega psi p in
  let p' = lib_nttinv ninv omegainv psiinv pntt in
  lemma_mul_assoc ninv (exp psiinv k) (sum_n (mapi (fun j g -> mul g (exp omegainv (k*j))) pntt));
  assert(p'.[k] == mul #a (mul ninv (exp psiinv k)) (sum_n (mapi (fun j g -> mul g (exp omegainv (k*j))) pntt)));
  let l = createi n (fun x -> x) in
  let f (x:nat{x<n}) (y:nat{y<n}) : a = mul (exp psi y) (mul p.[y] (mul (exp omega (x*y)) (exp omegainv (k*x)))) in
  let sk = mapi (fun j g -> mul g (exp omegainv (k*j))) pntt in
  let sk' = Seq.map (fun y -> sum_n (Seq.map (fun x -> f x y) l)) l in
  assert(p'.[k] == mul #a (mul ninv (exp psiinv k)) (sum_n sk));
  let customprop (j:nat{j<n}) : GTot Type0 =
    sk.[j] == sum_n (Seq.map (fun y -> f j y) l) in
  let customlemma (j:nat{j<n}) : Lemma (customprop j) =
    lib_ntt_inversion1_sublemma_kj omega omegainv psi p k j in
  FStar.Classical.forall_intro customlemma;
  eq_intro sk (Seq.map (fun x -> sum_n (Seq.map (fun y -> f x y) l)) l);
  eq_elim sk (Seq.map (fun x -> sum_n (Seq.map (fun y -> f x y) l)) l);
  assert(p'.[k] == mul (mul ninv (exp psiinv k)) (sum_n (Seq.map (fun x -> sum_n (Seq.map (fun y -> f x y) l)) l)));
  let s1 = (Seq.map (fun x -> sum_n (Seq.map (fun y -> f x y) l)) l) in
  let s2 = (Seq.map (fun y -> sum_n (Seq.map (fun x -> f x y) l)) l) in
  sum_n_fubini_ring f l l

#reset-options "--z3rlimit 500 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val lib_ntt_inversion1_lemma_k_:
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat
  -> ninv: a//{mul (repeat_plus one n) ninv == one}
  -> omega:a{exp omega n == one /\ (forall (nn:nat{nn<n}). (exp omega nn == one ==> nn = 0) /\ (~(is_invertible(minus (exp omega nn) one)) ==> nn = 0))}
  -> omegainv:a{mul omega omegainv == one}
  -> psi:a
  -> psiinv:a//{mul psiinv psi == one}
  -> p:lib_poly a n
  -> k:nat{k<n}
  -> Lemma(let p' = lib_nttinv ninv omegainv psiinv (lib_ntt omega psi p) in p'.[k] == mul #a (mul ninv (exp psiinv k)) (mul (mul (exp psi k) (repeat_plus one n)) p.[k]))


let lib_ntt_inversion1_lemma_k_ #a [| ring a |] #n ninv omega omegainv psi psiinv p k =
  let m = (add_ag #a).g.m in
  let p' = lib_nttinv ninv omegainv psiinv (lib_ntt omega psi p) in
  let l = createi n (fun x -> x) in
  let f (x:nat{x<n}) (y:nat{y<n}) : a = mul (exp psi y) (mul p.[y] (mul (exp omega (x*y)) (exp omegainv (k*x)))) in
  let sk' = Seq.map (fun y -> sum_n (Seq.map (fun x -> f x y) l)) l in

  lib_ntt_inversion1_fubini_k ninv omega omegainv psi psiinv p k;
  let customprop' (j:nat{j<n /\ j<>k}) : Type0 =
    sk'.[j] == zero #a in
  let customlemma' (j:nat{j<n /\ j<>k}) : Lemma (customprop' j) =
    assert(customprop' j) by (apply_lemma (`lib_ntt_inversion1_sublemma_kj'))
  in
  FStar.Classical.forall_intro customlemma';
  assert(sum_n sk' == sk'.[k]) by (apply_lemma(`sum_n_one_non_id_coeff));
  assert (p'.[k] == mul #a (mul ninv (exp psiinv k)) sk'.[k]);
  assert(sk'.[k] == mul #a (mul (exp psi k) (repeat_plus one n)) p.[k]) by (apply_lemma(`lib_ntt_inversion1_sublemma_kk'))

#reset-options "--z3rlimit 500 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val lib_ntt_inversion1_lemma_k:
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat
  -> ninv:a{mul ninv (repeat_plus one n) == one}
  -> omega:a{exp omega n == one /\ (forall (nn:nat{nn<n}). (exp omega nn == one ==> nn = 0) /\ (~(is_invertible(minus (exp omega nn) one)) ==> nn = 0))}
  -> omegainv:a{mul omega omegainv == one}
  -> psi:a
  -> psiinv:a{mul psiinv psi == one}
  -> p:lib_poly a n
  -> k:nat{k<n}
  -> Lemma(let p' = lib_nttinv ninv omegainv psiinv (lib_ntt omega psi p) in p'.[k] == p.[k])

#reset-options "--z3rlimit 500 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

let lib_ntt_inversion1_lemma_k #a [| ring a |] #n ninv omega omegainv psi psiinv p k =
  let p' = lib_nttinv ninv omegainv psiinv (lib_ntt omega psi p) in
  assert(p'.[k] == mul #a (mul ninv (exp psiinv k)) (mul (mul (exp psi k) (repeat_plus one n)) p.[k])) by (apply_lemma (`lib_ntt_inversion1_lemma_k_));
  lemma_mul_assoc #a (mul ninv (exp psiinv k)) (mul (exp psi k) (repeat_plus one n)) p.[k];
  lemma_mul_assoc #a (mul ninv (exp psiinv k)) (exp psi k) (repeat_plus one n);
  lemma_mul_assoc #a ninv (exp psiinv k) (exp psi k);
  lemma_exp_inv #a psiinv psi k;
  lemma_one2 #a ninv;
  lemma_one1 #a p.[k]

#reset-options "--z3rlimit 500 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"


let lib_ntt_inversion_lemma1 #a [| ring a |] #n ninv omega omegainv psi psiinv p =
  let pntt = lib_ntt omega psi p in
  let p' = lib_nttinv ninv omegainv psiinv pntt in

  let customprop (k:nat{k<n}) : Type0 = (p'.[k] == p.[k]) in
  let customlemma (k:nat{k<n}) : Lemma (customprop k) =
    lib_ntt_inversion1_lemma_k ninv omega omegainv psi psiinv p k
  in
  FStar.Classical.forall_intro customlemma;
  eq_intro p' p;
  eq_elim p' p

#reset-options "--z3rlimit 500 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val lib_ntt_inversion2_sublemma_kj:
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat
  -> ninv:a{mul ninv (repeat_plus one n) == one}
  -> omega:a
  -> omegainv:a
  -> psi:a
  -> psiinv:a{mul psi psiinv == one}
  -> p:lib_poly a n
  -> k:nat{k<n}
  -> j:nat{j<n}
  -> Lemma(let m = (add_ag #a).g.m in
	  let pnttinv = lib_nttinv ninv omegainv psiinv p in
	  let l = createi n (fun x -> x) in
	  let s = mapi (fun j g -> mul (exp psi j) (mul g (exp #a omega (k*j)))) pnttinv in
	  let f (x:nat{x<n}) (y:nat{y<n}) : a = mul #a p.[y] (mul (exp omegainv (x*y)) (exp omega (k*x))) in
	  s.[j] == mul #a ninv (sum_n (Seq.map (fun y -> f j y) l)))

let lib_ntt_inversion2_sublemma_kj #a [| ring a |] #n ninv omega omegainv psi psiinv p k j =
  let m = (add_ag #a).g.m in
  let pnttinv = lib_nttinv ninv omegainv psiinv p in
  let p' = lib_ntt omega psi pnttinv in
  let l = createi n (fun x -> x) in
  let s = mapi (fun j g -> mul (exp psi j) (mul g (exp #a omega (k*j)))) pnttinv in
  let f (x:nat{x<n}) (y:nat{y<n}) : a = mul #a p.[y] (mul (exp omegainv (x*y)) (exp omega (k*x))) in
  assert(s.[j] == mul #a (exp psi j) (mul (mul #a ninv (mul (exp psiinv j) (sum_n #a (mapi (fun i g -> mul g (exp omegainv (j*i))) p)))) (exp #a omega (k*j))));
  lemma_mul_assoc #a ninv (exp psiinv j) (sum_n #a (mapi (fun i g -> mul g (exp omegainv (j*i))) p));
  lemma_mul_assoc #a (exp psi j) (mul (mul ninv (exp psiinv j)) (sum_n #a (mapi (fun i g -> mul g (exp omegainv (j*i))) p))) (exp #a omega (k*j));
  lemma_mul_assoc #a (exp psi j) (mul ninv (exp psiinv j)) (sum_n #a (mapi (fun i g -> mul g (exp omegainv (j*i))) p));
  lemma_mul_assoc #a (exp psi j) ninv (exp psiinv j);

  // (mul (mul #a (exp psi j) ninv) (exp psiinv j)) == ninv
  lemma_mul_assoc #a (mul (exp psi j) ninv) (exp psiinv j) (repeat_plus #a one n);
  lemma_one1 #a (exp psiinv j);
  lemma_one2 #a (exp psiinv j);
  lemma_repeat_plus_swap_mul #a one (exp psiinv j) n;
  lemma_mul_assoc #a (mul (exp psi j) ninv) (repeat_plus #a one n) (exp psiinv j);
  lemma_mul_assoc #a (exp psi j) ninv (repeat_plus #a one n);
  lemma_one2 (exp psi j);
  lemma_exp_inv psi psiinv j;
  lemma_one1 #a ninv;
  lemma_one2 #a ninv;
  lemma_repeat_plus_swap_mul #a one ninv n;
  lemma_op_eq2_m_witness #a #mul_m (repeat_plus #a one n) ninv (mul (mul #a (exp psi j) ninv) (exp psiinv j)) ninv;

  lemma_mul_assoc #a ninv (sum_n #a (mapi (fun i g -> mul g (exp omegainv (j*i))) p)) (exp #a omega (k*j));
  assert(s.[j] == mul #a ninv (mul (sum_n #a (mapi (fun i g -> mul g (exp omegainv (j*i))) p)) (exp #a omega (k*j))));
  let s1 = mapi (fun i g -> mul g (exp omegainv (j*i))) p in
  let s2 = Seq.map (fun x -> mul #a x (exp #a omega (k*j))) s1 in
  sum_n_mul_distrib_r_lemma s1 (exp #a omega (k*j));
  assert (s.[j] == mul #a ninv (sum_n s2));
  let customprop' (i:nat{i<n}) : Type0 = (s2.[i] == f j i) in
  let customlemma' (i:nat{i<n}) : Lemma (customprop' i) =
    lemma_mul_assoc #a p.[i] (exp omegainv (j*i)) (exp omega (k*j))
  in
  FStar.Classical.forall_intro customlemma';
  eq_intro s2 (Seq.map (fun y -> f j y) l);
  eq_elim s2 (Seq.map (fun y -> f j y) l)

val lib_ntt_inversion2_sublemma_kjd':
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat
  -> omega:a{exp omega n == one}
  -> omegainv: a{mul omegainv omega == one}
  -> p:lib_poly a n
  -> k:nat{k<n}
  -> j:nat{j<n}
  -> d:nat{d<n}
  -> Lemma(let l = createi n (fun x -> x) in
	  let f = (fun (x:nat{x<n}) (y:nat{y<n}) -> mul #a p.[y] (mul (exp omegainv (x*y)) (exp #a omega (k*x)))) in
	  let s = Seq.map (fun x -> f x j) l in
	  s.[d] == mul #a p.[j] (exp (exp omega ((k-j)%n)) d))


#reset-options "--z3rlimit 300 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

let lib_ntt_inversion2_sublemma_kjd' #a [| ring a |] #n omega omegainv p k j d =
  let l = createi n (fun x -> x) in
  let f = (fun (x:nat{x<n}) (y:nat{y<n}) -> mul #a p.[y] (mul (exp omegainv (x*y)) (exp #a omega (k*x)))) in
  let s = Seq.map (fun x -> f x j) l in
  assert(s.[d] == f d j);
  assert(s.[d] == mul #a p.[j] (mul (exp omegainv (d*j)) (exp #a omega (k*d))));
  lemma_simpl_exp_with_inv2 #a omega omegainv n (d*j) (k*d);
  assert(s.[d] == mul #a p.[j] (exp #a omega ((k*d-d*j)%n)));
  lemma_mul_sub_distr d k j;
  assert(s.[d] == mul #a p.[j] (exp #a omega (((k-j)*d)%n)));
  lemma_mod_mul_distr_l (k-j) d n;
  lemma_simpl_exp #a omega n (((k-j)%n)*d);
  lemma_exp_exp #a omega ((k-j)%n) d

val lib_ntt_inversion2_sublemma_kj'_:
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat
  -> omega:a{exp omega n == one}
  -> omegainv:a{mul omegainv omega == one}
  -> p:lib_poly a n
  -> k:nat{k<n}
  -> j:nat{j<n}
  -> Lemma(let l = createi n (fun x -> x) in
	  let f : (x:nat{x<n}) -> (y:nat{y<n}) -> a = (fun x y -> mul p.[y] (mul (exp omegainv (x*y)) (exp omega (k*x)))) in
	  let sk = Seq.map (fun y -> sum_n #a #add_ag.g.m (Seq.map (fun x -> f x y) l)) l in
	  let pows = powers n (exp omega ((k-j)%n)) in
	  sk.[j] == mul #a p.[j] (sum_n #a #add_ag.g.m pows))

let lib_ntt_inversion2_sublemma_kj'_ #a [| ring a |] #n omega omegainv p k j =
  let m = (add_ag #a).g.m in
  let l = createi n (fun x -> x) in
  let f : (x:nat{x<n}) -> (y:nat{y<n}) -> a = (fun x y -> mul #a p.[y] (mul (exp omegainv (x*y)) (exp omega (k*x)))) in
  let sk = Seq.map (fun y -> sum_n (Seq.map (fun x -> f x y) l)) l in
  assert (sk.[j] == sum_n (Seq.map (fun x -> f x j) l));
  let s = Seq.map (fun x -> f x j) l in
  let pows = powers n (exp omega ((k-j) % n)) in
  assert (sk.[j] == sum_n s);
  let customprop (d:nat{d<n}) : Type0 =
    s.[d] == mul #a p.[j] pows.[d] in
  let customlemma (d:nat{d<n}) : Lemma (customprop d) =
    lib_ntt_inversion2_sublemma_kjd' omega omegainv p k j d in
  FStar.Classical.forall_intro customlemma;
  eq_intro s (Seq.map (fun y -> mul #a p.[j] y) pows);
  eq_elim s (Seq.map (fun y -> mul #a p.[j] y) pows);
  sum_n_mul_distrib_l_lemma pows (p.[j]);
  assert( sum_n s == mul #a p.[j] (sum_n pows));
  assert(sk.[j] == mul #a p.[j] (sum_n pows))

val lib_ntt_inversion2_sublemma_kj':
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat
  -> omega:a{exp omega n == one /\ (forall (nn:nat{nn<n}). (exp omega nn == one ==> nn = 0) /\ (~(is_invertible(minus (exp omega nn) one)) ==> nn = 0))}
  -> omegainv:a{mul omegainv omega == one}
  -> p:lib_poly a n
  -> k:nat{k<n}
  -> j:nat{j<n /\ j<>k}
  -> Lemma(let m = (add_ag #a).g.m in
	  let l = createi n (fun x -> x) in
	  let f (x:nat{x<n}) (y:nat{y<n}) : a = mul #a p.[y] (mul (exp omegainv (x*y)) (exp omega (k*x))) in
	  let sk = Seq.map (fun y -> sum_n (Seq.map (fun x -> f x y) l)) l in
	  sk.[j] == zero #a)

let lib_ntt_inversion2_sublemma_kj' #a [| ring a |] #n omega omegainv p k j =
  let m = (add_ag #a).g.m in
  let l = createi n (fun x -> x) in
  let f : (y:nat{y<n}) -> (y:nat{y<n}) -> a = (fun x y -> mul #a p.[y] (mul (exp omegainv (x*y)) (exp omega (k*x)))) in
  let sk = Seq.map (fun y -> sum_n #a #add_ag.g.m (Seq.map (fun x -> f x y) l)) l in
  let h = ((k-j)%n) in
  let pows = powers #a n (exp omega h) in
  lib_ntt_inversion2_sublemma_kj'_ omega omegainv p k j;
  if(j>k) then (modulo_lemma (j-k) n; assert(h<>0))
  else (modulo_addition_lemma (j-k) 1 n; modulo_lemma ((j-k)+n) n; assert(h<>0));
  assert(h <> 0);
  lemma_exp_exp #a omega h n;
  lemma_exp_exp #a omega n h;
  assert (exp #a (exp omega h) n == exp #a (exp omega n) h);
  lemma_exp_one #a h;
  let o = (exp #a omega h) in
  sum_nth_root_unity_lemma n o;
  assert (sum_n pows == zero);
  lemma_zero_absorb2 #a p.[j]

val lib_ntt_inversion2_sublemma_kk':
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat
  -> omega:a{exp omega n == one}
  -> omegainv:a{mul omegainv omega == one}
  -> p:lib_poly a n
  -> k:nat{k<n}
  -> Lemma(let l = createi n (fun x -> x) in
	  let f : (x:nat{x<n}) -> (y:nat{y<n}) -> a = (fun x y -> mul p.[y] (mul (exp omegainv (x*y)) (exp omega (k*x)))) in
	  let sk' = Seq.map (fun y -> sum_n #a #add_ag.g.m (Seq.map (fun x -> f x y) l)) l in
	  sk'.[k] == mul #a (repeat_plus one n) p.[k])

let lib_ntt_inversion2_sublemma_kk' #a [|ring a|] #n omega omegainv p k =
  let m = (add_ag #a).g.m in
  let l = createi n (fun x -> x) in
  let f : (x:nat{x<n}) -> (y:nat{y<n}) -> a = (fun x y -> mul #a p.[y] (mul (exp omegainv (x*y)) (exp omega (k*x)))) in
  let sk' = Seq.map (fun y -> sum_n #a (Seq.map (fun x -> f x y) l)) l in
  let h = ((k-k)%n) in
  let pows = powers #a n (exp omega ((k-k) % n)) in
  lib_ntt_inversion2_sublemma_kj'_ omega omegainv p k k;
  let customprop' (d:nat{d<n}) : Type0 = (pows.[d] == one #a) in
  let customlemma' (d:nat{d<n}) : Lemma (customprop' d) =
    assert ((k-k)%n = 0);
    lemma_exp_zero #a omega;
    lemma_exp_one #a d
    in
  FStar.Classical.forall_intro customlemma';
  sum_n_all_c_is_repeat_c_n one pows;
  lemma_one1 #a p.[k];
  lemma_one2 #a p.[k];
  lemma_repeat_plus_swap_mul #a one p.[k] n

val lib_ntt_inversion2_lemma_k:
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat
  -> ninv:a{mul ninv (repeat_plus one n) == one}
  -> omega:a{exp omega n == one /\ (forall (nn:nat{nn<n}). (exp omega nn == one ==> nn = 0) /\ (~(is_invertible(minus (exp omega nn) one)) ==> nn = 0))}
  -> omegainv:a{mul omegainv omega == one}
  -> psi:a
  -> psiinv:a{mul psi psiinv == one}
  -> p:lib_poly a n
  -> k:nat{k<n}
  -> Lemma(let p' = lib_ntt omega psi (lib_nttinv ninv omegainv psiinv p) in p'.[k] == p.[k])

let lib_ntt_inversion2_lemma_k #a [| ring a |] #n ninv omega omegainv psi psiinv p k =
  let m = (add_ag #a).g.m in
  let pnttinv = lib_nttinv ninv omegainv psiinv p in
  let p' = lib_ntt omega psi pnttinv in
  let l = createi n (fun x -> x) in
  let s = mapi (fun j g -> mul (exp psi j) (mul g (exp #a omega (k*j)))) pnttinv in
  let f (x:nat{x<n}) (y:nat{y<n}) : a = mul #a p.[y] (mul (exp omegainv (x*y)) (exp omega (k*x))) in
  let sk = Seq.map (fun y -> sum_n (Seq.map (fun x -> f x y) l)) l in
  let customprop (j:nat{j<n}) : Type0 = (s.[j] == mul #a ninv (sum_n (Seq.map (fun y -> f j y) l))) in
  let customlemma (j:nat{j<n}) : Lemma (customprop j) =
    lib_ntt_inversion2_sublemma_kj ninv omega omegainv psi psiinv p k j
  in
  FStar.Classical.forall_intro customlemma;
  eq_intro s (Seq.map (fun z -> mul #a ninv z) (Seq.map (fun x -> sum_n (Seq.map (fun y -> f x y) l)) l));
  eq_elim s (Seq.map (fun z -> mul #a ninv z) (Seq.map (fun x -> sum_n (Seq.map (fun y -> f x y) l)) l));
  sum_n_mul_distrib_l_lemma (Seq.map (fun x -> sum_n (Seq.map (fun y -> f x y) l)) l) ninv;
  assert(p'.[k] == mul #a ninv (sum_n (Seq.map (fun x -> sum_n (Seq.map (fun y -> f x y) l)) l)));
  sum_n_fubini_ring f l l;
  assert(p'.[k] == mul #a ninv (sum_n sk));
  let customprop' (j:nat{j<n /\ j<>k}) : Type0 = sk.[j] == zero #a in
  let customlemma' (j:nat{j<n /\ j<>k}) : Lemma (customprop' j) =
    assert(customprop' j) by apply_lemma (`lib_ntt_inversion2_sublemma_kj')
  in
  FStar.Classical.forall_intro customlemma';
  assert(sum_n sk == sk.[k]) by (apply_lemma(`sum_n_one_non_id_coeff));
  assert(sk.[k] == mul #a (repeat_plus one n) p.[k]) by apply_lemma(`lib_ntt_inversion2_sublemma_kk');
  lemma_mul_assoc #a ninv (repeat_plus one n) p.[k];
  lemma_one1 #a p.[k]

#reset-options "--z3rlimit 500 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"


let lib_ntt_inversion_lemma2 #a [| ring a |] #n ninv omega omegainv psi psiinv p =
  let pnttinv = lib_nttinv ninv omegainv psiinv p in
  let p' = lib_ntt omega psi pnttinv in

  let customprop (k:nat{k<n}) : Type0 = (p'.[k] == p.[k]) in
  let customlemma (k:nat{k<n}) : Lemma (customprop k) =
    lib_ntt_inversion2_lemma_k ninv omega omegainv psi psiinv p k
  in
  FStar.Classical.forall_intro customlemma;
  eq_intro p' p;
  eq_elim p' p

val lemma_ntt_split1even:
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat{n%2 = 0}
  -> omega:a
  -> psi:a
  -> p:lib_poly a n
  -> peven:lib_poly a (n/2)
  -> podd:lib_poly a (n/2)
  -> pseq:lib_poly a n
  -> p1:lib_poly a (n/2)
  -> p2:lib_poly a (n/2)
  -> k:size_nat{k<n/2}
  -> Lemma (requires pseq == lib_ntt_sequence omega psi p k /\ (peven,podd) == split_seq p /\ (p1,p2) == split_seq pseq)
    (ensures (sum_n #a #add_ag.g.m p1 == (lib_ntt (exp omega 2) (exp psi 2) peven).[k]))

let lemma_ntt_split1even #a [|ring a|] #n omega psi p peven podd pseq p1 p2 k =
  let m = (add_ag #a).g.m in
  let omega2 = exp omega 2 in
  let psi2 = exp psi 2 in
  let p1' = lib_ntt_sequence omega2 psi2 peven k in
  let p2' = lib_ntt_sequence omega2 psi2 podd k in
  let customprop1 (i:size_nat{i<n/2}) : Type0 = (p1.[i] == p1'.[i]) in
  let customlemma1 (i:size_nat{i<n/2}) : Lemma (customprop1 i) =
    lib_ntt_sequence_instantiate omega psi p pseq k (2*i);
    assert(p1.[i] == mul #a (exp psi (2*i)) (mul p.[2*i] (exp omega (k*2*i))));
    lemma_exp_exp psi 2 i;
    lemma_exp_exp #a omega 2 (k*i);
    assert(p1.[i] == mul #a (exp psi2 i) (mul p.[2*i] (exp omega2 (k*i))));
    lib_ntt_sequence_instantiate omega2 psi2 peven p1' k i
    in
  FStar.Classical.forall_intro customlemma1;
  eq_intro p1 p1';
  lib_ntt_lemma_instantiate omega2 psi2 peven (lib_ntt (exp omega 2) (exp psi 2) peven) k

val lemma_ntt_split1odd:
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat{n%2 = 0}
  -> omega:a
  -> psi:a
  -> p:lib_poly a n
  -> peven:lib_poly a (n/2)
  -> podd:lib_poly a (n/2)
  -> pseq:lib_poly a n
  -> p1:lib_poly a (n/2)
  -> p2:lib_poly a (n/2)
  -> k:size_nat{k<n/2}
  -> Lemma (requires pseq == lib_ntt_sequence omega psi p k /\ (peven,podd) == split_seq p /\ (p1,p2) == split_seq pseq)
    (ensures (sum_n #a #add_ag.g.m p2 == mul psi (mul (lib_ntt (exp omega 2) (exp psi 2) podd).[k] (exp omega k))))

let lemma_ntt_split1odd #a [|ring a|] #n omega psi p peven podd pseq p1 p2 k =
  let m = (add_ag #a).g.m in
  let omega2 = exp omega 2 in
  let psi2 = exp psi 2 in
  let p1' = lib_ntt_sequence omega2 psi2 peven k in
  let p2' = lib_ntt_sequence omega2 psi2 podd k in
  let customprop2 (i:size_nat{i<n/2}) : Type0 = (p2.[i] == (Seq.map (fun x -> mul psi x) (Seq.map (fun x -> mul #a x (exp omega k)) p2')).[i]) in
  let customlemma2 (i:size_nat{i<n/2}) : Lemma (customprop2 i) =
    lib_ntt_sequence_instantiate omega psi p pseq k (2*i);
    assert(p2.[i] == mul #a (exp psi (2*i+1)) (mul p.[2*i+1] (exp omega (k*(2*i+1)))));
    lemma_exp_succ1 psi (2*i);
    lemma_exp_exp psi 2 i;
    lemma_mul_assoc psi (exp psi2 i) (mul #a p.[2*i+1] (exp omega (k*(2*i+1))));
    assert(p2.[i] == mul #a psi (mul (exp psi2 i) (mul p.[2*i+1] (exp omega (k*(2*i+1))))));
    distributivity_add_right k (2*i) 1;
    lemma_exp_morphism #a omega (k*2*i) k;
    lemma_exp_exp #a omega 2 (k*i);
    lemma_mul_assoc #a p.[2*i+1] (exp omega2 (k*i)) (exp omega k);
    assert(p2.[i] == mul #a psi (mul (exp psi2 i) (mul (mul p.[2*i+1] (exp omega2 (k*i))) (exp omega k))));
    lemma_mul_assoc #a (exp psi2 i) (mul #a p.[2*i+1] (exp omega2 (k*i))) (exp omega k);
    lib_ntt_sequence_instantiate omega2 psi2 podd p2' k i
  in
  FStar.Classical.forall_intro customlemma2;
  eq_intro p2 (Seq.map (fun x -> mul psi x) (Seq.map (fun x -> mul #a x (exp omega k)) p2'));
  sum_n_mul_distrib_l_lemma #a (Seq.map (fun x -> mul #a x (exp omega k)) p2') psi;
  sum_n_mul_distrib_r_lemma #a p2' (exp omega k);
  lib_ntt_lemma_instantiate omega2 psi2 podd (lib_ntt (exp omega 2) (exp psi 2) podd) k


val lemma_ntt_split1:
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat{n%2 = 0}
  -> omega:a
  -> psi:a
  -> p:lib_poly a n
  -> peven:lib_poly a (n/2)
  -> podd:lib_poly a (n/2)
  -> k:size_nat{k<n/2}
  -> Lemma (requires (peven,podd) == split_seq p)
    (ensures (lib_ntt omega psi p).[k] == plus #a (lib_ntt (exp omega 2) (exp psi 2) peven).[k] (mul psi (mul (lib_ntt (exp omega 2) (exp psi 2) podd).[k] (exp omega k))))

let lemma_ntt_split1 #a [| ring a |] #n omega psi p peven podd k =
  let m = (add_ag #a).g.m in
  let p' = lib_ntt omega psi p in
  let omega2 = exp omega 2 in
  let psi2 = exp psi 2 in
  lib_ntt_lemma_instantiate omega psi p p' k;
  let pseq = lib_ntt_sequence omega psi p k in
  let p1,p2 = split_seq pseq in
  let p1' = lib_ntt_sequence omega2 psi2 peven k in
  let p2' = lib_ntt_sequence omega2 psi2 podd k in
  sum_n_split_lemma pseq p1 p2;
  assert(p'.[k] == plus #a (sum_n p1) (sum_n p2));
  lemma_ntt_split1even omega psi p peven podd pseq p1 p2 k;
  lemma_ntt_split1odd omega psi p peven podd pseq p1 p2 k


val lemma_ntt_split2even:
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat{n%2 = 0}
  -> omega:a
  -> psi:a
  -> p:lib_poly a n
  -> peven:lib_poly a (n/2)
  -> podd:lib_poly a (n/2)
  -> pseq:lib_poly a n
  -> p1:lib_poly a (n/2)
  -> p2:lib_poly a (n/2)
  -> k:size_nat{k<n/2}
  -> Lemma (requires exp omega n == one #a /\ pseq == lib_ntt_sequence omega psi p (k+n/2) /\ (peven,podd) == split_seq p /\ (p1,p2) == split_seq pseq)
    (ensures (sum_n #a #add_ag.g.m p1 == (lib_ntt (exp omega 2) (exp psi 2) peven).[k]))

let lemma_ntt_split2even #a [|ring a|] #n omega psi p peven podd pseq p1 p2 k =
  let m = (add_ag #a).g.m in
  let omega2 = exp omega 2 in
  let psi2 = exp psi 2 in
  let p1' = lib_ntt_sequence omega2 psi2 peven k in
  let p2' = lib_ntt_sequence omega2 psi2 podd k in
  let customprop1 (i:size_nat{i<n/2}) : Type0 = (p1.[i] == p1'.[i]) in
  let customlemma1 (i:size_nat{i<n/2}) : Lemma (customprop1 i) =
    lib_ntt_sequence_instantiate omega psi p pseq (k+n/2) (2*i);
    assert(p1.[i] == mul #a (exp psi (2*i)) (mul p.[2*i] (exp omega ((k+n/2)*2*i))));
    distributivity_add_left k (n/2) (2*i);
    lemma_exp_morphism omega (k*2*i) (n/2*2*i);
    div_exact_r n 2;
    assert(p1.[i] == mul #a (exp psi (2*i)) (mul p.[2*i] (mul (exp omega (k*2*i)) (exp omega (n*i)))));
    lemma_exp_exp omega n i;
    lemma_exp_one #a i;
    lemma_one2 (exp omega (k*2*i));
    lemma_exp_exp omega 2 (k*i);
    lemma_exp_exp psi 2 i;
    assert(p1.[i] == mul #a (exp psi2 i) (mul p.[2*i] (exp omega2 (k*i))));
    lib_ntt_sequence_instantiate omega2 psi2 peven p1' k i
    in
  FStar.Classical.forall_intro customlemma1;
  eq_intro p1 p1';
  lib_ntt_lemma_instantiate omega2 psi2 peven (lib_ntt (exp omega 2) (exp psi 2) peven) k

val lemma_ntt_split2odd:
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat{n%2 = 0}
  -> omega:a
  -> psi:a
  -> p:lib_poly a n
  -> peven:lib_poly a (n/2)
  -> podd:lib_poly a (n/2)
  -> pseq:lib_poly a n
  -> p1:lib_poly a (n/2)
  -> p2:lib_poly a (n/2)
  -> k:size_nat{k<n/2}
  -> Lemma (requires exp omega n == one #a /\ pseq == lib_ntt_sequence omega psi p (k+n/2) /\ (peven,podd) == split_seq p /\ (p1,p2) == split_seq pseq)
    (ensures (sum_n #a #add_ag.g.m p2 == mul psi (mul (lib_ntt (exp omega 2) (exp psi 2) podd).[k] (exp omega (k+n/2)))))

#reset-options "--z3rlimit 1000 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"
let sub_lemma_omega #a [|ring a|] (n:size_nat{n%2=0}) (omega:a) (k:nat) (i:nat) : Lemma (requires exp omega n == one #a) (ensures exp omega ((k+n/2)*(2*i+1)) == mul (exp (exp omega 2) (k*i)) (exp omega (k+n/2))) =
  distributivity_add_right (k+n/2) (2*i) 1;
  lemma_exp_morphism #a omega ((k+n/2)*2*i) (k+n/2);
  assert(exp omega ((k+n/2)*(2*i+1)) == mul (exp omega ((k+n/2)*2*i)) (exp omega (k+n/2)));
  distributivity_add_left k (n/2) (2*i);
  lemma_exp_morphism omega (k*2*i) (n/2*2*i);
  assert(exp omega ((k+n/2)*(2*i+1)) == mul (mul (exp omega (k*2*i)) (exp omega (n/2*2*i))) (exp omega (k+n/2)));
  div_exact_r n 2;
  lemma_exp_exp omega n i;
  lemma_exp_one #a i;
  lemma_one2 (exp omega (k*2*i));
  assert(exp omega ((k+n/2)*(2*i+1)) == mul (exp omega (k*2*i)) (exp omega (k+n/2)));
  lemma_exp_exp #a omega 2 (k*i)


let lemma_ntt_split2odd #a [|ring a|] #n omega psi p peven podd pseq p1 p2 k =
  let m = (add_ag #a).g.m in
  let omega2 = exp omega 2 in
  let psi2 = exp psi 2 in
  let p1' = lib_ntt_sequence omega2 psi2 peven k in
  let p2' = lib_ntt_sequence omega2 psi2 podd k in
  let customprop2 (i:size_nat{i<n/2}) : Type0 = (p2.[i] == (Seq.map (fun x -> mul psi x) (Seq.map (fun x -> mul #a x (exp omega (k+n/2))) p2')).[i]) in
  let customlemma2 (i:size_nat{i<n/2}) : Lemma (customprop2 i) =
    lib_ntt_sequence_instantiate omega psi p pseq (k+n/2) (2*i);
    assert(p2.[i] == mul #a (exp psi (2*i+1)) (mul podd.[i] (exp omega ((k+n/2)*(2*i+1)))));
    lemma_exp_succ1 psi (2*i);
    lemma_exp_exp psi 2 i;
    lemma_mul_assoc psi (exp psi2 i) (mul #a podd.[i] (exp omega ((k+n/2)*(2*i+1))));
    assert(p2.[i] == mul #a psi (mul (exp psi2 i) (mul podd.[i] (exp omega ((k+n/2)*(2*i+1))))));
    sub_lemma_omega n omega k i;
    assert(p2.[i] == mul #a psi (mul (exp psi2 i) (mul podd.[i] (mul (exp omega2 (k*i)) (exp omega (k+n/2))))));
    lemma_mul_assoc #a podd.[i] (exp omega2 (k*i)) (exp omega (k+n/2));
    assert(p2.[i] == mul #a psi (mul (exp psi2 i) (mul (mul podd.[i] (exp omega2 (k*i))) (exp omega (k+n/2)))));
    lemma_mul_assoc #a (exp psi2 i) (mul #a podd.[i] (exp omega2 (k*i))) (exp omega (k+n/2));
    assert(p2.[i] == mul #a psi (mul (mul (exp psi2 i) (mul podd.[i] (exp omega2 (k*i)))) (exp omega (k+n/2))));
    lib_ntt_sequence_instantiate omega2 psi2 podd p2' k i
  in
  FStar.Classical.forall_intro customlemma2;
  eq_intro p2 (Seq.map (fun x -> mul psi x) (Seq.map (fun x -> mul #a x (exp omega (k+n/2))) p2'));
  sum_n_mul_distrib_l_lemma #a (Seq.map (fun x -> mul #a x (exp omega (k+n/2))) p2') psi;
  sum_n_mul_distrib_r_lemma #a p2' (exp omega (k+n/2));
  lib_ntt_lemma_instantiate omega2 psi2 podd (lib_ntt (exp omega 2) (exp psi 2) podd) k


val lemma_ntt_split2:
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat{n%2 = 0}
  -> omega:a
  -> psi:a
  -> p:lib_poly a n
  -> peven:lib_poly a (n/2)
  -> podd:lib_poly a (n/2)
  -> k:size_nat{k<n/2}
  -> Lemma (requires exp omega n == one #a /\ (peven,podd) == split_seq p)
    (ensures (lib_ntt omega psi p).[k+n/2] == plus #a (lib_ntt (exp omega 2) (exp psi 2) peven).[k] (mul psi (mul (lib_ntt (exp omega 2) (exp psi 2) podd).[k] (exp omega (k+n/2)))))

let lemma_ntt_split2 #a [| ring a |] #n omega psi p peven podd k =
  let m = (add_ag #a).g.m in
  let p' = lib_ntt omega psi p in
  let omega2 = exp #a omega 2 in
  let psi2 = exp psi 2 in
  lib_ntt_lemma_instantiate omega psi p p' (k+n/2);
  let pseq = lib_ntt_sequence omega psi p (k+n/2) in
  let p1,p2 = split_seq pseq in
  let p1' = lib_ntt_sequence omega2 psi2 peven k in
  let p2' = lib_ntt_sequence omega2 psi2 podd k in
  sum_n_split_lemma pseq p1 p2;
  assert(p'.[k+n/2] == plus #a (sum_n p1) (sum_n p2));
  lemma_ntt_split2even omega psi p peven podd pseq p1 p2 k;
  lemma_ntt_split2odd omega psi p peven podd pseq p1 p2 k
