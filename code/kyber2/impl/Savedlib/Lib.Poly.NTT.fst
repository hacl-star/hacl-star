module Lib.Poly.NTT

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open FStar.Mul
open FStar.Math.Lemmas
open FStar.Classical
open FStar.Tactics

open Lib.ModularArithmetic
open Lib.ModularArithmetic.Lemmas

friend Lib.ModularArithmetic.Lemmas

module Seq = Lib.Sequence
module Loops = Lib.LoopCombinators


#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"


let powers #m n o = 
  createi n (fun i -> o ^% i)


val sum_nth_root_unity_lemma_:  
  #q:nat{q>1} 
  -> n:size_nat
  -> o:field q{o ^% n = 1 /\ o<>1} 
  -> Lemma (modular_sum_n (powers n o) = o *% modular_sum_n (powers n o))

let sum_nth_root_unity_lemma_ #q n o =
  let p = powers n o in
  let s = modular_sum_n p in
  let p' = Seq.map (fun x -> o *% x) p in
  let s' = modular_sum_n p' in
  modular_sum_n_mult_distrib_l_lemma p o;
  assert (s'== o *% s);
  assert (forall(k:nat{k<n-1}). p'.[k] = p.[k+1]);
  assert (forall(k:nat{k<n-1}). (sub p' 0 (n-1)).[k] = (sub p 1 (n-1)).[k]);
  if (n=0) then ()
  else begin
  eq_intro (sub p' 0 (n-1)) (sub p 1 (n-1));
  eq_elim (sub p' 0 (n-1)) (sub p 1 (n-1));
  modular_sum_n_simple_lemma p';
  assert(p'.[n-1] = o ^% n);
  assert(p'.[n-1] = p.[0]);
  calc (==) {
    s';
      = {modular_sum_n_simple_lemma p'}
    modular_sum_n (sub p' 0 (n-1)) +% p'.[n-1];
      = {assert (sub p' 0 (n-1) == sub p 1 (n-1)); ()}
    modular_sum_n (sub p 1 (n-1)) +% p'.[n-1];
      = {assert(p'.[n-1] = p.[0]); ()}
    p.[0] +% modular_sum_n (sub p 1 (n-1));
      = {}
    modular_sum_n p;
      = {}
    s;
    }end


#reset-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"


let sum_nth_root_unity_lemma #q n o =
  let inv = invert_mod (o-%1) in
  let p = powers n o in
  let s = modular_sum_n p in
  let p' = Seq.map (fun x -> o *% x) p in
  let s' = modular_sum_n p' in

  sum_nth_root_unity_lemma_ n o;
  assert (s = modular_mul #q o s);
  modular_mul_one_lemma #q s;
  assert (modular_add #q (modular_mul #q (q-1) s) (modular_mul #q 1 s) = (q-1) *% s +% o *% s);
  modular_mul_add_distrib_lemma #q (q-1) 1 s;
  modular_mul_add_distrib_lemma #q (q-1) o s;
  assert (modular_add #q (q-1) 1 = q % q);
  assert (modular_add #q (q-1) 1 = 0);
  assert (((q-1) +% o ) *% s = 0);
  assert((o -% 1) *% s = 0);
  calc (==) {
    s;
      = {modular_mul_one_lemma #q s}
    1 *% s;
      = {}
    (inv *% (o-%1)) *% s;
      = {modular_mul_associativity_lemma inv (o-%1) s}
    inv *% ((o-%1) *% s);
      = {}
    inv *% 0;
      = {}
    0 % q;
      = {modulo_lemma 0 q}
    0;
  }


#reset-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

  
let lib_ntt #n #m omega psi p = 
  createi n (fun k -> modular_sum_n (mapi (fun j g -> (psi^%j) *% g *% (omega ^% (k*j))) p))
  
let lib_ntt_lemma #n #m omega psi p p' = ()

let lib_nttinv #n #m ninv omegainv psiinv p =
  createi n (fun k -> ninv *% (psiinv^%k) *% modular_sum_n (mapi (fun j g -> g *% (omegainv ^% (k*j))) p))

let lib_nttinv_lemma #n #m ninv omegainv psiinv p p' = ()

#reset-options "--z3rlimit 1000 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"


val lib_ntt_inversion_sublemma_kj: 
  #n:size_nat
  -> #m:nat{m>1}
  -> omega:field m
  -> omegainv : field m
  -> psi:field m 
  -> p:lib_poly n m 
  -> k:nat{k<n}
  -> j:nat{j<n} ->
  Lemma(let pntt = lib_ntt omega psi p in
	let sk = mapi (fun l g -> g *% (omegainv ^% (k*l))) pntt in let l = createi n (fun x -> x) in let f = (fun (x:nat{x<n}) (y:nat{y<n}) -> (psi^%y) *% p.[y] *% ((omega ^% (x*y)) *% (omegainv^%(k*x)))) in sk.[j] = modular_sum_n (Seq.map (fun y -> f j y) l))


let lib_ntt_inversion_sublemma_kj #n #m omega omegainv psi p k j =
  let pntt = lib_ntt omega psi p in
  let sk = mapi (fun l g -> g *% (omegainv ^% (k*l))) pntt in
  let l = createi n (fun x -> x) in
  let f = (fun (x:nat{x<n}) (y:nat{y<n}) -> (psi^%y) *% p.[y] *% ((omega ^% (x*y)) *% (omegainv^%(k*x)))) in
  let s' = mapi (fun i g -> (psi^%i) *% g *% (omega ^% (j*i))) p in
  let s = Seq.map (fun y -> y *% (omegainv ^% (k*j))) s' in
  assert(sk.[j] = pntt.[j] *% (omegainv ^% (k*j)));
  assert(pntt.[j] = modular_sum_n (mapi (fun i g -> (psi^%i) *% g *% (omega ^% (j*i))) p));
  assert(sk.[j] = (modular_sum_n (mapi (fun i g -> (psi^%i) *% g *% (omega ^% (j*i))) p)) *% (omegainv ^% (k*j)));
  modular_sum_n_mult_distrib_r_lemma (mapi (fun i g -> (psi^%i) *% g *% (omega ^% (j*i))) p) (omegainv ^% (k*j));
  assert(sk.[j] = modular_sum_n s);
  assert(forall (d:nat{d<n}). s.[d] = ((psi^%d) *% p.[d] *% (omega ^% (j*d))) *% (omegainv ^% (k*j)));
  let customprop (d:nat{d<n}) : GTot Type0 =
    s.[d] = f j d in
  let customlemma (d:nat{d<n}) : Lemma (customprop d) =
    modular_mul_associativity_lemma ((psi^%d) *% p.[d]) (omega ^% (j*d)) (omegainv ^% (k*j))
  in
  FStar.Classical.forall_intro customlemma;
  eq_intro s (Seq.map (fun y -> f j y) l);
  eq_elim s (Seq.map (fun y -> f j y) l)

#reset-options "--z3rlimit 300 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"
 
val lib_ntt_inversion_sublemma_kjd': 
  #n:size_nat
  -> #m:nat{m>1}
  -> omega:field m{omega ^% n = 1} 
  -> omegainv: field m{omega *% omegainv = 1} 
  -> psi:field m 
  -> p:lib_poly n m 
  -> k:nat{k<n} 
  -> j:nat{j<n} 
  -> d:nat{d<n} 
  -> Lemma(let l = createi n (fun x -> x) in
	  let f = (fun (x:nat{x<n}) (y:nat{y<n}) -> (psi^%y) *% p.[y] *% ((omega ^% (x*y)) *% (omegainv^%(k*x)))) in 
	  let s = Seq.map (fun x -> f x j) l in 
	  s.[d] = (psi^%j) *% p.[j] *% ((omega ^% ((j-k)%n)) ^% d))

let __omega__pows__calc__lemma (#m:nat{m>1}) (n:size_nat) (omega:field m{omega ^% n = 1}) (omegainv: field m{omega *% omegainv = 1}) (k:nat{k<n}) (j:nat{j<k}) : Lemma ((omega^%j) *% (omegainv^%k) = omega ^% ((j-k) % n)) =
  modular_mul_one_lemma (omegainv^%k);
  assert (omegainv^%k = (omegainv ^% k) *% (omega ^% n));
  modular_exp_morphism_lemma omega k (n - k);
  modular_mul_associativity_lemma (omegainv ^% k) (omega ^%k) (omega ^% (n-k));
  modular_exp_lemma_inv omegainv omega k;
  modular_mul_one_lemma (omega^%(n-k));
  modular_exp_morphism_lemma omega j (n-k);
  assert((omega^%j)*%(omegainv^%k) = omega ^% (n-k+j));
  assert(n-k+j = n +(j-k));
  assert(0<=n-k+j /\ n-k+j < n);
  modulo_lemma (n-k+j) n;
  assert((n-k+j) % n = (n+(j-k)) % n);
  lemma_mod_plus (j-k) 1 n;
  assert(n-k+j = (j-k) % n)

#reset-options "--z3rlimit 300 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

let lib_ntt_inversion_sublemma_kjd' #n #m omega omegainv psi p k j d =
  let l = createi n (fun x -> x) in
  let f = (fun (x:nat{x<n}) (y:nat{y<n}) -> (psi^%y) *% p.[y] *% ((omega ^% (x*y)) *% (omegainv^%(k*x)))) in
  let s = Seq.map (fun x -> f x j) l in
  assert(s.[d] = f d j);
  assert(s.[d] = (psi^%j) *% p.[j] *% ((omega ^% (d*j)) *% (omegainv^%(k*d))));
  modular_exp_exp_lemma omega j d;
  modular_exp_exp_lemma omegainv k d;
  modular_exp_lemma_expand (omega ^%j) (omegainv ^% k) d;
  assert(s.[d] = (psi^%j) *% p.[j] *% (((omega ^% (j)) *% (omegainv^%(k))) ^% d));
  if j<k then
    __omega__pows__calc__lemma n omega omegainv k j
  else if j=k then begin
    modular_exp_lemma_inv omega omegainv k;
    modular_exp_lemma_zero omega;
    modulo_lemma (j-k) n
  end
  else begin
    modular_exp_morphism_lemma omega (j-k) k;
    modular_mul_associativity_lemma (omega ^% (j-k)) (omega ^% k) (omegainv ^% k);
    modular_exp_lemma_inv omega omegainv k;
    modular_mul_one_lemma (omega ^% (j-k));
    modulo_lemma (j-k) n
    end



#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val lib_ntt_inversion_sublemma_kj'_: 
  #n:size_nat
  -> #m:nat{m>1} 
  -> omega:field m{omega ^% n = 1} 
  -> omegainv:field m{omega *% omegainv = 1} 
  -> psi:field m 
  -> p:lib_poly n m
  -> k:nat{k<n}
  -> j:nat{j<n} 
  -> Lemma(let l = createi n (fun x -> x) in 
	  let f : field n -> field n -> field m = (fun x y -> (psi^%y) *% p.[y] *% ((omega ^% (x*y)) *% (omegainv^%(k*x)))) in
	  let sk' = Seq.map (fun y -> modular_sum_n (Seq.map (fun x -> f x y) l)) l in
	  let pows = powers n (omega ^% ((j-k)%n)) in 
	  sk'.[j] = ((psi ^%j) *% p.[j]) *% modular_sum_n pows)

let lib_ntt_inversion_sublemma_kj'_ #n #m omega omegainv psi p k j =
  let l = createi n (fun x -> x) in
  let f : field n -> field n -> field m = (fun x y -> (psi^%y) *% p.[y] *% ((omega ^% (x*y)) *% (omegainv^%(k*x)))) in
  let sk' = Seq.map (fun y -> modular_sum_n (Seq.map (fun x -> f x y) l)) l in
  assert (sk'.[j] = modular_sum_n (Seq.map (fun x -> f x j) l));
  let s = Seq.map (fun x -> f x j) l in
  let pows = powers n (omega ^% (j-k) % n) in
  assert (sk'.[j] = modular_sum_n s);
  let customprop (d:nat{d<n}) : Type0 =
    s.[d] = (psi ^%j) *% p.[j] *% pows.[d] in
  let customlemma (d:nat{d<n}) : Lemma (customprop d) =
    lib_ntt_inversion_sublemma_kjd' omega omegainv psi p k j d in
  FStar.Classical.forall_intro customlemma;
  eq_intro s (Seq.map (fun y -> ((psi ^%j) *% p.[j]) *%y) pows);
  eq_elim s (Seq.map (fun y -> ((psi ^%j) *% p.[j]) *%y) pows);
  modular_sum_n_mult_distrib_l_lemma pows ((psi ^%j) *% p.[j]);  
  assert( modular_sum_n s = ((psi ^%j) *% p.[j]) *% modular_sum_n pows);
  assert(sk'.[j] = ((psi ^%j) *% p.[j]) *% modular_sum_n pows)

#reset-options "--z3rlimit 300 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

val lib_ntt_inversion_sublemma_kj': 
  #n:size_nat
  -> #m:nat{m>1} 
  -> omega:field m{omega ^% n = 1 /\ (forall (nn:field n). (omega ^% nn = 1 ==> nn = 0) /\ (~(is_invertible((omega ^% nn) -%1)) ==> nn = 0))} 
  -> omegainv:field m{omega *% omegainv = 1} 
  -> psi:field m
  -> p:lib_poly n m
  -> k:nat{k<n} 
  -> j:nat{j<n /\ j <>k} 
  -> Lemma(let l = createi n (fun x -> x) in
	  let f : field n -> field n -> field m = (fun x y -> (psi^%y) *% p.[y] *% ((omega ^% (x*y)) *% (omegainv^%(k*x)))) in 
	  let sk' = Seq.map (fun y -> modular_sum_n (Seq.map (fun x -> f x y) l)) l in 
	  let pows = powers n (omega ^% ((j-k)%n)) in
	  sk'.[j] = 0)

let lib_ntt_inversion_sublemma_kj' #n #m omega omegainv psi p k j =
    let l = createi n (fun x -> x) in
    let f : field n -> field n -> field m = (fun x y -> (psi^%y) *% p.[y] *% ((omega ^% (x*y)) *% (omegainv^%(k*x)))) in
    let sk' = Seq.map (fun y -> modular_sum_n (Seq.map (fun x -> f x y) l)) l in
    let h = ((j-k)%n) in
    let pows = powers n (omega ^% (j-k) % n) in
    lib_ntt_inversion_sublemma_kj'_ omega omegainv psi p k j;
    if(j>k) then (modulo_lemma (j-k) n; assert(h<>0))
    else (modulo_addition_lemma (j-k) 1 n; modulo_lemma (n+(j-k)) n; assert(h<>0));
    assert(h <> 0);
    modular_exp_exp_lemma omega h n;
    modular_exp_exp_lemma omega n h;
    assert ((omega ^% h) ^% n = (omega ^% n) ^% h);
    modular_exp_lemma_one2 #m h;
    let o = (omega ^% h) in    
    sum_nth_root_unity_lemma n o;
    assert (modular_sum_n pows = 0);
    assert (sk'.[j] = (((psi ^%j) *% p.[j]) * 0) % m);
    assert(((psi ^%j) *% p.[j]) * 0 = 0);
    assert(sk'.[j] = 0 % m);
    modulo_lemma 0 m;
    assert(sk'.[j] = 0)
    

#reset-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val lib_ntt_inversion_sublemma_kk': 
  #n:size_nat
  -> #m:nat{m>n /\ m>1}
  -> omega:field m{omega ^% n = 1} 
  -> omegainv:field m{omega *% omegainv = 1} 
  -> psi:field m 
  -> p:lib_poly n m 
  -> k:nat{k<n}
  -> Lemma(let l = createi n (fun x -> x) in 
	  let f : field n -> field n -> field m = (fun x y -> (psi^%y) *% p.[y] *% ((omega ^% (x*y)) *% (omegainv^%(k*x)))) in
	  let sk' = Seq.map (fun y -> modular_sum_n (Seq.map (fun x -> f x y) l)) l in
	  sk'.[k] = ((psi ^% k) *% p.[k]) *% n)

let lib_ntt_inversion_sublemma_kk' #n #m omega omegainv psi p k = 
  let l = createi n (fun x -> x) in
  let f : field n -> field n -> field m = (fun x y -> (psi^%y) *% p.[y] *% ((omega ^% (x*y)) *% (omegainv^%(k*x)))) in
  let sk' = Seq.map (fun y -> modular_sum_n (Seq.map (fun x -> f x y) l)) l in
  let h = ((k-k)%n) in
  let pows = powers n (omega ^% ((k-k) % n)) in
  lib_ntt_inversion_sublemma_kj'_ omega omegainv psi p k k;
  let customprop' (d:field n) : Type0 = (pows.[d] = 1) in
  let customlemma' (d:field n) : Lemma (customprop' d) =
    assert ((k-k)%n = 0);
    modular_exp_lemma_zero omega;
    modular_exp_lemma_one2 #m d
  in  
  FStar.Classical.forall_intro customlemma';
  modular_sum_n_all_1_is_n_mod_q pows;
  modulo_lemma n m;
  assert(sk'.[k] = ((psi ^%k) *% p.[k]) *% n)


#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"


val fubini: 
  #n:size_nat
  -> #m:pos 
  -> f:(field n -> field n -> field m) 
  -> l:set n n 
  -> Lemma (modular_sum_n (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) l)) l) = modular_sum_n (Seq.map (fun y -> modular_sum_n (Seq.map (fun x -> f x y) l)) l))

let fubini #n #m f l =
  modular_fubini_lemma f l l (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) l)) l) (Seq.map (fun y -> modular_sum_n (Seq.map (fun x -> f x y) l)) l)

#reset-options "--z3rlimit 500 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"
 
open FStar.Tactics

val lib_ntt_inversion_fubini_k: 
  #n:size_nat
  -> #m:nat{m>n}
  -> ninv: field m{n *% ninv = 1}
  -> omega:field m
  -> omegainv:field m{omega *% omegainv = 1} 
  -> psi:field m 
  -> psiinv:field m{psi *% psiinv = 1} 
  -> p:lib_poly n m 
  -> k:nat{k<n} 
  -> Lemma(let p' = lib_nttinv ninv omegainv psiinv (lib_ntt omega psi p) in
	  let l = createi n (fun x -> x) in
	  let f (x:nat{x<n}) (y:nat{y<n}) : field m = (psi^%y) *% p.[y] *% ((omega ^% (x*y)) *% (omegainv^%(k*x))) in
	  let sk' = Seq.map (fun y -> modular_sum_n (Seq.map (fun x -> f x y) l)) l in
	  p'.[k] = (ninv *% (psiinv ^% k)) *% modular_sum_n sk')


let lib_ntt_inversion_fubini_k #n #m ninv omega omegainv psi psiinv p k =
  let pntt = lib_ntt omega psi p in
  let p' = lib_nttinv ninv omegainv psiinv pntt in
  assert(p'.[k] = (ninv *% (psiinv^%k)) *% modular_sum_n (mapi (fun j g -> g *% (omegainv ^% (k*j))) pntt));
  let l = createi n (fun x -> x) in
  let f (x:nat{x<n}) (y:nat{y<n}) : field m = (psi^%y) *% p.[y] *% ((omega ^% (x*y)) *% (omegainv^%(k*x))) in
  let sk = mapi (fun j g -> g *% (omegainv ^% (k*j))) pntt in
  let sk' = Seq.map (fun y -> modular_sum_n (Seq.map (fun x -> f x y) l)) l in  
  
  assert(p'.[k] = (ninv *% (psiinv^%k)) *% modular_sum_n sk);
  let customprop (j:nat{j<n}) : GTot Type0 =
    sk.[j] = modular_sum_n (Seq.map (fun y -> f j y) l) in
  let customlemma (j:nat{j<n}) : Lemma (customprop j) =
    lib_ntt_inversion_sublemma_kj omega omegainv psi p k j in
  FStar.Classical.forall_intro customlemma;
  eq_intro sk (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) l)) l);
  eq_elim sk (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) l)) l);
  assert(p'.[k] = (ninv *% (psiinv^%k)) *% modular_sum_n (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) l)) l));
  assert(modular_sum_n (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) l)) l) = modular_sum_n (Seq.map (fun y -> modular_sum_n (Seq.map (fun x -> f x y) l)) l)) by
   (apply_lemma (`fubini));
  assert (p'.[k] = modular_mul #m (ninv *% (psiinv^%k)) (modular_sum_n sk'))
  

#reset-options "--z3rlimit 3000 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

let __dummy_lemma (#m:nat{m>1}) (p:field m) (a:field m) (b:field m{p = a *% b}) (c:field m{c = b}) : Lemma (p = a *% c) = ()

#reset-options "--z3rlimit 500 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val lib_ntt_inversion_lemma_k_: 
  #n:size_nat
  -> #m:nat{m>n}
  -> ninv: field m{n *% ninv = 1}
  -> omega:field m{omega ^% n = 1 /\ (forall (nn:field n). (omega ^% nn = 1 ==> nn = 0) /\ (~(is_invertible((omega ^% nn) -%1)) ==> nn = 0))} 
  -> omegainv:field m{omega *% omegainv = 1} 
  -> psi:field m 
  -> psiinv:field m{psi *% psiinv = 1} 
  -> p:lib_poly n m 
  -> k:nat{k<n} 
  -> Lemma(let p' = lib_nttinv ninv omegainv psiinv (lib_ntt omega psi p) in p'.[k] = (ninv *% (psiinv ^% k)) *% (((psi ^%k) *% p.[k]) *% n))


let lib_ntt_inversion_lemma_k_ #n #m ninv omega omegainv psi psiinv p k =
  let p' = lib_nttinv ninv omegainv psiinv (lib_ntt omega psi p) in
  let l = createi n (fun x -> x) in
  let f (x:nat{x<n}) (y:nat{y<n}) : field m = (psi^%y) *% p.[y] *% ((omega ^% (x*y)) *% (omegainv^%(k*x))) in
  let sk' = Seq.map (fun y -> modular_sum_n (Seq.map (fun x -> f x y) l)) l in  

  lib_ntt_inversion_fubini_k ninv omega omegainv psi psiinv p k;
  let customprop' (j:nat{j<n /\ j<>k}) : Type0 =
    sk'.[j] = 0 in
  let customlemma' (j:nat{j<n /\ j<>k}) : Lemma (customprop' j) =
    assert(customprop' j) by (apply_lemma (`lib_ntt_inversion_sublemma_kj'))
  in 
  FStar.Classical.forall_intro customlemma';
  assert(modular_sum_n sk' = sk'.[k]) by (apply_lemma(`modular_sum_n_one_non_zero_coeff));
  __dummy_lemma p'.[k] (ninv *% (psiinv^%k)) (modular_sum_n sk') sk'.[k];
  assert (p'.[k] = (ninv *% (psiinv ^%k)) *% sk'.[k]);
  assert(sk'.[k] = (((psi ^%k) *% p.[k]) *% n)) by (apply_lemma(`lib_ntt_inversion_sublemma_kk'));
  __dummy_lemma p'.[k] (ninv *% (psiinv^%k)) sk'.[k] (((psi ^%k) *% p.[k]) *% n)

#reset-options "--z3rlimit 500 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val lib_ntt_inversion_lemma_k: 
  #n:size_nat
  -> #m:nat{m>n}
  -> ninv:field m{n *% ninv = 1}
  -> omega:field m{omega ^% n = 1 /\ (forall (nn:field n). (omega ^% nn = 1 ==> nn = 0) /\ (~(is_invertible((omega ^% nn) -%1)) ==> nn = 0))} 
  -> omegainv:field m{omega *% omegainv = 1} 
  -> psi:field m 
  -> psiinv:field m{psi *% psiinv = 1} 
  -> p:lib_poly n m 
  -> k:nat{k<n} 
  -> Lemma(let p' = lib_nttinv ninv omegainv psiinv (lib_ntt omega psi p) in p'.[k] = p.[k])

let __calc__lemma (n:size_nat) (#m:nat{m>n}) (ninv:field m{n *% ninv = 1}) (omega:field m) (psi:field m) (psiinv:field m{psi *% psiinv = 1}) (k:nat) (x:field m) : Lemma ((ninv *% (psiinv^%k)) *% (((psi ^%k) *% x) *% n) = x) =
  calc (==) {
    (ninv *% (psiinv^%k)) *% (((psi ^%k) *% x) *% n);
      = {}
    ((psiinv^%k) *% ninv) *% (n *% ((psi ^%k) *% x));
      = {modular_mul_associativity_lemma (psiinv ^%k) ninv (n *% ((psi ^%k) *% x))}
    (psiinv^%k) *% (ninv *% (n *% ((psi ^%k) *% x)));
      = {modular_mul_associativity_lemma ninv n ((psi ^%k) *% x); ()}
    (psiinv^%k) *% ((ninv *% n) *% ((psi ^%k) *% x));
      = {modular_mul_one_lemma ((psi ^% k) *% x)}
    (psiinv ^%k) *% ((psi ^% k) *% x);
      = {modular_mul_associativity_lemma (psiinv ^%k) (psi ^%k) x}
    ((psiinv ^%k) *% (psi ^% k)) *% x;
      = {modular_mul_one_lemma x}
    x;
  }

#reset-options "--z3rlimit 500 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

let lib_ntt_inversion_lemma_k #n #m ninv omega omegainv psi psiinv p k =
  let p' = lib_nttinv ninv omegainv psiinv (lib_ntt omega psi p) in
  assert(p'.[k] = (ninv *% (psiinv^%k)) *% (((psi ^%k) *% p.[k]) *% n)) by (apply_lemma (`lib_ntt_inversion_lemma_k_));
  __calc__lemma n ninv omega psi psiinv k p.[k]
  
#reset-options "--z3rlimit 500 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"


let lib_ntt_inversion_lemma_with_explicit_inverses #n #m ninv omega omegainv psi psiinv p =
  let pntt = lib_ntt omega psi p in
  let p' = lib_nttinv ninv omegainv psiinv pntt in

  let customprop (k:nat{k<n}) : Type0 = (p'.[k] = p.[k]) in
  let customlemma (k:nat{k<n}) : Lemma (customprop k) =
    lib_ntt_inversion_lemma_k ninv omega omegainv psi psiinv p k
  in
  FStar.Classical.forall_intro customlemma;
  eq_intro p' p;
  eq_elim p' p


let lib_ntt_inversion_lemma #n #m omega psi p =
  lib_ntt_inversion_lemma_with_explicit_inverses (invert_mod #m n) omega (invert_mod omega) psi (invert_mod psi) p


val lib_poly_modular_add:
  #n:size_nat
  -> #m:nat
  -> p1:lib_poly n m
  -> p2:lib_poly n m
  -> Tot (p:lib_poly n m{forall (k:nat). k<n ==> p.[k] = p1.[k] +% p2.[k]})

let lib_poly_modular_add #n #m p1 p2 =
  Seq.map2 (+%) p1 p2 

val lib_poly_naive_modular_mul:
  #n:size_nat
  -> #m:pos
  -> p1:lib_poly n m
  -> p2:lib_poly n m
  -> Tot (p:lib_poly n m{forall (k:nat). k < n ==> (let lk = createi (k+1) (fun x -> x) in let f = fun (i:field (k+1)) -> (p1.[i] *% p2.[k-i]) in p.[k] = modular_sum_n (Seq.map f lk))})

let lib_poly_naive_modular_mul #n #m p1 p2 =
  Seq.createi n (fun (k:field n) -> (let lk = createi (k+1) (fun x -> x) in let f = fun (i:field (k+1)) -> (p1.[i] *% p2.[k-i]) in modular_sum_n (Seq.map f lk)))


val lib_poly_pointwise_modular_mul:
  #n:size_nat
  -> #m:nat
  -> p1:lib_poly n m
  -> p2:lib_poly n m
  -> Tot (p:lib_poly n m{forall (k:nat). k < n ==> p.[k] = p1.[k] *% p2.[k]})

let lib_poly_pointwise_modular_mul #n #m p1 p2 =
  Seq.map2 ( *% ) p1 p2
(*
val lemma_multiply_using_ntt:
  #n:size_nat
  -> #m:nat{m>1}
  -> omega:field m
  -> psi:field m
  -> p1:lib_poly n m
  -> p2:lib_poly n m
  -> Lemma (lib_ntt omega psi (lib_poly_naive_modular_mul p1 p2) == lib_poly_pointwise_modular_mul (lib_ntt omega psi p1) (lib_ntt omega psi p2))

let lemma_multiply_using_ntt_kj #n #m omega psi p1 p2 k j =
  let p = lib_poly_naive_modular_mul p1 p2 in
  let p' = lib_ntt omega psi p in
  
  let p1' = lib_ntt omega psi p1 in
  let p2' = lib_ntt omega psi p2 in
  let s = (mapi (fun j g -> (psi^%j) *% g *% (omega ^% (k*j))) p) in
  assert(s.[j] = (psi^%j) *% p.[j] *% (omega ^% (k*j)))


let lemma_multiply_using_ntt_k #n #m omega psi p1 p2 k =
  let p = lib_poly_naive_modular_mul p1 p2 in
  let p' = lib_ntt omega psi p in
  
  let p1' = lib_ntt omega psi p1 in
  let p2' = lib_ntt omega psi p2 in
  let s = (mapi (fun j g -> (psi^%j) *% g *% (omega ^% (k*j))) p) in
  
  

let lemma_multiply_using_ntt #n #m omega psi p1 p2 =
  let p = lib_poly_naive_modular_mul p1 p2 in
  let p' = lib_ntt omega psi p in
  
  let p1' = lib_ntt omega psi p1 in
  let p2' = lib_ntt omega psi p2 in
  assert(forall (k:nat{k<n}). p'.[k] = modular_sum_n (mapi (fun j g -> (psi^%j) *% g *% (omega ^% (k*j))) p));
  let s = (mapi (fun j g -> (psi^%j) *% g *% (omega ^% (k*j))) p) in
  admit()
