module Spec.Kyber.NTT

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open FStar.Mul
open FStar.Math.Lemmas
open FStar.Classical
open FStar.Tactics

open Spec.Kyber.Params
open Spec.Kyber.Lemmas
open Spec.Kyber.Poly

open Lib.ModularArithmetic
open Lib.ModularArithmetic.Lemmas
open Lib.Poly.NTT

module Seq = Lib.Sequence
module Loops = Lib.LoopCombinators


type reversed (#m:nat) (a:poly m) = bool
type normal (#m:nat) (a:poly m) = bool

type zq = field params_q
unfold inline_for_extraction 
type nttpoly = p:(poly params_q){reversed p}

unfold inline_for_extraction
type poly  =  p:(poly params_q){normal p}

#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

val lemma_is_prime_params_q: unit -> Lemma (is_prime params_q)

let lemma_is_prime_params_q () =
  let customprop (p:field params_q{p>1}) = (params_q % p <> 0) in
  let f (p:field params_q{p>1}) : Lemma (customprop p) =
    assert(params_q % p <> 0) in
  FStar.Classical.forall_intro f


val ntt:   
  p:poly 
  -> Tot (p':nttpoly{forall (k:nat{k<params_n}). p'.[k] = modular_sum_n (mapi (fun j g -> (params_psi^%j) *% g *% (params_omega ^% (k*j))) p)})

let ntt p = 
  let p': nttpoly = lib_ntt params_omega params_psi p in p'

val nttinv: 
  p:nttpoly 
  -> Tot (p':poly{forall (k:nat{k<params_n}). p'.[k] = params_ninv *% (params_psiinv^%k) *% modular_sum_n (mapi (fun j g -> g *% (params_omegainv ^% (k*j))) p)})

let nttinv p = 
  lemma_is_prime_params_q ();
  let p':poly = lib_nttinv params_ninv params_omegainv params_psiinv p in p'


#reset-options "--z3rlimit 200 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"


let ( ^% ) = modular_exp #params_q

val order_omega: unit -> p:pos{ params_omega ^%p = 1 /\ (forall (nn:field p). params_omega ^% nn = 1 ==> nn = 0)}

let order_omega unit = 
  let rec __aux (counter:nat{counter<params_q-1}) (acc:field params_q{acc = params_omega ^% counter /\ (counter > 0 <==> acc <> 1)}) : Tot (p:pos{ acc *% (params_omega ^% p) = 1 /\ (forall (d:nat{d<p}). (d>0 \/ counter > 0) ==> acc *% (params_omega ^% d) <>1 )}) (decreases (params_q-counter)) =
  if(counter = params_q-2) then begin
    assert (acc = params_omega ^% (params_q-2));
    assert (acc *% params_omega = (params_omega ^% (params_q-2)) *% params_omega);
    modular_exp_lemma_one1 #params_q params_omega;
    modular_exp_morphism_lemma #params_q params_omega (params_q-2) 1;
    assert (acc *% params_omega = params_omega ^% (params_q-1));
    assert_norm(params_omega ^% (params_q-1) = 1);
    acc *% params_omega end
  else if params_omega *% acc = 1 then (modular_exp_lemma_one1 #params_q params_omega; 1)
  else begin
    modular_exp_lemma_one1 #params_q params_omega;
    modular_exp_morphism_lemma #params_q params_omega counter 1;
    assert(acc *% params_omega = params_omega ^% (counter+1));
    let p = __aux (counter+1) (acc *% params_omega) in
    assert ((acc *% params_omega) *% (params_omega ^% p) = 1);
    modular_mul_associativity_lemma acc params_omega (params_omega ^% p);
    assert (acc *% (params_omega *% (params_omega ^% p)) = 1);
    modular_exp_lemma_one1 #params_q params_omega;
    modular_exp_morphism_lemma #params_q params_omega 1 p;
    assert(acc *% (params_omega ^% (p+1)) = 1);
    let customprop (d:nat{d<p+1}) : Type0 = (d>0 \/ counter > 0) ==> acc *% (params_omega ^% d) <> 1 in
    let customlemma (d:nat{d<p+1}) : Lemma (customprop d) =
      if d=0 then 
	if acc = 1 then (assert(counter = 0); ())
	  else (modular_exp_lemma_zero #params_q params_omega; modular_mul_one_lemma #params_q acc; assert (acc *% (params_omega ^% d) = acc); ())
      else
	begin
	calc (==) {
	  acc *% (params_omega ^% d);
	    = {modular_exp_morphism_lemma #params_q params_omega 1 (d-1); ()}
	  acc *% ((params_omega ^% 1) *% (params_omega ^% (d-1)));
	    = {modular_exp_lemma_one1 #params_q params_omega; ()}
	  acc *% (params_omega *% (params_omega ^% (d-1)));
	    = {modular_mul_associativity_lemma acc params_omega (params_omega ^% (d-1))}
	  (acc *% params_omega) *% (params_omega ^% (d-1));
	} end
    in
    FStar.Classical.forall_intro customlemma; p+1
    end
  in
  let p = __aux 0 1 in
  modular_mul_one_lemma (params_omega ^% p);
  assert (params_omega ^% p = 1);
  let prop_p (d:nat{d<p+1}) : Type0 = (forall(d:nat{d<p}). (params_omega ^%d) = 1 ==> d = 0) in
  let lemma_p (d:nat{d<p+1}) : Lemma (prop_p d) =
    modular_mul_one_lemma (params_omega ^% p); () in
  FStar.Classical.forall_intro lemma_p;
  p

val lemma_multiplicative_order_omega: unit -> Lemma (forall (nn:field params_n). params_omega ^% nn = 1 ==> nn = 0)

let lemma_multiplicative_order_omega () =
  assert_norm(order_omega () = params_n); ()
  
val ntt_inversion_lemma: 
 p:poly
 -> Lemma(nttinv (ntt p) == p)


let ntt_inversion_lemma p =
  lemma_is_prime_params_q ();
  assert_norm(modular_exp #params_q params_omega params_n == 1);
  lemma_multiplicative_order_omega ();
  let customprop' (nn:field params_n) : Type0 = (~(is_invertible((params_omega ^% nn) -%1)) ==> nn = 0) in
  let customlemma' (nn:field params_n) : Lemma (customprop' nn) =
    lemma_q_prime_zq_field params_q
     in
  FStar.Classical.forall_intro customlemma';
  lib_ntt_inversion_lemma_with_explicit_inverses params_ninv params_omega params_omegainv params_psi params_psiinv p

    
//val forall_elim: #a:Type0 -> #p: (a -> Type0) -> (squash (forall(y:a). p y)) -> (y:a -> Lemma (p y))
//let forall_elim #a #p s = fun y -> (give_witness_from_squash s; assert(p y))


val poly_modular_mul:

