module Spec.Kyber2.NTT

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open FStar.Mul
open FStar.Math.Lemmas
open FStar.Classical
open FStar.Tactics

open Spec.Kyber2.Params
open Spec.Kyber2.Lemmas
open Spec.Kyber2.Poly

open Lib.ModularArithmetic
open Lib.ModularArithmetic.Lemmas
open Lib.Poly.NTT2

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

(** continue here tomorrow *)

val ntt:
  p:poly
  -> Tot (p':nttpoly)

let ntt p =
  let p': nttpoly = lib_ntt params_zeta p in p'

val nttinv:
  p:nttpoly
  -> Tot (p':poly)

let nttinv p =
  let p':poly = lib_nttinv params_halfninv params_zetainv p in p'



#reset-options "--z3rlimit 200 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"


let ( ^% ) = modular_exp #params_q


val order_zeta: unit -> p:pos{ params_zeta ^%p = 1 /\ (forall (nn:field p). params_zeta ^% nn = 1 ==> nn = 0)}

let order_zeta unit =
  let rec __aux (counter:nat{counter<params_q-1}) (acc:field params_q{acc = params_zeta ^% counter /\ (counter > 0 <==> acc <> 1)}) : Tot (p:pos{ acc *% (params_zeta ^% p) = 1 /\ (forall (d:nat{d<p}). (d>0 \/ counter > 0) ==> acc *% (params_zeta ^% d) <>1 )}) (decreases (params_q-counter)) =
  if(counter = params_q-2) then begin
    assert (acc = params_zeta ^% (params_q-2));
    assert (acc *% params_zeta = (params_zeta ^% (params_q-2)) *% params_zeta);
    modular_exp_lemma_one1 #params_q params_zeta;
    modular_exp_morphism_lemma #params_q params_zeta (params_q-2) 1;
    assert (acc *% params_zeta = params_zeta ^% (params_q-1));
    assert_norm(params_zeta ^% (params_q-1) = 1);
    acc *% params_zeta end
  else if params_zeta *% acc = 1 then (modular_exp_lemma_one1 #params_q params_zeta; 1)
  else begin
    modular_exp_lemma_one1 #params_q params_zeta;
    modular_exp_morphism_lemma #params_q params_zeta counter 1;
    assert(acc *% params_zeta = params_zeta ^% (counter+1));
    let p = __aux (counter+1) (acc *% params_zeta) in
    assert ((acc *% params_zeta) *% (params_zeta ^% p) = 1);
    modular_mul_associativity_lemma acc params_zeta (params_zeta ^% p);
    assert (acc *% (params_zeta *% (params_zeta ^% p)) = 1);
    modular_exp_lemma_one1 #params_q params_zeta;
    modular_exp_morphism_lemma #params_q params_zeta 1 p;
    assert(acc *% (params_zeta ^% (p+1)) = 1);
    let customprop (d:nat{d<p+1}) : Type0 = (d>0 \/ counter > 0) ==> acc *% (params_zeta ^% d) <> 1 in
    let customlemma (d:nat{d<p+1}) : Lemma (customprop d) =
      if d=0 then 
	if acc = 1 then (assert(counter = 0); ())
	  else (modular_exp_lemma_zero #params_q params_zeta; modular_mul_one_lemma #params_q acc; assert (acc *% (params_zeta ^% d) = acc); ())
      else
	begin
	calc (==) {
	  acc *% (params_zeta ^% d);
	    = {modular_exp_morphism_lemma #params_q params_zeta 1 (d-1); ()}
	  acc *% ((params_zeta ^% 1) *% (params_zeta ^% (d-1)));
	    = {modular_exp_lemma_one1 #params_q params_zeta; ()}
	  acc *% (params_zeta *% (params_zeta ^% (d-1)));
	    = {modular_mul_associativity_lemma acc params_zeta (params_zeta ^% (d-1))}
	  (acc *% params_zeta) *% (params_zeta ^% (d-1));
	} end
    in
    FStar.Classical.forall_intro customlemma; p+1
    end
  in
  let p = __aux 0 1 in
  modular_mul_one_lemma (params_zeta ^% p);
  assert (params_zeta ^% p = 1);
  let prop_p (d:nat{d<p+1}) : Type0 = (forall(d:nat{d<p}). (params_zeta ^%d) = 1 ==> d = 0) in
  let lemma_p (d:nat{d<p+1}) : Lemma (prop_p d) =
    modular_mul_one_lemma (params_zeta ^% p); () in
  FStar.Classical.forall_intro lemma_p;
  p

val lemma_multiplicative_order_zeta: unit -> Lemma (forall (nn:field (params_n)). params_zeta ^% nn = 1 ==> nn = 0)

let lemma_multiplicative_order_zeta () =
  assert_norm(order_zeta () = params_n); ()



#reset-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"
val ntt_inversion_lemma: 
 p:poly
 -> Lemma(nttinv (ntt p) == p)

let ntt_inversion_lemma p =
  lemma_is_prime_params_q ();
  assert_norm(order_zeta () = params_n);
  lemma_multiplicative_order_zeta ();
  let customprop' (nn:field (params_n)) : Type0 = (~(is_invertible((params_zeta ^% nn) -%1)) ==> nn = 0) in
  let customlemma' (nn:field (params_n)) : Lemma (customprop' nn) =
     lemma_q_prime_zq_field params_q
     in
  FStar.Classical.forall_intro customlemma';
  lib_ntt_inversion_lemma_with_explicit_inverses params_halfninv params_zeta params_zetainv p


//val forall_elim: #a:Type0 -> #p: (a -> Type0) -> (squash (forall(y:a). p y)) -> (y:a -> Lemma (p y))
//let forall_elim #a #p s = fun y -> (give_witness_from_squash s; assert(p y))

