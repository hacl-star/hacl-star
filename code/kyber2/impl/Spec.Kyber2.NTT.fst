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

type zq = field params_q
let ring_zq = Lib.Arithmetic.Ring.ring_mod #params_q

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
  -> Tot (p':poly)

let ntt p =
  let p': poly = lib_ntt #Spec.Kyber2.Group.t #Spec.Kyber2.Ring.ring_t #params_n 7 (i16 params_zeta) p in p'

val nttinv:
  p:poly
  -> Tot (p':poly)

let nttinv p =
  let p':poly = lib_nttinv #Spec.Kyber2.Group.t #Spec.Kyber2.Ring.ring_t #params_n 7 (i16 params_halfninv) (i16 params_zetainv) p in p'



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

val lemma_multiplicative_order_params_zeta: unit -> Lemma (forall (nn:nat{nn<params_n}). params_zeta ^% nn = 1 ==> nn = 0)

let lemma_multiplicative_order_params_zeta () =
  assert_norm(order_zeta () = params_n); ()

let exp_t = Lib.Arithmetic.Ring.exp #Group.t #Ring.ring_t

let rec exp_correspondancy (a:Group.t) (n:nat) : Lemma (ensures Group.v (exp_t a n) == (Group.v a) ^% n) (decreases n) =
  if n = 0 then Lib.Arithmetic.Ring.lemma_exp_zero #Group.t #Ring.ring_t a
  else (Lib.Arithmetic.Ring.lemma_exp_succ1 #Group.t #Ring.ring_t a (n-1); Group.mul_lemma_t a (exp_t a (n-1)); exp_correspondancy a (n-1))

let repeat_plus_t = Lib.Arithmetic.Ring.repeat_plus #Group.t #Ring.ring_t
let repeat_plus_zq = Lib.Arithmetic.Ring.repeat_plus #(field params_q) #(Lib.Arithmetic.Ring.ring_mod #params_q)

let rec repeat_plus_correspondancy (a:Group.t) (n:nat) : Lemma (ensures Group.v (repeat_plus_t a n) == repeat_plus_zq (Group.v a) n) (decreases n) =
  if n = 0 then (Lib.Arithmetic.Group.lemma_repeat_op_zero #Group.t #(Group.monoid_plus_t) a; Lib.Arithmetic.Group.lemma_repeat_op_zero #(field params_q) #(Lib.Arithmetic.Group.monoid_plus_mod #params_q) (Group.v a))
  else (Lib.Arithmetic.Group.lemma_repeat_op_succ1 #Group.t #Group.monoid_plus_t a (n-1); Lib.Arithmetic.Group.lemma_repeat_op_succ1 #(field params_q) #(Lib.Arithmetic.Group.monoid_plus_mod #params_q) (Group.v a) (n-1); Group.plus_lemma_t a (repeat_plus_t a (n-1)); repeat_plus_correspondancy a (n-1))

val lemma_multiplicative_order_zeta: unit -> Lemma (forall (nn:nat{nn<params_n}). exp_t (Group.mk_t params_zeta) nn == Group.one_t ==> nn = 0)

let lemma_multiplicative_order_zeta () =
  let customprop (nn:nat{nn<params_n}) : Type0 = (exp_t (Group.mk_t params_zeta) nn == Group.one_t ==> nn = 0) in
  let customlemma (nn:nat{nn<params_n}) : Lemma (customprop nn) =
    exp_correspondancy (Group.mk_t params_zeta) nn;
    lemma_multiplicative_order_params_zeta ()
  in FStar.Classical.forall_intro customlemma

#reset-options "--z3rlimit 500 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

val lemma_is_invertible_implication : (a:Group.t) -> Lemma (requires ~(Lib.Arithmetic.Ring.is_invertible #Group.t #Ring.ring_t a)) (ensures ~(is_invertible #params_q (Group.v a)))

let lemma_is_invertible_implication a =
  let customprop (y:field params_q) : Type0 = (~((Group.v a) *% y = 1)) in
  let customlemma (y:field params_q) : Lemma (customprop y) =
    if((Group.v a) *% y = 1) then (Group.mul_lemma_t a (Group.mk_t y); Ring.lemma_mul_swap_t a (Group.mk_t y); assert(Group.mul_t a (Group.mk_t y) == Group.one_t /\ Group.mul_t (Group.mk_t y) a == Group.one_t); FStar.Classical.exists_intro (fun y -> Group.mul_t a y == Group.one_t) (Group.mk_t y)) else () in
  FStar.Classical.forall_intro customlemma

  #reset-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"
val ntt_inversion_lemma1:
 p:poly
 -> Lemma(nttinv (ntt p) == p)

let ntt_inversion_lemma1 p =
  lemma_is_prime_params_q ();
  assert_norm(order_zeta () = params_n);
  lemma_multiplicative_order_params_zeta ();
  let customprop' (nn:field (params_n)) : Type0 = (~(Lib.Arithmetic.Ring.is_invertible #Group.t #Ring.ring_t (Lib.Arithmetic.Ring.minus #Group.t #Ring.ring_t (exp_t (Group.mk_t params_zeta) nn) Group.one_t)) ==> nn = 0) in
  let customlemma' (nn:field (params_n)) : Lemma (customprop' nn) =
     exp_correspondancy (Group.mk_t params_zeta) nn;
     Ring.minus_lemma_t (exp_t (Group.mk_t params_zeta) nn) Group.one_t;
     assert(Group.v (Lib.Arithmetic.Ring.minus #Group.t #Ring.ring_t (exp_t (Group.mk_t params_zeta) nn) Group.one_t) == (params_zeta ^% nn) -% 1);
     FStar.Classical.move_requires lemma_is_invertible_implication (Lib.Arithmetic.Ring.minus #Group.t #Ring.ring_t (exp_t (Group.mk_t params_zeta) nn) Group.one_t);
     assert(~(Lib.Arithmetic.Ring.is_invertible #Group.t #Ring.ring_t (Lib.Arithmetic.Ring.minus #Group.t #Ring.ring_t (exp_t (Group.mk_t params_zeta) nn) Group.one_t)) ==> ~(is_invertible #params_q ((params_zeta ^% nn) -% 1)));
     lemma_q_prime_zq_field params_q
     in
  FStar.Classical.forall_intro customlemma';
  assert_norm (repeat_plus_zq 1 (params_n/2) == params_n/2);
  repeat_plus_correspondancy Group.one_t (params_n/2);
  shift_right_lemma (Group.mk_t params_n) (size 1);
  assert(params_halfninv *% repeat_plus_zq 1 (params_n/2) = 1);
  Group.mul_lemma_t (Group.mk_t params_halfninv) (repeat_plus_t Group.one_t (params_n/2));
  assert(Group.mul_t (Group.mk_t params_halfninv) (repeat_plus_t Group.one_t (params_n/2)) == Group.one_t);
  lemma_multiplicative_order_zeta ();
  Group.mul_lemma_t (Group.mk_t params_zeta) (Group.mk_t params_zetainv);
  Ring.lemma_mul_swap_t (Group.mk_t params_zeta) (Group.mk_t params_zetainv);
  assert(op_Star_Percent #params_q params_zeta params_zetainv = 1);

  assert(Lib.Arithmetic.Ring.mul #Group.t #Ring.ring_t (Group.mk_t params_halfninv) (Lib.Arithmetic.Ring.repeat_plus #Group.t #Ring.ring_t (Lib.Arithmetic.Ring.one #Group.t #Ring.ring_t) (params_n/2)) == Lib.Arithmetic.Ring.one #Group.t #Ring.ring_t);
  exp_correspondancy (Group.mk_t params_zeta) params_n;
  assert(Lib.Arithmetic.Ring.exp #Group.t #Ring.ring_t (Group.mk_t params_zeta) params_n == Lib.Arithmetic.Ring.one #Group.t #Ring.ring_t);
  assert_norm(Lib.Poly.NTT.lib_poly Group.t params_n == poly);
  let coerce #a #b (x:a) : Pure b (requires a == b) (ensures fun _ -> True) = x in
  lib_ntt_inversion_lemma1 #Group.t #Ring.ring_t #params_n 7 (Group.mk_t params_halfninv) (Group.mk_t params_zeta) (Group.mk_t params_zetainv) (coerce p)

val ntt_inversion_lemma2:
 p:poly
 -> Lemma(ntt (nttinv p) == p)

let ntt_inversion_lemma2 p =
  lemma_is_prime_params_q ();
  assert_norm(order_zeta () = params_n);
  lemma_multiplicative_order_params_zeta ();
  let customprop' (nn:field (params_n)) : Type0 = (~(Lib.Arithmetic.Ring.is_invertible #Group.t #Ring.ring_t (Lib.Arithmetic.Ring.minus #Group.t #Ring.ring_t (exp_t (Group.mk_t params_zeta) nn) Group.one_t)) ==> nn = 0) in
  let customlemma' (nn:field (params_n)) : Lemma (customprop' nn) =
     exp_correspondancy (Group.mk_t params_zeta) nn;
     Ring.minus_lemma_t (exp_t (Group.mk_t params_zeta) nn) Group.one_t;
     assert(Group.v (Lib.Arithmetic.Ring.minus #Group.t #Ring.ring_t (exp_t (Group.mk_t params_zeta) nn) Group.one_t) == (params_zeta ^% nn) -% 1);
     FStar.Classical.move_requires lemma_is_invertible_implication (Lib.Arithmetic.Ring.minus #Group.t #Ring.ring_t (exp_t (Group.mk_t params_zeta) nn) Group.one_t);
     assert(~(Lib.Arithmetic.Ring.is_invertible #Group.t #Ring.ring_t (Lib.Arithmetic.Ring.minus #Group.t #Ring.ring_t (exp_t (Group.mk_t params_zeta) nn) Group.one_t)) ==> ~(is_invertible #params_q ((params_zeta ^% nn) -% 1)));
     lemma_q_prime_zq_field params_q
     in
  FStar.Classical.forall_intro customlemma';
  assert_norm (repeat_plus_zq 1 (params_n/2) == params_n/2);
  repeat_plus_correspondancy Group.one_t (params_n/2);
  shift_right_lemma (Group.mk_t params_n) (size 1);
  assert(params_halfninv *% repeat_plus_zq 1 (params_n/2) = 1);
  Group.mul_lemma_t (Group.mk_t params_halfninv) (repeat_plus_t Group.one_t (params_n/2));
  assert(Group.mul_t (Group.mk_t params_halfninv) (repeat_plus_t Group.one_t (params_n/2)) == Group.one_t);
  lemma_multiplicative_order_zeta ();
  Group.mul_lemma_t (Group.mk_t params_zeta) (Group.mk_t params_zetainv);
  Ring.lemma_mul_swap_t (Group.mk_t params_zeta) (Group.mk_t params_zetainv);
  assert(op_Star_Percent #params_q params_zeta params_zetainv = 1);

  assert(Lib.Arithmetic.Ring.mul #Group.t #Ring.ring_t (Group.mk_t params_halfninv) (Lib.Arithmetic.Ring.repeat_plus #Group.t #Ring.ring_t (Lib.Arithmetic.Ring.one #Group.t #Ring.ring_t) (params_n/2)) == Lib.Arithmetic.Ring.one #Group.t #Ring.ring_t);
  exp_correspondancy (Group.mk_t params_zeta) params_n;
  assert(Lib.Arithmetic.Ring.exp #Group.t #Ring.ring_t (Group.mk_t params_zeta) params_n == Lib.Arithmetic.Ring.one #Group.t #Ring.ring_t);
  assert_norm(Lib.Poly.NTT.lib_poly Group.t params_n == poly);
  let coerce #a #b (x:a) : Pure b (requires a == b) (ensures fun _ -> True) = x in
  lib_ntt_inversion_lemma2 #Group.t #Ring.ring_t #params_n 7 (Group.mk_t params_halfninv) (Group.mk_t params_zeta) (Group.mk_t params_zetainv) (coerce p)
