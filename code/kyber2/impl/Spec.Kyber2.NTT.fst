module Spec.Kyber2.NTT

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.Arithmetic.Sums

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
module NTT =  Lib.Poly.NTT

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

val ntt1: lseq (Group.t) (params_n/2) -> GTot (lseq (Group.t) (params_n/2))

let ntt1 p =
  NTT.lib_ntt #Group.t #Ring.ring_t (exp_t (Group.mk_t params_zeta) 2) (Group.mk_t params_zeta) p

noextract inline_for_extraction
let coerce_poly (x:poly) : Tot (lseq num params_n) = assert_norm(Lib.Poly.NTT.lib_poly Group.t params_n == poly); x


#reset-options "--z3rlimit 200 --max_fuel 1 --max_ifuel 1"

val lemma_ntt1_ntt:
  p:poly
  -> k:size_nat{k<params_n / 2}
  -> Lemma (let (p1,p2) = Lib.Arithmetic.Sums.split_seq #Group.t #params_n (coerce_poly p) in let p' = ntt p in let p1' = ntt1 p1 in let p2' = ntt1 p2 in Seq.index #Group.t #params_n p' (2*(br 7 k)) == p1'.[k] /\ Seq.index #Group.t #params_n p' (2*(br 7 k) + 1) == p2'.[k])

let lemma_ntt1_ntt p k =
  let (p1,p2) = Lib.Arithmetic.Sums.split_seq (coerce_poly p) in
  let p1' = ntt1 p1 in let p2' = ntt1 p2 in
  reorg_lemma 7 p1' k; reorg_lemma 7 p2' k

val ntt1_rec:
  i:size_nat{pow2 i <= params_n/2}
  -> p:lseq num (params_n/(pow2 (i+1)))
  -> GTot (lseq num (params_n/(pow2 (i+1))))

let ntt1_rec i p =
  NTT.lib_ntt #Group.t #Ring.ring_t (exp_t (Group.mk_t params_zeta) (pow2 (i+1))) (exp_t (Group.mk_t params_zeta) (pow2 i)) p

val lemma_ntt1_rec_zero:
  p:lseq num (params_n/2)
  -> Lemma (ntt1 p == ntt1_rec 0 p)

let lemma_ntt1_rec_zero p =
  assert(pow2 1 = 2);
  assert(exp_t (Group.mk_t params_zeta) (pow2 1) == exp_t (Group.mk_t params_zeta) 2);
  Lib.Arithmetic.Ring.lemma_exp_succ1 #num #Ring.ring_t (Group.mk_t params_zeta) 0;
  Lib.Arithmetic.Ring.lemma_exp_zero #num #Ring.ring_t (Group.mk_t params_zeta);
  Lib.Arithmetic.Ring.lemma_one2 #num #Ring.ring_t (Group.mk_t params_zeta)

val ntt1_reorg_rec:
  i:size_nat{pow2 i <= params_n/2}
  -> p:lseq num (params_n/(pow2 (i+1)))
  -> GTot (lseq num (params_n/(pow2 (i+1))))

let ntt1_reorg_rec i p =
  assert_norm(params_n == pow2 8);
  assert_norm(params_n/2 == pow2 7);
  if (i > 7) then pow2_lt_compat i 7;
  pow2_minus 8 (i+1);
  reorg (8-i-1) (ntt1_rec i p)

val lemma_ntt1_reorg_rec_seven_id:
  p:lseq num (params_n/(pow2 8))
  -> Lemma (ntt1_reorg_rec 7 p == p)

let lemma_ntt1_reorg_rec_seven_id p =
  assert_norm (params_n/(pow2 8) == 1);
  assert_norm(br 0 0 = 0);
  reorg_lemma 0 (ntt1_rec 7 p) 0;
  eq_intro (ntt1_reorg_rec 7 p) (ntt1_rec 7 p);
  NTT.lib_ntt_length_one_is_id (exp_t (Group.mk_t params_zeta) (pow2 8)) (exp_t (Group.mk_t params_zeta) (pow2 7)) p

val lemma_ntt1_reorg_rec_ntt_instantiate:
  p:poly
  -> k:size_nat{k<params_n / 2}
  -> Lemma (let (p1,p2) = Lib.Arithmetic.Sums.split_seq #Group.t #params_n p in let p' = ntt p in let p1' = ntt1_reorg_rec 0 p1 in let p2' = ntt1_reorg_rec 0 p2 in Seq.index #Group.t #params_n p' (2*k) == p1'.[k] /\ Seq.index #Group.t #params_n p' (2*k + 1) == p2'.[k])

let lemma_ntt1_reorg_rec_ntt_instantiate p k =
  let (p1,p2) = Lib.Arithmetic.Sums.split_seq p in
  lemma_ntt1_rec_zero p1; lemma_ntt1_rec_zero p2

val lemma_ntt1_reorg_rec_ntt:
  p:poly
  -> Lemma (let (p1,p2) = Lib.Arithmetic.Sums.split_seq #Group.t #params_n p in let p1' = ntt1_reorg_rec 0 p1 in let p2' = ntt1_reorg_rec 0 p2 in ntt p == join_seq p1' p2')

let lemma_ntt1_reorg_rec_ntt p =
  let (p1,p2) = Lib.Arithmetic.Sums.split_seq #Group.t #params_n p in let p' = ntt p in let p1' = ntt1_reorg_rec 0 p1 in let p2' = ntt1_reorg_rec 0 p2 in let j = join_seq p1' p2' in
  let customprop (k:size_nat{k<params_n}) : GTot Type0 = (Seq.index #Group.t #params_n p' k == j.[k]) in
  let customlemma (k:size_nat{k<params_n}) : Lemma (customprop k) =
    lemma_ntt1_reorg_rec_ntt_instantiate p (k/2)
  in FStar.Classical.forall_intro customlemma;
  eq_intro p' j

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

val lemma_ntt1_rec_split1:
  i:size_nat{i<max_size_t /\ pow2 i < params_n/2}
  -> p:lseq num (params_n/(pow2 (i+1)))
  -> peven:lseq num (params_n/(pow2 (i+2)))
  -> podd:lseq num (params_n/(pow2 (i+2)))
  -> k:size_nat{k<(params_n/(pow2 (i+2)))}
  -> Lemma (requires pow2 (i+1) <= params_n/2 /\ (params_n/(pow2(i+1)) == 2*(params_n/(pow2(i+2)))) /\ (peven,podd) == split_seq p)
    (ensures (ntt1_rec i p).[k] == Group.plus_t (ntt1_rec (i+1) peven).[k] (Group.mul_t (exp_t (Group.mk_t params_zeta) ((2*k+1)*pow2 i)) (ntt1_rec (i+1) podd).[k]))

let lemma_ntt1_rec_split1 i p peven podd k =
  NTT.lemma_ntt_split1 #num #Ring.ring_t #(params_n/(pow2 (i+1))) (exp_t (Group.mk_t params_zeta) (pow2 (i+1))) (exp_t (Group.mk_t params_zeta) (pow2 i)) p peven podd k;
  Lib.Arithmetic.Ring.lemma_exp_exp (Group.mk_t params_zeta) (pow2 (i+1)) 2;
  Lib.Arithmetic.Ring.lemma_exp_exp (Group.mk_t params_zeta) (pow2 i) 2;
  Lib.Arithmetic.Ring.lemma_exp_exp (Group.mk_t params_zeta) (pow2 (i+1)) k;
  pow2_double_mult i;
  pow2_double_mult (i+1);
  assert((ntt1_rec i p).[k] == Group.plus_t (ntt1_rec (i+1) peven).[k] (Group.mul_t (exp_t (Group.mk_t params_zeta) (pow2 i)) (Group.mul_t (ntt1_rec (i+1) podd).[k] (exp_t (Group.mk_t params_zeta) ((pow2 (i+1))*k)))));
  Ring.lemma_mul_swap_t (ntt1_rec (i+1) podd).[k] (exp_t (Group.mk_t params_zeta) ((pow2 (i+1))*k));
  Group.lemma_mul_assoc_t (exp_t (Group.mk_t params_zeta) (pow2 i)) (exp_t (Group.mk_t params_zeta) ((pow2 (i+1))*k)) (ntt1_rec (i+1) podd).[k];
  Lib.Arithmetic.Ring.lemma_exp_morphism (Group.mk_t params_zeta) (pow2 i) ((pow2 (i+1)) * k);
  assert (pow2 i + ((pow2 (i+1)) * k) == (2*k+1)*pow2 i);
  assert (exp_t (Group.mk_t params_zeta) (pow2 i + ((pow2 (i+1)) * k)) == exp_t (Group.mk_t params_zeta) ((2*k+1)*pow2 i))

val lemma_ntt1_rec_split2:
  i:size_nat{i<max_size_t /\ pow2 i < params_n/2}
  -> p:lseq num (params_n/(pow2 (i+1)))
  -> peven:lseq num (params_n/(pow2 (i+2)))
  -> podd:lseq num (params_n/(pow2 (i+2)))
  -> k:size_nat{k<(params_n/(pow2 (i+2)))}
  -> Lemma (requires pow2 (i+1) <= params_n/2 /\ (params_n/(pow2(i+1)) == 2*(params_n/(pow2(i+2)))) /\ (peven,podd) == split_seq p)
    (ensures (ntt1_rec i p).[k+(params_n/(pow2 (i+2)))] == Lib.Arithmetic.Ring.minus #num #Ring.ring_t (ntt1_rec (i+1) peven).[k] (Group.mul_t (exp_t (Group.mk_t params_zeta) ((2*k+1)*pow2 i)) (ntt1_rec (i+1) podd).[k]))

#reset-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0"

let lemma_ntt1_rec_split2 i p peven podd k =
  Lib.Arithmetic.Ring.lemma_exp_exp (Group.mk_t params_zeta) (pow2 (i+1)) (params_n/pow2 (i+1));
  assert_norm(params_n = pow2 8);
  if (i >= 8) then pow2_le_compat i 8;
  assert(i<8);
  pow2_minus 8 (i+1);
  pow2_plus (i+1) (8-(i+1));
  //assert (exp_t (exp_t (Group.mk_t params_zeta) (pow2 (i+1))) (params_n/pow2 (i+1)) == exp_t (Group.mk_t params_zeta) params_n);
  exp_correspondancy (Group.mk_t params_zeta) params_n;
  assert_norm(order_zeta () == params_n);
  assert(exp_t (exp_t (Group.mk_t params_zeta) (pow2 (i+1))) (params_n/pow2 (i+1)) == Group.one_t);
  NTT.lemma_ntt_split2 #num #Ring.ring_t #(params_n/(pow2 (i+1))) (exp_t (Group.mk_t params_zeta) (pow2 (i+1))) (exp_t (Group.mk_t params_zeta) (pow2 i)) p peven podd k;
  Lib.Arithmetic.Ring.lemma_exp_exp (Group.mk_t params_zeta) (pow2 (i+1)) 2;
  Lib.Arithmetic.Ring.lemma_exp_exp (Group.mk_t params_zeta) (pow2 i) 2;
  Lib.Arithmetic.Ring.lemma_exp_exp (Group.mk_t params_zeta) (pow2 (i+1)) (k+(params_n/(pow2 (i+2))));
  pow2_double_mult i;
  pow2_double_mult (i+1);
  assert((ntt1_rec i p).[k+(params_n/(pow2 (i+2)))] == Group.plus_t (ntt1_rec (i+1) peven).[k] (Group.mul_t (exp_t (Group.mk_t params_zeta) (pow2 i)) (Group.mul_t (ntt1_rec (i+1) podd).[k] (exp_t (Group.mk_t params_zeta) ((pow2 (i+1))*(k+(params_n/(pow2 (i+2)))))))));
  Ring.lemma_mul_swap_t (ntt1_rec (i+1) podd).[k] (exp_t (Group.mk_t params_zeta) ((pow2 (i+1))*(k+(params_n/(pow2 (i+2))))));
  Group.lemma_mul_assoc_t (exp_t (Group.mk_t params_zeta) (pow2 i)) (exp_t (Group.mk_t params_zeta) ((pow2 (i+1))*(k+(params_n/(pow2 (i+2)))))) (ntt1_rec (i+1) podd).[k];
  Ring.lemma_mul_swap_t (exp_t (Group.mk_t params_zeta) (pow2 i)) (exp_t (Group.mk_t params_zeta) ((pow2 (i+1))*(k+(params_n/(pow2 (i+2))))));
  pow2_minus 8 (i+2);
  pow2_plus (i+1) (8-(i+2));
  pow2_minus 8 1;
  assert((pow2 (i+1)) * (k + (params_n/(pow2 (i+2)))) == pow2 (i+1) * k + pow2 7);
  assert(exp_t (Group.mk_t params_zeta) ((pow2 (i+1))*(k+(params_n/(pow2 (i+2))))) == exp_t (Group.mk_t params_zeta) ((pow2 (i+1) * k + pow2 7)));
  Lib.Arithmetic.Ring.lemma_exp_morphism (Group.mk_t params_zeta) (pow2 (i+1) * k) (pow2 7);
  Ring.lemma_mul_swap_t (exp_t (Group.mk_t params_zeta) (pow2 (i+1) * k)) (exp_t (Group.mk_t params_zeta) (pow2 7));
  Group.lemma_mul_assoc_t (exp_t (Group.mk_t params_zeta) (pow2 7)) (exp_t (Group.mk_t params_zeta) (pow2 (i+1) * k)) (exp_t (Group.mk_t params_zeta) (pow2 i));
  Lib.Arithmetic.Ring.lemma_exp_morphism (Group.mk_t params_zeta) ((pow2 (i+1)) * k) (pow2 i);
  assert (((pow2 (i+1)) * k) + pow2 i == (2*k+1)*pow2 i);
  assert (exp_t (Group.mk_t params_zeta) (((pow2 (i+1)) * k) + pow2 i) == exp_t (Group.mk_t params_zeta) ((2*k+1)*pow2 i));
  Group.lemma_mul_assoc_t (exp_t (Group.mk_t params_zeta) (pow2 7)) (exp_t (Group.mk_t params_zeta) ((2*k+1)*(pow2 i))) (ntt1_rec (i+1) podd).[k];
  let g1 = (ntt1_rec (i+1) peven).[k] in
  let g2 = Group.mul_t (exp_t (Group.mk_t params_zeta) ((2*k+1)*(pow2 i))) (ntt1_rec (i+1) podd).[k] in
  assert_norm(pow2 7 = 128);
  exp_correspondancy (Group.mk_t params_zeta) 128;
  assert_norm (params_zeta ^% 128 == (-1) % params_q);
  assert((ntt1_rec i p).[k+(params_n/(pow2 (i+2)))] == Group.plus_t g1 (Group.mul_t (exp_t (Group.mk_t params_zeta) 128) g2));
  Group.plus_lemma_t g1 (Group.mul_t (exp_t (Group.mk_t params_zeta) 128) g2);
  Group.mul_lemma_t (exp_t (Group.mk_t params_zeta) 128) g2;
  assert(Group.v (ntt1_rec i p).[k+(params_n/(pow2 (i+2)))] == (Group.v g1 + ((((-1)%params_q)*Group.v g2) % params_q)) %params_q);
  lemma_mod_mul_distr_l (-1) (Group.v g2) params_q;
  assert(Group.v (ntt1_rec i p).[k+(params_n/(pow2 (i+2)))] == (Group.v g1 + (((-1)*Group.v g2) % params_q)) %params_q);
  lemma_mod_plus_distr_r (Group.v g1) (- Group.v g2) params_q;
  assert(Group.v (ntt1_rec i p).[k+(params_n/(pow2 (i+2)))] == (Group.v g1 + (- Group.v g2)) %params_q);
  assert(Group.v (ntt1_rec i p).[k+(params_n/(pow2 (i+2)))] == (Group.v g1 - Group.v g2) %params_q);
  Ring.minus_lemma_t g1 g2

val lemma_ntt1_rec_br_split1:
  i:size_nat{i<max_size_t /\ pow2 i < params_n/2}
  -> p:lseq num (params_n/(pow2 (i+1)))
  -> peven:lseq num (params_n/(pow2 (i+2)))
  -> podd:lseq num (params_n/(pow2 (i+2)))
  -> k:size_nat{k<(params_n/(pow2 (i+1))) /\ k%2 = 0}
  -> Lemma (requires (params_n/(pow2(i+1)) == 2*(params_n/(pow2(i+2)))) /\ (peven,podd) == split_seq p)
    (ensures i < 7 /\ pow2 (i+1) <= params_n/2 /\ k < pow2 (8-i-1) /\ br (8 - i - 1) k < (params_n/(pow2 (i+2))) /\ pow2 (8-i-1) = (params_n/(pow2 (i+1))) /\ (params_n/(pow2(i+2))) <= params_n / (pow2 (i+1)) /\ (ntt1_rec i p).[br (8-i-1) k] == Group.plus_t (ntt1_rec (i+1) peven).[br (8-i-2) (k/2)] (Group.mul_t (exp_t (Group.mk_t params_zeta) (br 8 (k + pow2 (8-i-1)))) (ntt1_rec (i+1) podd).[br (8-i-2) (k/2)]))

let lemma_ntt1_rec_br_split1 i p peven podd k =
  assert_norm(params_n/2 = pow2 7);
  if (i>=7) then pow2_le_compat i 7;
  pow2_le_compat 7 (i+1);
  assert_norm(params_n = pow2 8);
  pow2_minus 8 (i+1);
  br_lemma_n2_2 (8 - i - 2) k;
  pow2_double_sum (8 - i - 2);
  pow2_minus 8 (i+2);
  assert(br (8-i-1) k < params_n/(pow2(i+2)));
  br_lemma_n2_1 (8-i-1) k;
  br_lemma_rec (8-i-1) k;
  br_lemma_rec_p (8-i) i (k+pow2 (8-i-1));
  assert (br 8 (k+ pow2 (8-i-1)) == (2*(br (8-i-1) k)+1) * pow2 i);
  assert((params_n/(pow2(i+1)) == 2*(params_n/(pow2(i+2)))));
  lemma_ntt1_rec_split1 i p peven podd (br (8-i-1) k);
  br_lemma_div (8-i-1) k;
  lemma_mult_le_left 2 (br (8-i-1) k) (pow2 (8-i-2));
  modulo_lemma (2*br (8-i-1) k) (pow2 (8-i-1));
  assert(br (8-i-1) (k/2) == 2 * br (8-i-1) k);
  lemma_div_lt k (8-i-1) 1;
  br_lemma_rec (8-i-2) (k/2)

val lemma_ntt1_rec_br_split2:
  i:size_nat{i<max_size_t /\ pow2 i < params_n/2}
  -> p:lseq num (params_n/(pow2 (i+1)))
  -> peven:lseq num (params_n/(pow2 (i+2)))
  -> podd:lseq num (params_n/(pow2 (i+2)))
  -> k:size_nat{k<(params_n/(pow2 (i+1))) /\ k%2 = 0}
  -> Lemma (requires (params_n/(pow2(i+1)) == 2*(params_n/(pow2(i+2)))) /\ (peven,podd) == split_seq p)
    (ensures i < 7 /\ pow2 (i+1) <= params_n/2 /\ k < pow2 (8-i-1) /\ br (8 - i - 1) k < (params_n/(pow2 (i+2))) /\ pow2 (8-i-1) = (params_n/(pow2 (i+1))) /\ (params_n/(pow2(i+2))) <= params_n / (pow2 (i+1)) /\ (ntt1_rec i p).[br (8-i-1) (k+1)] == Lib.Arithmetic.Ring.minus (ntt1_rec (i+1) peven).[br (8-i-2) (k/2)] (Group.mul_t (exp_t (Group.mk_t params_zeta) (br 8 (k + pow2 (8-i-1)))) (ntt1_rec (i+1) podd).[br (8-i-2) (k/2)]))

let lemma_ntt1_rec_br_split2 i p peven podd k =
  assert_norm(params_n/2 = pow2 7);
  if (i>=7) then pow2_le_compat i 7;
  pow2_le_compat 7 (i+1);
  assert_norm(params_n = pow2 8);
  pow2_minus 8 (i+1);
  br_lemma_n2_2 (8 - i - 2) k;
  pow2_double_sum (8 - i - 2);
  pow2_minus 8 (i+2);
  assert(br (8-i-1) k < params_n/(pow2(i+2)));
  br_lemma_n2_1 (8-i-1) k;
  br_lemma_rec (8-i-1) k;
  br_lemma_rec_p (8-i) i (k+pow2 (8-i-1));
  assert (br 8 (k+ pow2 (8-i-1)) == (2*(br (8-i-1) k)+1) * pow2 i);
  assert((params_n/(pow2(i+1)) == 2*(params_n/(pow2(i+2)))));
  lemma_ntt1_rec_split2 i p peven podd (br (8-i-1) k);
  br_lemma_div (8-i-1) k;
  lemma_mult_le_left 2 (br (8-i-1) k) (pow2 (8-i-2));
  modulo_lemma (2*br (8-i-1) k) (pow2 (8-i-1));
  assert(br (8-i-1) (k/2) == 2 * br (8-i-1) k);
  lemma_div_lt k (8-i-1) 1;
  br_lemma_rec (8-i-2) (k/2);
  br_lemma_n2_2 (8-i-2) k

val lemma_ntt1_rec_reorg_split1:
  i:size_nat{i<7}
  -> p:lseq num (params_n/(pow2 (i+1)))
  -> peven:lseq num (params_n/(pow2 (i+2)))
  -> podd:lseq num (params_n/(pow2 (i+2)))
  -> k:size_nat{k<(params_n/(pow2 (i+2)))}
  -> Lemma (requires (params_n/(pow2(i+1)) == 2*(params_n/(pow2(i+2)))) /\ (peven,podd) == split_seq p)
    (ensures pow2 (8-i-1) = (params_n/(pow2 (i+1))) /\ pow2 (8-i-2) = (params_n/(pow2 (i+2))) /\ (ntt1_reorg_rec i p).[2*k] == Group.plus_t (ntt1_reorg_rec (i+1) peven).[k] (Group.mul_t (exp_t (Group.mk_t params_zeta) (br 7 (k + pow2 (6-i)))) (ntt1_reorg_rec (i+1) podd).[k]))

let lemma_ntt1_rec_reorg_split1 i p peven podd k =
  pow2_lt_compat 7 i;
  assert_norm(params_n/2 = pow2 7);
  lemma_ntt1_rec_br_split1 i p peven podd (2*k);
  assert_norm(params_n == pow2 8);
  pow2_minus 8 (i+2);
  multiple_division_lemma k 2;
  reorg_lemma (8-i-1) (ntt1_rec i p) (2*k);
  reorg_lemma (8-i-2) (ntt1_rec (i+1) peven) (k);
  reorg_lemma (8-i-2) (ntt1_rec (i+1) podd) (k);
  pow2_double_mult (6-i);
  distributivity_add_right 2 k (pow2 (6-i));
  pow2_double_sum (7-i);
  assert(2*k + pow2 (7-i) < pow2 (8-i));
  multiple_division_lemma (k + pow2 (6-i)) 2;
  br_lemma_div 8 (2*k + pow2 (7-i));
  br_lemma_n2_2 7 (2*k + pow2 (7-i));
  cancel_mul_div (br 8 (2*k + pow2 (7-i))) 2;
  br_lemma_rec 7 (k + pow2 (6-i))

val lemma_ntt1_rec_reorg_split2:
  i:size_nat{i<7}
  -> p:lseq num (params_n/(pow2 (i+1)))
  -> peven:lseq num (params_n/(pow2 (i+2)))
  -> podd:lseq num (params_n/(pow2 (i+2)))
  -> k:size_nat{k<(params_n/(pow2 (i+2)))}
  -> Lemma (requires (params_n/(pow2(i+1)) == 2*(params_n/(pow2(i+2)))) /\ (peven,podd) == split_seq p)
    (ensures pow2 (8-i-1) = (params_n/(pow2 (i+1))) /\ pow2 (8-i-2) = (params_n/(pow2 (i+2))) /\ (ntt1_reorg_rec i p).[2*k+1] == Lib.Arithmetic.Ring.minus (ntt1_reorg_rec (i+1) peven).[k] (Group.mul_t (exp_t (Group.mk_t params_zeta) (br 7 (k + pow2 (6-i)))) (ntt1_reorg_rec (i+1) podd).[k]))

let lemma_ntt1_rec_reorg_split2 i p peven podd k =
  pow2_lt_compat 7 i;
  assert_norm(params_n/2 = pow2 7);
  lemma_ntt1_rec_br_split2 i p peven podd (2*k);
  assert_norm(params_n == pow2 8);
  pow2_minus 8 (i+2);
  reorg_lemma (8-i-1) (ntt1_rec i p) (2*k+1);
  reorg_lemma (8-i-2) (ntt1_rec (i+1) peven) k;
  reorg_lemma (8-i-2) (ntt1_rec (i+1) podd) k;
  pow2_double_mult (6-i);
  distributivity_add_right 2 k (pow2 (6-i));
  pow2_double_sum (7-i);
  assert(2*k + pow2 (7-i) < pow2 (8-i));
  multiple_division_lemma (k + pow2 (6-i)) 2;
  br_lemma_div 8 (2*k + pow2 (7-i));
  br_lemma_n2_2 7 (2*k + pow2 (7-i));
  cancel_mul_div (br 8 (2*k + pow2 (7-i))) 2;
  br_lemma_rec 7 (k + pow2 (6-i))

