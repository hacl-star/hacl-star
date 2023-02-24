module Hacl.Impl.P256.Qinv

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open FStar.Math.Lemmas
open Hacl.Impl.P256.Math

open Hacl.Impl.P256.Bignum
open Hacl.Impl.P256.Constants
open Hacl.Spec.P256.Lemmas
open FStar.Tactics
open FStar.Tactics.Canon

open FStar.Mul

open Lib.Loops

friend Hacl.Impl.P256.Scalar

module S = Spec.P256

#reset-options " --z3rlimit 200 --fuel 0 --ifuel 0"


[@ CInline]
val cswap: bit:uint64{v bit <= 1} -> p:felem -> q:felem
  -> Stack unit
    (requires fun h ->
      as_nat h p < S.order /\ as_nat h q < S.order /\
      live h p /\ live h q /\ (disjoint p q \/ p == q))
    (ensures  fun h0 _ h1 ->
      modifies (loc p |+| loc q) h0 h1 /\
	(
	  let (r0, r1) = Spec.ECDSA.conditional_swap bit (as_nat h0 p) (as_nat h0 q) in
	  let pBefore = as_seq h0 p in let qBefore = as_seq h0 q in
	  let pAfter = as_seq h1 p in let qAfter = as_seq h1 q in
	  if uint_v bit = 0 then r0 == as_nat h0 p /\ r1 == as_nat h0 q else r0 == as_nat h0 q /\ r1 == as_nat h0 p) /\
	  as_nat h1 p < S.order /\ as_nat h1 q < S.order /\
      (v bit == 1 ==> as_seq h1 p == as_seq h0 q /\ as_seq h1 q == as_seq h0 p) /\
      (v bit == 0 ==> as_seq h1 p == as_seq h0 p /\ as_seq h1 q == as_seq h0 q))


let cswap bit p1 p2 =
  let h0 = ST.get () in
  let mask = u64 0 -. bit in
  let open Lib.Sequence in
  [@ inline_let]
  let inv h1 (i:nat{i <= 4}) =
    (forall (k:nat{k < i}).
      if v bit = 1
      then (as_seq h1 p1).[k] == (as_seq h0 p2).[k] /\ (as_seq h1 p2).[k] == (as_seq h0 p1).[k]
      else (as_seq h1 p1).[k] == (as_seq h0 p1).[k] /\ (as_seq h1 p2).[k] == (as_seq h0 p2).[k]) /\
    (forall (k:nat{i <= k /\ k < 4}).
      (as_seq h1 p1).[k] == (as_seq h0 p1).[k] /\ (as_seq h1 p2).[k] == (as_seq h0 p2).[k]) /\
    modifies (loc p1 |+| loc p2) h0 h1 in

  Lib.Loops.for 0ul 4ul inv
    (fun i ->
      let dummy = mask &. (p1.(i) ^. p2.(i)) in
      p1.(i) <- p1.(i) ^. dummy;
      p2.(i) <- p2.(i) ^. dummy;
      lemma_cswap2_step bit ((as_seq h0 p1).[v i]) ((as_seq h0 p2).[v i])
    );
  let h1 = ST.get () in
  Lib.Sequence.eq_intro (as_seq h1 p1) (if v bit = 1 then as_seq h0 p2 else as_seq h0 p1);
  Lib.Sequence.eq_intro (as_seq h1 p2) (if v bit = 1 then as_seq h0 p1 else as_seq h0 p2)


inline_for_extraction noextract
val montgomery_ladder_exponent_step0: a: felem -> b: felem -> Stack unit
  (requires fun h -> live h a /\ live h b /\
    as_nat h a < S.order /\ as_nat h b < S.order /\ disjoint a b)
  (ensures fun h0 _ h1 -> modifies (loc a |+| loc b) h0 h1 /\
    as_nat h1 a < S.order /\ as_nat h1 b < S.order /\
    (
      let (r0D, r1D) = _exp_step0 (fromDomain_ (as_nat h0 a)) (fromDomain_ (as_nat h0 b)) in
      r0D == fromDomain_ (as_nat h1 a) /\ r1D == fromDomain_ (as_nat h1 b)
    )
)

let montgomery_ladder_exponent_step0 a b =
    let h0 = ST.get() in
  montgomery_multiplication_ecdsa_module a b b;
    lemmaToDomainFromDomain (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 b) % S.order);
  montgomery_multiplication_ecdsa_module a a a ;
    lemmaToDomainFromDomain (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a) % S.order)


inline_for_extraction noextract
val montgomery_ladder_exponent_step: a: felem -> b: felem -> scalar: glbuffer uint8 (size 32) ->   i:size_t{v i < 256} ->  Stack unit
  (requires fun h -> live h a  /\ live h b /\ live h scalar /\ as_nat h a < S.order /\ as_nat h b < S.order /\ disjoint a b)
  (ensures fun h0 _ h1 -> modifies (loc a |+| loc b) h0 h1  /\
    (
      let a_ = fromDomain_ (as_nat h0 a) in
      let b_ = fromDomain_ (as_nat h0 b) in
      let (r0D, r1D) = _exp_step (as_seq h0 scalar) (uint_v i) (a_, b_) in
      r0D == fromDomain_ (as_nat h1 a) /\ r1D == fromDomain_ (as_nat h1 b) /\
      as_nat h1 a < S.order /\ as_nat h1 b < S.order
    )
  )

let montgomery_ladder_exponent_step a b scalar i =
    let h0 = ST.get() in
  let bit0 = (size 255) -. i in
  let bit = scalar_bit scalar bit0 in
  cswap bit a b;
  montgomery_ladder_exponent_step0 a b;
  cswap bit a b;
  Spec.ECDSA.lemma_swaped_steps (fromDomain_ (as_nat h0 a)) (fromDomain_ (as_nat h0 b))


inline_for_extraction noextract
val _montgomery_ladder_exponent: a: felem ->b: felem ->  scalar: glbuffer uint8 (size 32) -> Stack unit
  (requires fun h -> live h a /\ live h b /\ live h scalar /\ as_nat h a < S.order /\
    as_nat h b < S.order /\ disjoint a b /\disjoint a scalar /\ disjoint b scalar)
  (ensures fun h0 _ h1 -> modifies (loc a |+| loc b) h0 h1 /\
    (
      let a_ = fromDomain_ (as_nat h0 a) in
      let b_ = fromDomain_ (as_nat h0 b) in
      let (r0D, r1D) = _exponent_spec (as_seq h0 scalar) (a_, b_) in
      r0D == fromDomain_ (as_nat h1 a) /\ r1D == fromDomain_ (as_nat h1 b) /\
      as_nat h1 a < S.order /\ as_nat h1 b < S.order )
  )


let _montgomery_ladder_exponent a b scalar =
  let h0 = ST.get() in
  [@inline_let]
  let spec_exp h0  = _exp_step (as_seq h0 scalar) in
  [@inline_let]
  let acc (h: mem) : GTot (tuple2 S.qelem S.qelem) = (fromDomain_ (as_nat h a), fromDomain_ (as_nat h b)) in
  Lib.LoopCombinators.eq_repeati0 256 (spec_exp h0) (acc h0);
  [@inline_let]
  let inv h (i: nat {i <= 256}) =
    live h a /\ live h b /\ live h scalar /\ modifies (loc a |+| loc b) h0 h /\ as_nat h a < S.order /\ as_nat h b < S.order /\
    acc h == Lib.LoopCombinators.repeati i (spec_exp h0) (acc h0) in
  for 0ul 256ul inv (
    fun i ->
	  montgomery_ladder_exponent_step a b scalar i;
	  Lib.LoopCombinators.unfold_repeati 256 (spec_exp h0) (acc h0) (uint_v i))


inline_for_extraction noextract
val upload_one_montg_form: b: felem -> Stack unit
  (requires fun h -> live h b)
  (ensures fun h0 _ h1 -> modifies (loc b) h0 h1 /\ as_nat h1 b == toDomain_ (1))

let upload_one_montg_form b =
  upd b (size 0) (u64 884452912994769583);
  upd b (size 1) (u64 4834901526196019579);
  upd b (size 2) (u64 0);
  upd b (size 3) (u64 4294967295);
    assert_norm(toDomain_ 1 == 26959946660873538059280334323273029441504803697035324946844617595567)


let montgomery_ladder_exponent r =
  push_frame();
    let p = create (size 4) (u64 0) in
    upload_one_montg_form p;
    recall_contents order_inverse_buffer order_inverse_seq;
    let h = ST.get() in
    mut_const_immut_disjoint #uint64 #uint8 p order_inverse_buffer h;
    mut_const_immut_disjoint #uint64 #uint8 r order_inverse_buffer h;
    assert (disjoint p order_inverse_buffer);
    assert (disjoint r order_inverse_buffer);
    _montgomery_ladder_exponent p r order_inverse_buffer;
      lemmaToDomainFromDomain 1;
    copy r p;
  pop_frame()

//--------------------------

val lemma_fromDomain1: a: nat ->
  Lemma ((fromDomain_ (fromDomain_ (fromDomain_ a))) == ((a * S.modp_inv2_prime (pow2 256) order * S.modp_inv2_prime (pow2 256) order * S.modp_inv2_prime (pow2 256) order) % order))

let lemma_fromDomain1 a =
  let f = S.modp_inv2_prime (pow2 256) order in
  lemma_mod_mul_distr_l (a * f) f order;
  lemma_mod_mul_distr_l (a * f * f) f order


val lemma_fromDomain2: a: nat ->
  Lemma (S.pow (fromDomain_ (fromDomain_ a)) (order - 2) % order ==
    (
      S.pow a (order - 2) *
      S.pow (S.modp_inv2_prime (pow2 256) order) (order - 2) *
      S.pow (S.modp_inv2_prime (pow2 256) order) (order - 2)) % order /\
      S.pow (S.modp_inv2_prime (pow2 256) order) (order - 2) * S.pow (pow2 256) (order -2) % order == 1
    )


let lemma_fromDomain2 a =
  let r = S.modp_inv2_prime (pow2 256) order in
  lemma_mod_mul_distr_l (a * r) r order;
  power_distributivity (a * r * r) (order - 2) order;
    assert_by_tactic (a * r * r == a * (r * r)) canon;
  power_distributivity_2 a (r * r) (order - 2);
  power_distributivity_2 (S.modp_inv2_prime (pow2 256) order) (S.modp_inv2_prime (pow2 256) order) (order -2);
  assert_by_tactic (S.pow a (order - 2) * (
      S.pow (S.modp_inv2_prime (pow2 256) order) (order - 2) *
      S.pow (S.modp_inv2_prime (pow2 256) order) (order - 2)) ==
      S.pow a (order - 2) *
      S.pow (S.modp_inv2_prime (pow2 256) order) (order - 2) *
      S.pow (S.modp_inv2_prime (pow2 256) order) (order - 2)) canon;

  let inv_pow256_order = 43790243014242295660885426880012836369732278457577312309071968676491870960761 in
  assert_norm (S.modp_inv2_prime (pow2 256) order == inv_pow256_order);
  assert_norm (inv_pow256_order * (pow2 256) % order == 1);
  power_distributivity_2 (inv_pow256_order) (pow2 256) (order - 2);
  power_distributivity (inv_pow256_order * pow2 256) (order - 2) order;
  power_one (order -2)


#push-options "--fuel 2"
let multPowerPartial s a b result =
  let h0 = ST.get() in
  push_frame();
    let buffFromDB = create (size 4) (u64 0) in
    fromDomainImpl b buffFromDB;
    fromDomainImpl buffFromDB buffFromDB;
    montgomery_multiplication_ecdsa_module a buffFromDB result;
  pop_frame();

    let p = S.pow (fromDomain_ (fromDomain_ (as_nat h0 s))) (order - 2) % order in
    let q = fromDomain_ (fromDomain_ (fromDomain_ (as_nat h0 b))) in
    let r = S.modp_inv2_prime (pow2 256) order in
      lemma_fromDomain1 (as_nat h0 b);
      lemma_fromDomain2 (as_nat h0 s);

      lemma_mod_mul_distr_l (S.pow (as_nat h0 s) (order - 2) * S.pow r (order - 2) * S.pow r (order - 2)) (((as_nat h0 b) * r * r * r) % order) order;
      lemma_mod_mul_distr_r (S.pow (as_nat h0 s) (order - 2) * S.pow r (order - 2) * S.pow r (order - 2)) ((as_nat h0 b) * r * r * r) order;
      assert_by_tactic (S.pow (as_nat h0 s) (order - 2) * S.pow r (order - 2) * S.pow r (order - 2) * ((as_nat h0 b) * r * r * r) == S.pow (as_nat h0 s) (order - 2) * (S.pow r (order - 2) * r) * (S.pow r (order - 2) * r) * (as_nat h0 b) * r) canon;

      pow_plus r (order - 2) 1;
      power_one r;
      lemma_mod_mul_distr_l (S.pow (as_nat h0 s) (order - 2) * (S.pow r (order - 1)) * (S.pow r (order - 1)) * (as_nat h0 b) * r) (pow2 256) order;

      assert_by_tactic (S.pow (as_nat h0 s) (order - 2) * (S.pow r (order - 1)) * (S.pow r (order - 1)) * (as_nat h0 b) * r * pow2 256 == S.pow (as_nat h0 s) (order - 2) * (S.pow r (order - 1)) * (S.pow r (order - 1)) * (as_nat h0 b) * (r * pow2 256)) canon;
      lemma_mod_mul_distr_r (S.pow (as_nat h0 s) (order - 2) * (S.pow r (order - 1)) * (S.pow r (order - 1)) * (as_nat h0 b)) (r * pow2 256) order;
      assert_norm ((pow2 256 * S.modp_inv2_prime (pow2 256) order) % order == 1);

      assert_by_tactic (S.pow (as_nat h0 s) (order - 2) * (S.pow r (order - 1)) * (S.pow r (order - 1)) * (as_nat h0 b) == S.pow (as_nat h0 s) (order - 2) * (as_nat h0 b)  * (S.pow r (order - 1)) * (S.pow r (order - 1))) canon;
      lemma_mod_mul_distr_r (S.pow (as_nat h0 s) (order - 2) * (as_nat h0 b)  * (S.pow r (order - 1))) (S.pow r (order - 1)) order;
      lemma_l_ferm ();

      lemma_mod_mul_distr_r (S.pow (as_nat h0 s) (order - 2) * (as_nat h0 b)) (S.pow r (order - 1)) order
#pop-options
