module Hacl.Impl.P256.Field

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.P256.Felem
open Hacl.Impl.P256.Bignum
open Hacl.Impl.P256.Constants

module S = Spec.P256
module SM = Hacl.Spec.P256.MontgomeryMultiplication
module SL = Hacl.Spec.P256.Lemmas

module BD = Hacl.Spec.Bignum.Definitions
module BM = Hacl.Bignum.Montgomery
module SBM = Hacl.Spec.Bignum.Montgomery
module SBML = Hacl.Spec.Montgomery.Lemmas

friend Hacl.Bignum256

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val mont_R_inv_is_bn_mont_d: unit -> Lemma
  (requires S.prime % 2 = 1)
  (ensures  (let d, _ = SBML.eea_pow2_odd 256 S.prime in SM.mont_R_inv == d % S.prime))

let mont_R_inv_is_bn_mont_d () =
  let d, k = SBML.eea_pow2_odd 256 S.prime in
  SBML.mont_preconditions_d 64 4 S.prime;
  assert (d * pow2 256 % S.prime = 1);

  assert_norm (SM.mont_R * SM.mont_R_inv % S.prime = 1);
  Math.Lemmas.lemma_mod_mul_distr_l (pow2 256) SM.mont_R_inv S.prime;
  assert (SM.mont_R_inv * pow2 256 % S.prime = 1);

  assert (SM.mont_R_inv * pow2 256 % S.prime = d * pow2 256 % S.prime);
  Hacl.Spec.P256.Math.lemma_modular_multiplication_pow256 SM.mont_R_inv d;
  assert (SM.mont_R_inv % S.prime == d % S.prime);
  Math.Lemmas.modulo_lemma SM.mont_R_inv S.prime;
  assert (SM.mont_R_inv == d % S.prime)


val lemma_prime_mont: unit ->
  Lemma (S.prime % 2 = 1 /\ S.prime < pow2 256 /\ (1 + S.prime) % pow2 64 = 0)

let lemma_prime_mont () =
  assert_norm (S.prime % 2 = 1);
  assert_norm (S.prime < pow2 256);
  assert_norm ((1 + S.prime) % pow2 64 = 0)


val mont_reduction_lemma: x:Lib.Sequence.lseq uint64 8 -> n:Lib.Sequence.lseq uint64 4 -> Lemma
  (requires BD.bn_v n = S.prime /\ BD.bn_v x < S.prime * S.prime)
  (ensures  BD.bn_v (SBM.bn_mont_reduction n (u64 1) x) == BD.bn_v x * SM.mont_R_inv % S.prime)

let mont_reduction_lemma x n =
  lemma_prime_mont ();
  assert (SBM.bn_mont_pre n (u64 1));
  let d, _ = SBML.eea_pow2_odd 256 (BD.bn_v n) in

  let res = SBM.bn_mont_reduction n (u64 1) x in
  assert_norm (S.prime * S.prime < S.prime * pow2 256);
  assert (BD.bn_v x < S.prime * pow2 256);

  SBM.bn_mont_reduction_lemma n (u64 1) x;
  assert (BD.bn_v res == SBML.mont_reduction 64 4 (BD.bn_v n) 1 (BD.bn_v x));
  SBML.mont_reduction_lemma 64 4 (BD.bn_v n) 1 (BD.bn_v x);
  assert (BD.bn_v res == BD.bn_v x * d % S.prime);
  calc (==) {
    (BD.bn_v x) * d % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r (BD.bn_v x) d S.prime }
    (BD.bn_v x) * (d % S.prime) % S.prime;
    (==) { mont_R_inv_is_bn_mont_d () }
    (BD.bn_v x) * SM.mont_R_inv % S.prime;
  }


val mont_reduction: x:widefelem -> res:felem -> Stack unit
  (requires fun h ->
    live h x /\ live h res /\ disjoint x res /\
    wide_as_nat h x < S.prime * S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res |+| loc x) h0 h1 /\
    as_nat h1 res == wide_as_nat h0 x * SM.mont_R_inv % S.prime)

[@CInline]
let mont_reduction x res =
  push_frame ();
  let n = create 4ul (u64 0) in
  make_prime n;

  let h0 = ST.get () in
  BM.bn_mont_reduction Hacl.Bignum256.bn_inst n (u64 1) x res;
  let h1 = ST.get () in
  bignum_bn_v_is_as_nat h0 n;
  bignum_bn_v_is_wide_as_nat h0 x;
  assert (BD.bn_v (as_seq h0 n) == as_nat h0 n);
  assert (BD.bn_v (as_seq h0 x) == wide_as_nat h0 x);
  mont_reduction_lemma (as_seq h0 x) (as_seq h0 n);
  assert (BD.bn_v (as_seq h1 res) == BD.bn_v (as_seq h0 x) * SM.mont_R_inv % S.prime);
  bignum_bn_v_is_as_nat h1 res;
  assert (as_nat h1 res == wide_as_nat h0 x * SM.mont_R_inv % S.prime);
  pop_frame ()

//---------------------

val fmod_short_lemma: a:nat{a < pow2 256} ->
  Lemma (let r = if a >= S.prime then a - S.prime else a in r = a % S.prime)

let fmod_short_lemma a =
  let r = if a >= S.prime then a - S.prime else a in
  if a >= S.prime then begin
    Math.Lemmas.lemma_mod_sub a S.prime 1;
    assert_norm (pow2 256 - S.prime < S.prime);
    Math.Lemmas.small_mod r S.prime end
  else
   Math.Lemmas.small_mod r S.prime


[@CInline]
let fmod_short x res =
  push_frame ();
  let tmp = create (size 4) (u64 0) in
  recall_contents prime_buffer (Lib.Sequence.of_list p256_prime_list);
  let h0 = ST.get () in
  let c = bn_sub4_il x prime_buffer tmp in
  bn_cmovznz4 c tmp x res;
  as_nat_bound h0 x;
  fmod_short_lemma (as_nat h0 x);
  pop_frame ()


[@CInline]
let fadd x y res =
  let h0 = ST.get () in
  push_frame ();
  let n = create 4ul (u64 0) in
  make_prime n;
  bn_add_mod4 x y n res;
  let h1 = ST.get () in
  assert (as_nat h1 res == (as_nat h0 x + as_nat h0 y) % S.prime);
  pop_frame ();
  SM.additionInDomain (as_nat h0 x) (as_nat h0 y);
  SM.inDomain_mod_is_not_mod (SM.fromDomain_ (as_nat h0 x) + SM.fromDomain_ (as_nat h0 y))


let fdouble x out =
  fadd x x out


[@CInline]
let fsub x y res =
  let h0 = ST.get () in
  push_frame ();
  let n = create 4ul (u64 0) in
  make_prime n;
  bn_sub_mod4 x y n res;
  let h1 = ST.get () in
  assert (as_nat h1 res == (as_nat h0 x - as_nat h0 y) % S.prime);
  pop_frame ();
  SM.substractionInDomain (as_nat h0 x) (as_nat h0 y);
  SM.inDomain_mod_is_not_mod (SM.fromDomain_ (as_nat h0 x) - SM.fromDomain_ (as_nat h0 y))


[@CInline]
let fromDomain a res =
  push_frame ();
  let t = create (size 8) (u64 0) in
  let t_low = sub t (size 0) (size 4) in
  let t_high = sub t (size 4) (size 4) in

  let h0 = ST.get () in
  copy t_low a;
  let h1 = ST.get () in
  assert (wide_as_nat h0 t = as_nat h0 t_low + as_nat h0 t_high * pow2 256);
  assert_norm (S.prime < S.prime * S.prime);
  mont_reduction t res;
  SM.lemmaFromDomain (as_nat h0 a);
  pop_frame ()


[@CInline]
let fmul a b res =
  push_frame ();
  let t = create (size 8) (u64 0) in
  let h0 = ST.get () in
  bn_mul4 a b t;
  let h1 = ST.get () in
  SL.mul_lemma_ (as_nat h0 a) (as_nat h0 b) S.prime;
  mont_reduction t res;
  SM.lemmaFromDomainToDomain (as_nat h0 a);
  SM.lemmaFromDomainToDomain (as_nat h0 b);
  SM.multiplicationInDomainNat
    #(SM.fromDomain_ (as_nat h0 a)) #(SM.fromDomain_ (as_nat h0 b)) (as_nat h0 a) (as_nat h0 b);
  SM.inDomain_mod_is_not_mod (SM.fromDomain_ (as_nat h0 a) * SM.fromDomain_ (as_nat h0 b));
  pop_frame ()


[@CInline]
let fsqr a res =
  push_frame ();
  let t = create (size 8) (u64 0) in
  let h0 = ST.get() in
  bn_sqr4 a t;
  let h1 = ST.get() in
  SL.mul_lemma_ (as_nat h0 a) (as_nat h0 a) S.prime;
  mont_reduction t res;
  SM.lemmaFromDomainToDomain (as_nat h0 a);
  SM.multiplicationInDomainNat
    #(SM.fromDomain_ (as_nat h0 a)) #(SM.fromDomain_ (as_nat h0 a)) (as_nat h0 a) (as_nat h0 a);
  SM.inDomain_mod_is_not_mod (SM.fromDomain_ (as_nat h0 a) * SM.fromDomain_ (as_nat h0 a));
  pop_frame ()

//----------------------------------------------

[@CInline]
let fcube a result =
  let h0 = ST.get () in
  fsqr a result;
  fmul result a result;
  let h1 = ST.get () in
  Math.Lemmas.lemma_mod_mul_distr_l
    (SM.fromDomain_ (as_nat h0 a) * SM.fromDomain_ (as_nat h0 a))
    (SM.fromDomain_ (as_nat h0 a)) S.prime;
  SM.inDomain_mod_is_not_mod
    (SM.fromDomain_ (as_nat h0 a) * SM.fromDomain_ (as_nat h0 a) * SM.fromDomain_ (as_nat h0 a))


let fmul_by_2 a out =
  let h0 = ST.get () in
  fadd a a out;
  SM.inDomain_mod_is_not_mod (2 * SM.fromDomain_ (as_nat h0 a))


[@CInline]
let fmul_by_3 a result =
  let h0 = ST.get () in
  fmul_by_2 a result;
  let h1 = ST.get () in
  assert (as_nat h1 result == SM.toDomain_ (2 * SM.fromDomain_ (as_nat h0 a) % S.prime));
  fadd a result result;
  let h2 = ST.get() in
  Math.Lemmas.lemma_mod_add_distr (SM.fromDomain_ (as_nat h0 a)) (2 * SM.fromDomain_ (as_nat h0 a)) S.prime;
  SM.inDomain_mod_is_not_mod (3 * SM.fromDomain_ (as_nat h0 a))


[@CInline]
let fmul_by_4 a result  =
  let h0 = ST.get() in
  fmul_by_2 a result;
  fmul_by_2 result result;
  Math.Lemmas.lemma_mod_mul_distr_r 2 (2 * SM.fromDomain_ (as_nat h0 a)) S.prime;
  SL.lemma_brackets 2 2 (SM.fromDomain_ (as_nat h0 a));
  SM.inDomain_mod_is_not_mod (4 * SM.fromDomain_ (as_nat h0 a))


[@CInline]
let fmul_by_8 a result  =
  let h0 = ST.get() in
  fmul_by_4 a result;
  fmul_by_2 result result;
  Math.Lemmas.lemma_mod_mul_distr_r 2 (4 * SM.fromDomain_ (as_nat h0 a)) S.prime;
  SL.lemma_brackets 2 4 (SM.fromDomain_ (as_nat h0 a));
  SM.inDomain_mod_is_not_mod (8 * SM.fromDomain_ (as_nat h0 a))
