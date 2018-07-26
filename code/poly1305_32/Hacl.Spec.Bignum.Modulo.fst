module Hacl.Spec.Bignum.Modulo

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul
open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Bignum.Limb


#reset-options "--max_fuel 0"

inline_for_extraction let mask_2_26 : p:t{v p = pow2 26 - 1} =
  assert_norm (pow2 32 = 0x100000000);
  assert_norm(pow2 26 - 1 = 0x3ffffff); uint32_to_limb 0x3fffffful

inline_for_extraction let five : limb   =
  assert_norm (pow2 64 > 5); uint32_to_limb 5ul

val reduce_pre: seqelem -> GTot Type0
let reduce_pre s =
  v (Seq.index s 0) * 5 < pow2 32

val reduce_spec: s:seqelem{reduce_pre s} -> Tot (s':seqelem)
let reduce_spec s =
  assert_norm(pow2 0 = 1);
  assert_norm(pow2 2 = 4);
  let s0 = Seq.index s 0 in
  let s0_4 = s0 <<^ 2ul in
  Math.Lemmas.modulo_lemma (v s0 * 4) (pow2 32);
  let s0_5 = s0_4 +^ s0 in
  Seq.upd s 0 s0_5


private val lemma_reduce_spec_: s:seqelem{reduce_pre s} -> Lemma
  (let s' = reduce_spec s in
   let s'' = Seq.append (Seq.slice s 1 len) (Seq.slice s 0 1) in
   v (Seq.index s' 1) = v (Seq.index s'' 0)
   /\ v (Seq.index s' 2) = v (Seq.index s'' 1)
   /\ v (Seq.index s' 3) = v (Seq.index s'' 2)
   /\ v (Seq.index s' 4) = v (Seq.index s'' 3)
   /\ v (Seq.index s' 0) = 5 * v (Seq.index s'' 4))
private let lemma_reduce_spec_ s =
  let s0 = Seq.index s 0 in
  assert_norm(pow2 2 = 4);
  Math.Lemmas.modulo_lemma (v s0 * 4) (pow2 32)


private let lemma_distr_5 a b c d e f : Lemma (a * (b + c + d + e + f) = a * b + a * c + a * d + a * e + a * f) = ()


#reset-options "--z3rlimit 20 --max_fuel 0"

private let lemma_reduce_spec_1_1 (a:nat) (b:nat) (c:nat) (d:nat) (e:nat) : Lemma
  ((pow2 limb_size * (a + pow2 26 * b + pow2 52 * c + pow2 78 * d + pow2 104 * e))
    = (pow2 26 * a + pow2 52 * b + pow2 78 * c + pow2 104 * d + pow2 130 * e))
  = assert(limb_size = 26);
    Math.Lemmas.pow2_plus limb_size 26;
    Math.Lemmas.pow2_plus limb_size 52;
    Math.Lemmas.pow2_plus limb_size 78;
    Math.Lemmas.pow2_plus limb_size 104;
    lemma_distr_5 (pow2 limb_size) a (pow2 26 * b) (pow2 52 * c) (pow2 78 * d) (pow2 104 * e);
    Math.Lemmas.paren_mul_right (pow2 26) (pow2 26) b;
    Math.Lemmas.paren_mul_right (pow2 26) (pow2 52) c;
    Math.Lemmas.paren_mul_right (pow2 26) (pow2 78) d;
    Math.Lemmas.paren_mul_right (pow2 26) (pow2 104) e


#set-options "--z3rlimit 20"

private let lemma_reduce_spec_1 (a:nat) (b:nat) (c:nat) (d:nat) (e:nat) : Lemma
  ((pow2 limb_size * (a + pow2 26 * b + pow2 52 * c + pow2 78 * d + pow2 104 * e)) % prime
    = (5 * e + pow2 26 * a + pow2 52 * b + pow2 78 * c + pow2 104 * d) % prime)
  = lemma_reduce_spec_1_1 a b c d e;
    Math.Lemmas.lemma_mod_plus_distr_l (pow2 130 * e) (pow2 26 * a + pow2 52 * b + pow2 78 * c + pow2 104 * d) prime;
    Math.Lemmas.lemma_mod_mul_distr_l (pow2 130) e prime;
    assert_norm(pow2 130 % (pow2 130 - 5) = 5);
    Math.Lemmas.lemma_mod_plus_distr_l (5 * e) (pow2 26 * a + pow2 52 * b + pow2 78 * c + pow2 104 * d) prime

val lemma_seval_5: s:seqelem -> Lemma
  (seval s = v (Seq.index s 0) + pow2 26 * v (Seq.index s 1) + pow2 52 * v (Seq.index s 2) + pow2 78 * v (Seq.index s 3) + pow2 104 * v (Seq.index s 4))
let lemma_seval_5 s =
  assert_norm (pow2 0 = 1);
  lemma_seval_def s 0;
  lemma_seval_def s 1;
  lemma_seval_def s 2;
  lemma_seval_def s 3;
  lemma_seval_def s 4;
  lemma_seval_def s 5


#reset-options "--z3rlimit 20 --max_fuel 0"

val lemma_reduce_spec: s:seqelem{reduce_pre s} -> Lemma
  (seval (reduce_spec s) % prime
   = (pow2 limb_size * seval (Seq.append (Seq.slice s 1 len) (Seq.slice s 0 1))) % prime)
let lemma_reduce_spec s =
  let s' = reduce_spec s in
  let s'' = Seq.append (Seq.slice s 1 len) (Seq.slice s 0 1) in
  lemma_reduce_spec_ s;
  assert_norm(pow2 130 % (pow2 130 - 5) = 5);
  lemma_seval_5 s';
  lemma_seval_5 s'';
  lemma_reduce_spec_1 (v (Seq.index s'' 0)) (v (Seq.index s'' 1)) (v (Seq.index s'' 2)) (v (Seq.index s'' 3)) (v (Seq.index s'' 4))


val carry_top_pre: seqelem -> GTot Type0
let carry_top_pre s =
  let _ = () in
  5 * (v (Seq.index s 4) / pow2 26) < pow2 32
  /\ 5 * (v (Seq.index s 4) / pow2 26) + v (Seq.index s 0) < pow2 32

val carry_top_spec: s:seqelem{carry_top_pre s} -> Tot seqelem
let carry_top_spec s =
  let b4 = Seq.index s 4 in
  let b0 = Seq.index s 0 in
  assert_norm((1 * pow2 limb_size) % pow2 (word_size) = pow2 (limb_size));
  assert_norm(pow2 limb_size > 1);
  let b4' = b4 &^ mask_2_26 in
  Math.Lemmas.modulo_lemma (v b4 / pow2 26) (pow2 word_size);
  let b4_26 = b4 >>^ 26ul in
  cut (v b4_26 = v b4 / pow2 26);
  assert_norm(pow2 2 = 4); Math.Lemmas.modulo_lemma (v b4_26 * 4) (pow2 32);
  let b2_5 = (b4_26 <<^ 2ul) +^ b4_26 in
  let b0' = b0 +^ b2_5 in
  let s' = Seq.upd s 4 b4' in
  Seq.upd s' 0 b0'


val lemma_carry_top_spec_: s:seqelem{carry_top_pre s} -> Lemma
  (let s' = carry_top_spec s in
    v (Seq.index s' 4) = v (Seq.index s 4) % pow2 26
    /\ v (Seq.index s' 0) = 5 * (v (Seq.index s 4) / pow2 26) + v (Seq.index s 0)
    /\ v (Seq.index s' 1) = v (Seq.index s 1)
    /\ v (Seq.index s' 2) = v (Seq.index s 2)
    /\ v (Seq.index s' 3) = v (Seq.index s 3))
let lemma_carry_top_spec_ s =
  let b4 = Seq.index s 4 in
  Math.Lemmas.modulo_lemma (v b4 / pow2 26) (pow2 word_size);
  let b0 = Seq.index s 0 in
  let b4' = b4 &^ mask_2_26 in
  UInt.logand_mask (v (Seq.index s 4)) 26;
  let b4_26 = (b4 >>^ 26ul) in
  cut (v b4_26 = v b4 / pow2 26);
  assert_norm(pow2 2 = 4); Math.Lemmas.modulo_lemma (v b4_26 * 4) (pow2 32);
  let s' = carry_top_spec s in
  cut (v (Seq.index s' 4) = v (Seq.index s 4) % pow2 26);
  cut (v (Seq.index s' 3) = v (Seq.index s 3));
  cut (v (Seq.index s' 2) = v (Seq.index s 2));
  cut (v (Seq.index s' 1) = v (Seq.index s 1));
  cut (v (Seq.index s' 0) = 5 * (v (Seq.index s 4) / pow2 26) + v (Seq.index s 0));
  ()

#reset-options "--max_fuel 0 --z3rlimit 20"

private val lemma_mod_0: a:nat -> b:nat -> c:nat -> Lemma
  ( (a + b * c) % prime = (a + (b % prime) * c) % prime)
private let lemma_mod_0 a b c =
  Math.Lemmas.lemma_mod_plus_distr_l (b * c) a prime;
  Math.Lemmas.lemma_mod_mul_distr_l (b) c prime;
  Math.Lemmas.lemma_mod_plus_distr_l ((b % prime) * c) a prime


#reset-options "--max_fuel 0 --z3rlimit 100 --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr native"

private let lemma_0 (a:nat) (b:nat) : Lemma
  ( (a + pow2 104 * (b % pow2 26) + pow2 130 * (b / pow2 26)) % prime
    = (a + pow2 104 * b) % prime)
  = 
  Math.Lemmas.pow2_plus 104 26;
  Math.Lemmas.lemma_div_mod (b) (pow2 26);
  Math.Lemmas.distributivity_add_right (pow2 104) (b % pow2 26) (pow2 26 * (b / pow2 26))

#reset-options "--max_fuel 0 --z3rlimit 20"

val carry_top_wide_pre: seqelem_wide -> GTot Type0
let carry_top_wide_pre s =
  let _ = () in
  5 * (w (Seq.index s 4) / pow2 26) < pow2 32
  /\ 5 * (w (Seq.index s 4) / pow2 26) + w (Seq.index s 0) < pow2 64

val lemma_seval_wide_3: s:seqelem_wide -> Lemma
  (seval_wide s = w (Seq.index s 0) + pow2 26 * w (Seq.index s 1) + pow2 52 * w (Seq.index s 2) + pow2 78 * w (Seq.index s 3) + pow2 104 * w (Seq.index s 4))
let lemma_seval_wide_3 s =
  assert_norm (pow2 0 = 1);
  lemma_seval_wide_def s 0;
  lemma_seval_wide_def s 1;
  lemma_seval_wide_def s 2;
  lemma_seval_wide_def s 3;
  lemma_seval_wide_def s 4;
  lemma_seval_wide_def s 5

val carry_top_wide_spec: s:seqelem_wide{carry_top_wide_pre s} -> Tot seqelem_wide
let carry_top_wide_spec s =
  let b4 = Seq.index s 4 in
  let b0 = Seq.index s 0 in
  let open Hacl.Bignum.Wide in
  assert_norm((1 * pow2 limb_size) % pow2 (2 * word_size) = pow2 (limb_size));
  assert_norm(pow2 limb_size > 1);
  let b4' = b4 &^ (limb_to_wide mask_2_26) in
  Math.Lemmas.modulo_lemma (v b4 / pow2 26) (pow2 word_size);
  let b4_26 = wide_to_limb (b4 >>^ 26ul) in
  cut (Hacl.Bignum.Limb.v b4_26 = v b4 / pow2 26);
  assert_norm(pow2 2 = 4); Math.Lemmas.modulo_lemma (Hacl.Bignum.Limb.v b4_26 * 4) (pow2 64);
  let b4_5 = limb_to_wide Hacl.Bignum.Limb.((b4_26 <<^ 2ul) +^ b4_26) in
  let b0' = b0 +^ b4_5 in
  let s' = Seq.upd s 4 b4' in
  Seq.upd s' 0 b0'

val lemma_carry_top_wide_spec_: s:seqelem_wide{carry_top_wide_pre s} -> Lemma
  (let s' = carry_top_wide_spec s in
    w (Seq.index s' 4) = w (Seq.index s 4) % pow2 26
    /\ w (Seq.index s' 0) = 5 * (w (Seq.index s 4) / pow2 26) + w (Seq.index s 0)
    /\ w (Seq.index s' 1) = w (Seq.index s 1)
    /\ w (Seq.index s' 2) = w (Seq.index s 2)
    /\ w (Seq.index s' 3) = w (Seq.index s 3))
let lemma_carry_top_wide_spec_ s =
  let b4 = Seq.index s 4 in
  let b0 = Seq.index s 0 in
  let open Hacl.Bignum.Wide in
  let b4' = b4 &^ (limb_to_wide mask_2_26) in
  UInt.logand_mask (w (Seq.index s 4)) 26;
  Math.Lemmas.modulo_lemma (v b4 / pow2 26) (pow2 word_size);
  let b4_26 = wide_to_limb (b4 >>^ 26ul) in
  cut (Hacl.Bignum.Limb.v b4_26 = v b4 / pow2 26);
  assert_norm(pow2 2 = 4); Math.Lemmas.modulo_lemma (Hacl.Bignum.Limb.v b4_26 * 4) (pow2 64);
  let s' = carry_top_wide_spec s in
  cut (w (Seq.index s' 4) = w (Seq.index s 4) % pow2 26);
  cut (w (Seq.index s' 1) = w (Seq.index s 1));
  cut (w (Seq.index s' 2) = w (Seq.index s 2));
  cut (w (Seq.index s' 3) = w (Seq.index s 3));
  cut (w (Seq.index s' 0) = 5 * (w (Seq.index s 4) / pow2 26) + w (Seq.index s 0));
  ()

#set-options "--max_fuel 0 --z3rlimit 50"

val lemma_carry_top_wide_spec: s:seqelem_wide{carry_top_wide_pre s} -> Lemma
  (seval_wide (carry_top_wide_spec s) % prime = seval_wide s % prime)
let lemma_carry_top_wide_spec s =
  let s' = carry_top_wide_spec s in
  lemma_carry_top_wide_spec_ s;
  assert_norm(pow2 130 % (pow2 130 - 5) = 5);
  lemma_seval_wide_3 s;
  lemma_seval_wide_3 s';
  Math.Lemmas.nat_times_nat_is_nat (pow2 26) (w (Seq.index s 1));
  Math.Lemmas.nat_times_nat_is_nat (pow2 52) (w (Seq.index s 2));
  Math.Lemmas.nat_times_nat_is_nat (pow2 78) (w (Seq.index s 3));
  Math.Lemmas.nat_times_nat_is_nat (pow2 104) (w (Seq.index s 4));
  let s' = carry_top_wide_spec s in
  let z0 = seval_wide (carry_top_wide_spec s) in
  cut (z0 = w (Seq.index s' 0) + pow2 26 * w (Seq.index s' 1) + pow2 52 * w (Seq.index s' 2) + pow2 78 * w (Seq.index s' 3) + pow2 104 * w (Seq.index s' 4) );
  cut (z0 = w (Seq.index s 0) + 5 * (w (Seq.index s 4) / pow2 26) + pow2 26 * w (Seq.index s 1) + pow2 52 * w (Seq.index s 2) + pow2 78 * w (Seq.index s 3) + pow2 104 * (w (Seq.index s 4) % pow2 26) );
  lemma_mod_0 (w (Seq.index s 0)  + pow2 26 * w (Seq.index s 1) + pow2 52 * w (Seq.index s 2) + pow2 78 * w (Seq.index s 3) + pow2 104 * (w (Seq.index s 4) % pow2 26)) (pow2 130) (w (Seq.index s 4) / pow2 26);
  cut (z0 % prime = (w (Seq.index s 0) + pow2 26 * w (Seq.index s 1) + pow2 52 * w (Seq.index s 2) + pow2 78 * w (Seq.index s 3) + pow2 104 * (w (Seq.index s 4) % pow2 26) + pow2 130 * (w (Seq.index s 4) / pow2 26)) % prime);
  lemma_0 (w (Seq.index s 0) + pow2 26 * w (Seq.index s 1) + pow2 52 * w (Seq.index s 2) + pow2 78 * w (Seq.index s 3)) (w (Seq.index s 4))


val lemma_carry_top_spec: s:seqelem{carry_top_pre s} -> Lemma
  (seval (carry_top_spec s) % prime = seval s % prime)
let lemma_carry_top_spec s =
  let s' = carry_top_spec s in
  lemma_carry_top_spec_ s;
  assert_norm(pow2 130 % (pow2 130 - 5) = 5);
  lemma_seval_5 s;
  lemma_seval_5 s';
  Math.Lemmas.nat_times_nat_is_nat (pow2 26) (v (Seq.index s 1));
  Math.Lemmas.nat_times_nat_is_nat (pow2 52) (v (Seq.index s 2));
  Math.Lemmas.nat_times_nat_is_nat (pow2 78) (v (Seq.index s 3));
  Math.Lemmas.nat_times_nat_is_nat (pow2 104) (v (Seq.index s 4));
  let s' = carry_top_spec s in
  let z0 = seval (carry_top_spec s) in
  cut (z0 = v (Seq.index s' 0) + pow2 26 * v (Seq.index s' 1) + pow2 52 * v (Seq.index s' 2) + pow2 78 * v (Seq.index s' 3) + pow2 104 * v (Seq.index s' 4) );
  cut (z0 = v (Seq.index s 0) + 5 * (v (Seq.index s 4) / pow2 26) + pow2 26 * v (Seq.index s 1) + pow2 52 * v (Seq.index s 2) + pow2 78 * v (Seq.index s 3) + pow2 104 * (v (Seq.index s 4) % pow2 26) );
  lemma_mod_0 (v (Seq.index s 0)  + pow2 26 * v (Seq.index s 1) + pow2 52 * v (Seq.index s 2) + pow2 78 * v (Seq.index s 3) + pow2 104 * (v (Seq.index s 4) % pow2 26)) (pow2 130) (v (Seq.index s 4) / pow2 26);
  cut (z0 % prime = (v (Seq.index s 0) + pow2 26 * v (Seq.index s 1) + pow2 52 * v (Seq.index s 2) + pow2 78 * v (Seq.index s 3) + pow2 104 * (v (Seq.index s 4) % pow2 26) + pow2 130 * (v (Seq.index s 4) / pow2 26)) % prime);
  lemma_0 (v (Seq.index s 0) + pow2 26 * v (Seq.index s 1) + pow2 52 * v (Seq.index s 2) + pow2 78 * v (Seq.index s 3)) (v (Seq.index s 4))
