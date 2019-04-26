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


#set-options "--initial_fuel 0 --max_fuel 0"

inline_for_extraction let mask_2_44 : p:t{v p = pow2 44 - 1} =
  assert_norm (pow2 64 = 0x10000000000000000);
  assert_norm(pow2 44 - 1 = 0xfffffffffff);  uint64_to_limb 0xfffffffffffuL
inline_for_extraction let mask_2_42 : p:Hacl.Bignum.Wide.t{w p = pow2 42 - 1} =
  assert_norm (pow2 64 = 0x10000000000000000); assert_norm(pow2 42 - 1 = 0x3ffffffffff);
  limb_to_wide (uint64_to_limb 0x3ffffffffffuL)
inline_for_extraction let mask_2_42' : p:t{v p = pow2 42 - 1} =
  assert_norm (pow2 64 = 0x10000000000000000); assert_norm(pow2 42 - 1 = 0x3ffffffffff);
  uint64_to_limb 0x3ffffffffffuL
inline_for_extraction let five : t   =
  assert_norm (pow2 64 > 5); uint64_to_limb 5uL


val reduce_pre: seqelem -> GTot Type0
let reduce_pre s =
  let _ = () in
  v (Seq.index s 0) * 20 < pow2 64


#set-options "--z3rlimit 20"

val reduce_spec: s:seqelem{reduce_pre s} -> Tot (s':seqelem)
let reduce_spec s =
  assert_norm(pow2 4 = 16);
  assert_norm(pow2 2 = 4);
  let s0 = Seq.index s 0 in
  let s0_16 = s0 <<^ 4ul in
  Math.Lemmas.modulo_lemma (v s0 * 16) (pow2 64);
  let s0_4 = s0 <<^ 2ul in
  Math.Lemmas.modulo_lemma (v s0 * 4) (pow2 64);
  let s0_20 = s0_16 +^ s0_4 in
  Seq.upd s 0 s0_20


private val lemma_reduce_spec_: s:seqelem{reduce_pre s} -> Lemma
  (let s' = reduce_spec s in
   let s'' = Seq.append (Seq.slice s 1 len) (Seq.slice s 0 1) in
   v (Seq.index s' 1) = v (Seq.index s'' 0)
   /\ v (Seq.index s' 2) = v (Seq.index s'' 1)
   /\ v (Seq.index s' 0) = 20 * v (Seq.index s'' 2))
private let lemma_reduce_spec_ s =
  let s0 = Seq.index s 0 in
  assert_norm(pow2 4 = 16);
  assert_norm(pow2 2 = 4);
  Math.Lemmas.modulo_lemma (v s0 * 16) (pow2 64);
  Math.Lemmas.modulo_lemma (v s0 * 4) (pow2 64)


private let lemma_reduce_spec_1_1 (a:nat) (b:nat) (c:nat) : Lemma
  ((pow2 limb_size * (a + pow2 44 * b + pow2 88 * c))
    = (pow2 44 * a + pow2 88 * b + pow2 132 * c))
  = Math.Lemmas.pow2_plus limb_size 44;
    Math.Lemmas.pow2_plus limb_size 88

#set-options "--z3rlimit 20"

private let lemma_reduce_spec_1 (a:nat) (b:nat) (c:nat) : Lemma
  ((pow2 limb_size * (a + pow2 44 * b + pow2 88 * c)) % prime
    = (20 * c + pow2 44 * a + pow2 88 * b) % prime)
  = lemma_reduce_spec_1_1 a b c;
    Math.Lemmas.lemma_mod_plus_distr_l (pow2 132 * c) (pow2 44 * a + pow2 88 * b) prime;
    Math.Lemmas.lemma_mod_mul_distr_l (pow2 132) c prime;
    assert_norm(pow2 132 % (pow2 130 - 5) = 20);
    Math.Lemmas.lemma_mod_plus_distr_l (20 * c) (pow2 44 * a + pow2 88 * b) prime


val lemma_seval_3: s:seqelem -> Lemma
  (seval s = v (Seq.index s 0) + pow2 44 * v (Seq.index s 1) + pow2 88 * v (Seq.index s 2))
let lemma_seval_3 s =
  assert_norm (pow2 0 = 1);
  lemma_seval_def s 0;
  lemma_seval_def s 1;
  lemma_seval_def s 2;
  lemma_seval_def s 3


val lemma_reduce_spec: s:seqelem{reduce_pre s} -> Lemma
  (seval (reduce_spec s) % prime
   = (pow2 limb_size * seval (Seq.append (Seq.slice s 1 len) (Seq.slice s 0 1))) % prime)
let lemma_reduce_spec s =
  let s' = reduce_spec s in
  let s'' = Seq.append (Seq.slice s 1 len) (Seq.slice s 0 1) in
  lemma_reduce_spec_ s;
  assert_norm(pow2 132 % (pow2 130 - 5) = 20);
  lemma_seval_3 s';
  lemma_seval_3 s'';
  lemma_reduce_spec_1 (v (Seq.index s'' 0)) (v (Seq.index s'' 1)) (v (Seq.index s'' 2))


val carry_top_pre: seqelem -> GTot Type0
let carry_top_pre s =
  let _ = () in
  5 * (v (Seq.index s 2) / pow2 42) < pow2 64
  /\ 5 * (v (Seq.index s 2) / pow2 42) + v (Seq.index s 0) < pow2 64

#set-options "--z3rlimit 20"

val carry_top_spec: s:seqelem{carry_top_pre s} -> Tot seqelem
let carry_top_spec s =
  let b2 = Seq.index s 2 in
  let b0 = Seq.index s 0 in
  assert_norm((1 * pow2 limb_size) % pow2 (word_size) = pow2 (limb_size));
  assert_norm(pow2 limb_size > 1);
  let b2' = b2 &^ mask_2_42' in
  Math.Lemmas.modulo_lemma (v b2 / pow2 42) (pow2 word_size);
  let b2_42 = b2 >>^ 42ul in
  cut (v b2_42 = v b2 / pow2 42);
  assert_norm(pow2 2 = 4); Math.Lemmas.modulo_lemma (v b2_42 * 4) (pow2 64);
  let b2_5 = (b2_42 <<^ 2ul) +^ b2_42 in
  let b0' = b0 +^ b2_5 in
  let s' = Seq.upd s 2 b2' in
  Seq.upd s' 0 b0'


#set-options "--z3rlimit 20"

val lemma_carry_top_spec_: s:seqelem{carry_top_pre s} -> Lemma
  (let s' = carry_top_spec s in
    v (Seq.index s' 2) = v (Seq.index s 2) % pow2 42
    /\ v (Seq.index s' 0) = 5 * (v (Seq.index s 2) / pow2 42) + v (Seq.index s 0)
    /\ v (Seq.index s' 1) = v (Seq.index s 1))
let lemma_carry_top_spec_ s =
  let b2 = Seq.index s 2 in
  Math.Lemmas.modulo_lemma (v b2 / pow2 42) (pow2 word_size);
  let b0 = Seq.index s 0 in
  let b2' = b2 &^ mask_2_42' in
  UInt.logand_mask (v (Seq.index s 2)) 42;
  let b2_42 = (b2 >>^ 42ul) in
  cut (v b2_42 = v b2 / pow2 42);
  assert_norm(pow2 2 = 4); Math.Lemmas.modulo_lemma (v b2_42 * 4) (pow2 64);
  let s' = carry_top_spec s in
  cut (v (Seq.index s' 2) = v (Seq.index s 2) % pow2 42);
  cut (v (Seq.index s' 1) = v (Seq.index s 1));
  cut (v (Seq.index s' 0) = 5 * (v (Seq.index s 2) / pow2 42) + v (Seq.index s 0));
  ()


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

private val lemma_mod_0: a:nat -> b:nat -> c:nat -> Lemma
  ( (a + b * c) % prime = (a + (b % prime) * c) % prime)
private let lemma_mod_0 a b c =
  Math.Lemmas.lemma_mod_plus_distr_l (b * c) a prime;
  Math.Lemmas.lemma_mod_mul_distr_l (b) c prime;
  Math.Lemmas.lemma_mod_plus_distr_l ((b % prime) * c) a prime

#set-options "--z3rlimit 20"

private let lemma_0 (a:nat) (b:nat) : Lemma
  ( (a + pow2 88 * (b % pow2 42) + pow2 130 * (b / pow2 42)) % prime
    = (a + pow2 88 * b) % prime)
  = Math.Lemmas.pow2_plus 88 42;
  Math.Lemmas.lemma_div_mod (b) (pow2 42);
  Math.Lemmas.distributivity_add_right (pow2 88) (b % pow2 42) (pow2 42 * (b / pow2 42))


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 50"

val lemma_carry_top_spec: s:seqelem{carry_top_pre s} -> Lemma
  (seval (carry_top_spec s) % prime = seval s % prime)
let lemma_carry_top_spec s =
  let s' = carry_top_spec s in
  lemma_carry_top_spec_ s;
  assert_norm(pow2 130 % (pow2 130 - 5) = 5);
  lemma_seval_3 s;
  lemma_seval_3 s';
  Math.Lemmas.nat_times_nat_is_nat (pow2 44) (v (Seq.index s 1));
  Math.Lemmas.nat_times_nat_is_nat (pow2 88) (v (Seq.index s 2));
  let z0 = seval (carry_top_spec s) in
  cut (z0 = v (Seq.index s' 0) + pow2 44 * v (Seq.index s' 1) + pow2 88 * v (Seq.index s' 2) );
  cut (z0 = v (Seq.index s 0) + 5 * (v (Seq.index s 2) / pow2 42) + pow2 44 * v (Seq.index s 1) + pow2 88 * (v (Seq.index s 2) % pow2 42) );
  lemma_mod_0 (v (Seq.index s 0)  + pow2 44 * v (Seq.index s 1) + pow2 88 * (v (Seq.index s 2) % pow2 42)) (pow2 130) (v (Seq.index s 2) / pow2 42);
  cut (z0 % prime = (v (Seq.index s 0) + pow2 44 * v (Seq.index s 1) + pow2 88 * (v (Seq.index s 2) % pow2 42) + pow2 130 * (v (Seq.index s 2) / pow2 42)) % prime);
  lemma_0 (v (Seq.index s 0) + pow2 44 * v (Seq.index s 1)) (v (Seq.index s 2))


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val carry_top_wide_pre: seqelem_wide -> GTot Type0
let carry_top_wide_pre s =
  let _ = () in
  5 * (w (Seq.index s 2) / pow2 42) < pow2 64
  /\ 5 * (w (Seq.index s 2) / pow2 42) + w (Seq.index s 0) < pow2 128

#set-options "--z3rlimit 20"

val carry_top_wide_spec: s:seqelem_wide{carry_top_wide_pre s} -> Tot seqelem_wide
let carry_top_wide_spec s =
  let b2 = Seq.index s 2 in
  let b0 = Seq.index s 0 in
  let open Hacl.Bignum.Wide in
  assert_norm((1 * pow2 limb_size) % pow2 (2 * word_size) = pow2 (limb_size));
  assert_norm(pow2 limb_size > 1);
  let b2' = b2 &^ mask_2_42 in
  Math.Lemmas.modulo_lemma (v b2 / pow2 42) (pow2 word_size);
  let b2_42 = wide_to_limb (b2 >>^ 42ul) in
  cut (Hacl.Bignum.Limb.v b2_42 = v b2 / pow2 42);
  assert_norm(pow2 2 = 4); Math.Lemmas.modulo_lemma (Hacl.Bignum.Limb.v b2_42 * 4) (pow2 64);
  let b2_5 = limb_to_wide Hacl.Bignum.Limb.((b2_42 <<^ 2ul) +^ b2_42) in
  let b0' = b0 +^ b2_5 in
  let s' = Seq.upd s 2 b2' in
  Seq.upd s' 0 b0'


#set-options "--z3rlimit 200"

val lemma_carry_top_wide_spec_: s:seqelem_wide{carry_top_wide_pre s} -> Lemma
  (let s' = carry_top_wide_spec s in
    w (Seq.index s' 2) = w (Seq.index s 2) % pow2 42
    /\ w (Seq.index s' 0) = 5 * (w (Seq.index s 2) / pow2 42) + w (Seq.index s 0)
    /\ w (Seq.index s' 1) = w (Seq.index s 1))
let lemma_carry_top_wide_spec_ s =
  let b2 = Seq.index s 2 in
  let b0 = Seq.index s 0 in
  let open Hacl.Bignum.Wide in
  let b2' = b2 &^ mask_2_42 in
  UInt.logand_mask (w (Seq.index s 2)) 42;
  Math.Lemmas.modulo_lemma (v b2 / pow2 42) (pow2 word_size);
  let b2_42 = wide_to_limb (b2 >>^ 42ul) in
  cut (Hacl.Bignum.Limb.v b2_42 = v b2 / pow2 42);
  assert_norm(pow2 2 = 4); Math.Lemmas.modulo_lemma (Hacl.Bignum.Limb.v b2_42 * 4) (pow2 64);
  let s' = carry_top_wide_spec s in
  cut (w (Seq.index s' 2) = w (Seq.index s 2) % pow2 42);
  cut (w (Seq.index s' 1) = w (Seq.index s 1));
  cut (w (Seq.index s' 0) = 5 * (w (Seq.index s 2) / pow2 42) + w (Seq.index s 0));
  ()


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val lemma_seval_wide_3: s:seqelem_wide -> Lemma
  (seval_wide s = w (Seq.index s 0) + pow2 44 * w (Seq.index s 1) + pow2 88 * w (Seq.index s 2))
let lemma_seval_wide_3 s =
  assert_norm (pow2 0 = 1);
  lemma_seval_wide_def s 0;
  lemma_seval_wide_def s 1;
  lemma_seval_wide_def s 2;
  lemma_seval_wide_def s 3


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 50"

val lemma_carry_top_wide_spec: s:seqelem_wide{carry_top_wide_pre s} -> Lemma
  (seval_wide (carry_top_wide_spec s) % prime = seval_wide s % prime)
let lemma_carry_top_wide_spec s =
  let s' = carry_top_wide_spec s in
  lemma_carry_top_wide_spec_ s;
  assert_norm(pow2 130 % (pow2 130 - 5) = 5);
  lemma_seval_wide_3 s;
  lemma_seval_wide_3 s';
  Math.Lemmas.nat_times_nat_is_nat (pow2 44) (w (Seq.index s 1));
  Math.Lemmas.nat_times_nat_is_nat (pow2 88) (w (Seq.index s 2));
  let s' = carry_top_wide_spec s in
  let z0 = seval_wide (carry_top_wide_spec s) in
  cut (z0 = w (Seq.index s' 0) + pow2 44 * w (Seq.index s' 1) + pow2 88 * w (Seq.index s' 2) );
  cut (z0 = w (Seq.index s 0) + 5 * (w (Seq.index s 2) / pow2 42) + pow2 44 * w (Seq.index s 1) + pow2 88 * (w (Seq.index s 2) % pow2 42) );
  lemma_mod_0 (w (Seq.index s 0)  + pow2 44 * w (Seq.index s 1) + pow2 88 * (w (Seq.index s 2) % pow2 42)) (pow2 130) (w (Seq.index s 2) / pow2 42);
  cut (z0 % prime = (w (Seq.index s 0) + pow2 44 * w (Seq.index s 1) + pow2 88 * (w (Seq.index s 2) % pow2 42) + pow2 130 * (w (Seq.index s 2) / pow2 42)) % prime);
  lemma_0 (w (Seq.index s 0) + pow2 44 * w (Seq.index s 1)) (w (Seq.index s 2))
