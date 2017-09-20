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


module U32 = FStar.UInt32

#reset-options "--max_fuel 0 --z3rlimit 20"

private let lemma_distr_5 a b c d e n : Lemma (n * (a + b + c + d + e) = n*a + n*b + n*c + n*d + n*e)
 = ()

inline_for_extraction let two54m152 =
  assert_norm (pow2 64 > 0x3fffffffffff68); uint64_to_limb 0x3fffffffffff68uL
inline_for_extraction let two54m8   =
  assert_norm (pow2 64 > 0x3ffffffffffff8); uint64_to_limb 0x3ffffffffffff8uL
inline_for_extraction let nineteen  = assert_norm(19 < pow2 64); uint64_to_limb 19uL
inline_for_extraction let mask_51    =
  assert_norm (0x7ffffffffffff < pow2 64); uint64_to_limb 0x7ffffffffffffuL


val add_zero_pre: seqelem -> GTot Type0
let add_zero_pre s =
  let _ = () in
  v (Seq.index s 0) < pow2 63
  /\ v (Seq.index s 1) < pow2 63
  /\ v (Seq.index s 2) < pow2 63
  /\ v (Seq.index s 3) < pow2 63
  /\ v (Seq.index s 4) < pow2 63


val add_zero_spec: s:seqelem{add_zero_pre s} -> Tot seqelem
let add_zero_spec s =
  assert_norm(pow2 63 > 0x3fffffffffff68);
  assert_norm(pow2 63 > 0x3ffffffffffff8);
  Math.Lemmas.pow2_double_sum 63;
  let s = Seq.upd s 0 (Seq.index s 0 +^ two54m152) in
  let s = Seq.upd s 1 (Seq.index s 1 +^ two54m8) in
  let s = Seq.upd s 2 (Seq.index s 2 +^ two54m8) in
  let s = Seq.upd s 3 (Seq.index s 3 +^ two54m8) in
  Seq.upd s 4 (Seq.index s 4 +^ two54m8)


val lemma_seval_5: s:seqelem -> Lemma
  (seval s = v (Seq.index s 0) + pow2 51 * v (Seq.index s 1) 
  + pow2 102 * v (Seq.index s 2) + pow2 153 * v (Seq.index s 3) + pow2 204 * v (Seq.index s 4))
let lemma_seval_5 s =
  assert_norm (pow2 0 = 1);
  lemma_seval_def s 0;
  lemma_seval_def s 1;
  lemma_seval_def s 2;
  lemma_seval_def s 3;
  lemma_seval_def s 4;
  lemma_seval_def s 5


#set-options "--z3rlimit 50"

val lemma_add_zero_spec_: s:seqelem{add_zero_pre s} -> Lemma
  (let s' = add_zero_spec s in
    v (Seq.index s' 0) = v (Seq.index s 0) + 0x3fffffffffff68
    /\ v (Seq.index s' 1) = v (Seq.index s 1) + 0x3ffffffffffff8
    /\ v (Seq.index s' 2) = v (Seq.index s 2) + 0x3ffffffffffff8
    /\ v (Seq.index s' 3) = v (Seq.index s 3) + 0x3ffffffffffff8
    /\ v (Seq.index s' 4) = v (Seq.index s 4) + 0x3ffffffffffff8)
let lemma_add_zero_spec_ s =
  assert_norm(pow2 63 > 0x3fffffffffff68);
  assert_norm(pow2 63 > 0x3ffffffffffff8);
  Math.Lemmas.pow2_double_sum 63


val lemma_add_zero_spec: s:seqelem{add_zero_pre s} -> Lemma
  (seval (add_zero_spec s) % prime = seval s % prime)
let lemma_add_zero_spec s =
  assert_norm(pow2 0 = 1);
  let s' = add_zero_spec s in
  lemma_seval_5 s';
  lemma_seval_5 s;
  assert_norm (0x3fffffffffff68 + pow2 51 * 0x3ffffffffffff8 + pow2 102 * 0x3ffffffffffff8
    + pow2 153 * 0x3ffffffffffff8 + pow2 204 * 0x3ffffffffffff8 = 8 * (pow2 255 - 19));
  lemma_add_zero_spec_ s;
  Math.Lemmas.distributivity_add_right (pow2 51) (v (Seq.index s 1)) 0x3fffffffffff68;
  Math.Lemmas.distributivity_add_right (pow2 102) (v (Seq.index s 2)) 0x3ffffffffffff8;
  Math.Lemmas.distributivity_add_right (pow2 153) (v (Seq.index s 3)) 0x3ffffffffffff8;
  Math.Lemmas.distributivity_add_right (pow2 204) (v (Seq.index s 4)) 0x3ffffffffffff8;
  Math.Lemmas.lemma_mod_plus (seval s) 8 prime;
  ()


val carry_top_pre: seqelem -> GTot Type0
let carry_top_pre s =
  let _ = () in
  19 * (v (Seq.index s 4) / pow2 limb_size) + v (Seq.index s 0) < pow2 64


val carry_top_spec: s:seqelem{carry_top_pre s} -> Tot seqelem
let carry_top_spec s =
  let s4 = Seq.index s 4 in
  let s0 = Seq.index s 0 in
  assert_norm((1 * pow2 limb_size) % pow2 word_size = pow2 limb_size);
  assert_norm(pow2 limb_size > 1);
  let mask = (limb_one <<^ climb_size) -^ limb_one in
  let nineteen = uint64_to_limb 19uL in
  let s4' = s4 &^ mask in
  let s0' = s0 +^ (nineteen *^ (s4 >>^ climb_size)) in
  let s = Seq.upd s 4 s4' in
  Seq.upd s 0 s0'


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 50"

val lemma_carry_top_spec_: s:seqelem{carry_top_pre s} -> Lemma
  (let s' = carry_top_spec s in
    v (Seq.index s' 4) = v (Seq.index s 4) % pow2 limb_size
    /\ v (Seq.index s' 0) = 19 * (v (Seq.index s 4) / pow2 limb_size) + v (Seq.index s 0)
    /\ v (Seq.index s' 1) = v (Seq.index s 1)
    /\ v (Seq.index s' 2) = v (Seq.index s 2)
    /\ v (Seq.index s' 3) = v (Seq.index s 3))
let lemma_carry_top_spec_ s =
  let s' = carry_top_spec s in
  assert_norm((1 * pow2 limb_size) % pow2 word_size = pow2 limb_size);
  assert_norm(pow2 limb_size > 1);
  UInt.logand_mask (v (Seq.index s 4)) limb_size;
  assert(v (Seq.index s' 4) = v (Seq.index s 4) % pow2 limb_size)


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

private let lemma_carry_top_spec_1 (a:nat) (b:nat) : Lemma
  ((pow2 204 * a + b) % prime = (19 * (a / pow2 limb_size) + pow2 204 * (a % pow2 limb_size) + b) % prime)
  = assert_norm(pow2 255 % (pow2 255 - 19) = 19);
    Math.Lemmas.lemma_div_mod a (pow2 limb_size);
    Math.Lemmas.distributivity_add_right (pow2 204) (pow2 limb_size * (a / pow2 limb_size))
                                         (a % pow2 limb_size);
    Math.Lemmas.pow2_plus 204 limb_size;
    cut (pow2 204 * a + b = pow2 255 * (a / pow2 limb_size) + pow2 204 * (a % pow2 limb_size) + b);
    Math.Lemmas.lemma_mod_plus_distr_l (pow2 255 * (a / pow2 limb_size))
                                       (pow2 204 * (a % pow2 limb_size) + b) prime;
    Math.Lemmas.lemma_mod_mul_distr_l (pow2 255) (a / pow2 limb_size) prime;
    Math.Lemmas.lemma_mod_plus_distr_l (19 * (a / pow2 limb_size))
                                       (pow2 204 * (a % pow2 limb_size) + b) prime;
    ()


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val lemma_carry_top_spec: s:seqelem{carry_top_pre s} -> Lemma
  (seval (carry_top_spec s) % prime = seval s % prime)
let lemma_carry_top_spec s =
  let s' = carry_top_spec s in
  lemma_carry_top_spec_ s;
  assert_norm(pow2 255 % (pow2 255 - 19) = 19);
  lemma_seval_5 s;
  lemma_seval_5 s';
  lemma_carry_top_spec_1 (v (Seq.index s 4)) (v (Seq.index s 0) + pow2 51 * v (Seq.index s 1) + pow2 102 * v (Seq.index s 2) + pow2 153 * v (Seq.index s 3))


val reduce_pre: seqelem -> GTot Type0
let reduce_pre s =
  let _ = () in
  v (Seq.index s 0) * 19 < pow2 64


val reduce_spec: s:seqelem{reduce_pre s} -> Tot seqelem
let reduce_spec s =
  let nineteen = uint64_to_limb 19uL in
  let s0 = Seq.index s 0 in
  Seq.upd s 0 (s0 *^ nineteen)


private val lemma_reduce_spec_: s:seqelem{reduce_pre s} -> Lemma
  (let s' = reduce_spec s in
   let s'' = Seq.append (Seq.slice s 1 len) (Seq.slice s 0 1) in
   v (Seq.index s' 1) = v (Seq.index s'' 0)
   /\ v (Seq.index s' 2) = v (Seq.index s'' 1)
   /\ v (Seq.index s' 3) = v (Seq.index s'' 2)
   /\ v (Seq.index s' 4) = v (Seq.index s'' 3)
   /\ v (Seq.index s' 0) = 19 * v (Seq.index s'' 4))
private let lemma_reduce_spec_ s = ()


#reset-options "--max_fuel 0 --z3rlimit 400"

private let lemma_reduce_spec_1_1 (a:nat) (b:nat) (c:nat) (d:nat) (e:nat) : Lemma
  ((pow2 limb_size * (a + pow2 51 * b + pow2 102 * c + pow2 153 * d + pow2 204 * e))
    = (pow2 51 * a + pow2 102 * b + pow2 153 * c + pow2 204 * d + pow2 255 * e))
  = let p51  = pow2 51 in
    let p102 = pow2 102 in
    let p153 = pow2 153 in
    let p204 = pow2 204 in
    Math.Lemmas.pow2_plus limb_size 51;
    Math.Lemmas.pow2_plus limb_size 102;
    Math.Lemmas.pow2_plus limb_size 153;
    Math.Lemmas.pow2_plus limb_size 204;
    lemma_distr_5 (pow2 limb_size) a (p51 * b) (p102 * c) (p153 * d) (p204 * e)


private let lemma_reduce_spec_1 (a:nat) (b:nat) (c:nat) (d:nat) (e:nat) : Lemma
  ((pow2 limb_size * (a + pow2 51 * b + pow2 102 * c + pow2 153 * d + pow2 204 * e)) % prime
    = (19 * e + pow2 51 * a + pow2 102 * b + pow2 153 * c + pow2 204 * d) % prime)
  = lemma_reduce_spec_1_1 a b c d e;
    Math.Lemmas.lemma_mod_plus_distr_l (pow2 255 * e) (pow2 51 * a + pow2 102 * b + pow2 153 * c + pow2 204 * d) prime;
    Math.Lemmas.lemma_mod_mul_distr_l (pow2 255) e prime;
    assert_norm(pow2 255 % (pow2 255 - 19) = 19);
    Math.Lemmas.lemma_mod_plus_distr_l (19 * e) (pow2 51 * a + pow2 102 * b + pow2 153 * c + pow2 204 * d) prime


val lemma_reduce_spec: s:seqelem{reduce_pre s} -> Lemma
  (seval (reduce_spec s) % prime
   = (pow2 limb_size * seval (Seq.append (Seq.slice s 1 len) (Seq.slice s 0 1))) % prime)
let lemma_reduce_spec s =
  let s' = reduce_spec s in
  let s'' = Seq.append (Seq.slice s 1 len) (Seq.slice s 0 1) in
  lemma_reduce_spec_ s;
  assert_norm(pow2 255 % (pow2 255 - 19) = 19);
  lemma_seval_5 s';
  lemma_seval_5 s'';
  lemma_reduce_spec_1 (v (Seq.index s'' 0)) (v (Seq.index s'' 1)) (v (Seq.index s'' 2)) (v (Seq.index s'' 3)) (v (Seq.index s'' 4))


val carry_top_wide_pre: seqelem_wide -> GTot Type0
let carry_top_wide_pre s =
  let _ = () in
  w (Seq.index s 4) / pow2 51 < pow2 64
  /\ 19 * (w (Seq.index s 4) / pow2 limb_size) + w (Seq.index s 0) < pow2 128


val carry_top_wide_spec: s:seqelem_wide{carry_top_wide_pre s} -> Tot seqelem_wide
let carry_top_wide_spec s =
  let b4 = Seq.index s 4 in
  let b0 = Seq.index s 0 in
  let open Hacl.Bignum.Wide in
  (* TODO: a "mk_mask_wide" function *)
  assert_norm((1 * pow2 limb_size) % pow2 (2 * word_size) = pow2 (limb_size));
  assert_norm(pow2 limb_size > 1);
  let mask = (wide_one <<^ climb_size) -^ wide_one in
  let b4' = b4 &^ mask in
  Math.Lemmas.modulo_lemma (w b4 / pow2 limb_size) (pow2 word_size);
  let b0' = b0 +^ (nineteen *^ (wide_to_limb (b4 >>^ climb_size))) in
  let s' = Seq.upd s 4 b4' in
  let s'' = Seq.upd s' 0 b0' in
  s''


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 50"

val lemma_carry_top_wide_spec_: s:seqelem_wide{carry_top_wide_pre s} -> Lemma
  (let s' = carry_top_wide_spec s in
    w (Seq.index s' 4) = w (Seq.index s 4) % pow2 limb_size
    /\ w (Seq.index s' 0) = 19 * (w (Seq.index s 4) / pow2 limb_size) + w (Seq.index s 0)
    /\w (Seq.index s' 1) = w (Seq.index s 1)
    /\ w (Seq.index s' 2) = w (Seq.index s 2)
    /\ w (Seq.index s' 3) = w (Seq.index s 3))
let lemma_carry_top_wide_spec_ s =
  let s' = carry_top_wide_spec s in
  assert_norm((1 * pow2 limb_size) % pow2 (2*word_size) = pow2 limb_size);
  assert_norm(pow2 limb_size > 1);
  UInt.logand_mask (w (Seq.index s 4)) limb_size;
  assert_norm(pow2 51 < pow2 128);
  assert_norm(pow2 64 < pow2 128);
  Math.Lemmas.modulo_lemma (w (Seq.index s 4) / pow2 limb_size) (pow2 64)


val lemma_seval_wide_5: s:seqelem_wide -> Lemma
  (seval_wide s = w (Seq.index s 0) + pow2 51 * w (Seq.index s 1)
  + pow2 102 * w (Seq.index s 2) + pow2 153 * w (Seq.index s 3) + pow2 204 * w (Seq.index s 4))
let lemma_seval_wide_5 s =
  assert_norm (pow2 0 = 1);
  lemma_seval_wide_def s 0;
  lemma_seval_wide_def s 1;
  lemma_seval_wide_def s 2;
  lemma_seval_wide_def s 3;
  lemma_seval_wide_def s 4;
  lemma_seval_wide_def s 5


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val lemma_carry_top_wide_spec: s:seqelem_wide{carry_top_wide_pre s} -> Lemma
  (seval_wide (carry_top_wide_spec s) % prime = seval_wide s % prime)
let lemma_carry_top_wide_spec s =
  let s' = carry_top_wide_spec s in
  lemma_carry_top_wide_spec_ s;
  assert_norm(pow2 255 % (pow2 255 - 19) = 19);
  lemma_seval_wide_5 s;
  lemma_seval_wide_5 s';
  Math.Lemmas.nat_times_nat_is_nat (pow2 51) (w (Seq.index s 1));
  Math.Lemmas.nat_times_nat_is_nat (pow2 102) (w (Seq.index s 2));
  Math.Lemmas.nat_times_nat_is_nat (pow2 153) (w (Seq.index s 3));
  lemma_carry_top_spec_1 (w (Seq.index s 4)) (w (Seq.index s 0) + pow2 51 * w (Seq.index s 1) + pow2 102 * w (Seq.index s 2) + pow2 153 * w (Seq.index s 3))
