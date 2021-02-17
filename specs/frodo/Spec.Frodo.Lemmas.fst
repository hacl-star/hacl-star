module Spec.Frodo.Lemmas

open FStar.Mul
open Lib.IntTypes

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val lemma_mask_cast:
  mask:uint16{v mask = 0 \/ v mask = v (ones U16 SEC)} -> Lemma
  ((v mask = 0 ==> v (to_u8 mask) = 0) /\
   (v mask = v (ones U16 SEC) ==> v (to_u8 mask) = v (ones U8 SEC)))

let lemma_mask_cast mask = ()


// To avoid integral promotion, a cast to uint_16 is needed
// https://en.cppreference.com/w/cpp/language/operator_arithmetic
val lemma_frodo_sample:
  a:uint16{v a < pow2 15} -> b:uint16{v b < pow2 15} -> Lemma
  (let c0 = if v a > v b then 1 else 0 in
   let c1 = to_u16 (to_u32 (b -. a)) >>. 15ul in
   v c1 == c0)

let lemma_frodo_sample a b =
  let c = to_u16 (to_u32 (b -. a)) in
  assert (v c < modulus U16);
  Math.Lemmas.lemma_div_lt (uint_v c) 16 15;
  let c1 = c >>. 15ul in
  assert (v c1 = v c / pow2 15);
  Math.Lemmas.pow2_minus 16 15;
  assert (v c1 = 0 \/ v c1 = 1)


val modulo_pow2_u16:
  a:uint16 -> b:size_nat{b < 16} -> Lemma
  (v a % pow2 b == v (a &. ((u16 1 <<. size b) -. u16 1)))
let modulo_pow2_u16 a b =
  Math.Lemmas.pow2_lt_compat 16 b;
  mod_mask_lemma #U16 a (size b);
  assert (v (mod_mask #U16 #SEC (size b)) == v ((u16 1 <<. size b) -. u16 1))


val modulo_pow2_u64:
  a:uint64 -> b:size_nat{b < 64} -> Lemma
  (v a % pow2 b == v (a &. ((u64 1 <<. size b) -. u64 1)))
let modulo_pow2_u64 a b =
  Math.Lemmas.pow2_lt_compat 64 b;
  mod_mask_lemma #U64 a (size b);
  assert (v (mod_mask #U64 #SEC (size b)) == v ((u64 1 <<. size b) -. u64 1))


val lognot_plus_one:
  e:uint16 -> Lemma (v (lognot e) == modulus U16 - v e - 1)
let lognot_plus_one e =
  lognot_spec e;
  assert (v (lognot e) == UInt.lognot #16 (v e));
  UInt.lemma_lognot_value_mod #16 (v e);
  assert (v (lognot e) == pow2 16 - v e - 1)


val lemma_frodo_sample2:
  sign:uint16{v sign <= 1} -> e:uint16 -> Lemma
  (((lognot sign +. u16 1) ^. e) +. sign == u16 ((Math.Lib.powx (-1) (v sign) * v e) % modulus U16))

let lemma_frodo_sample2 sign e =
  calc (==) {
    v ((lognot sign +. u16 1) ^. e);
    (==) { logxor_spec (lognot sign +. u16 1) e }
    logxor_v #U16 (v (lognot sign +. u16 1)) (v e);
    (==) { lognot_plus_one sign }
    logxor_v #U16 ((modulus U16 - v sign) % modulus U16) (v e);
    (==) { UInt.logxor_commutative #16 ((modulus U16 - v sign) % modulus U16) (v e) }
    logxor_v #U16 (v e) ((modulus U16 - v sign) % modulus U16);
    };

  if v sign = 0 then begin
    calc (==) {
      logxor_v #U16 (v e) ((modulus U16 - v sign) % modulus U16);
      (==) { Math.Lemmas.multiple_modulo_lemma 1 (modulus U16) }
      logxor_v #U16 (v e) 0;
      (==) { UInt.logxor_lemma_1 #16 (v e) }
      v e;
      };
    assert (v (((lognot sign +. u16 1) ^. e) +. sign) == v e);

    assert_norm (Math.Lib.powx (-1) 0 = 1);
    Math.Lemmas.small_mod (v e) (modulus U16) end
  else begin
    calc (==) {
      logxor_v #U16 (v e) ((modulus U16 - v sign) % modulus U16);
      (==) { Math.Lemmas.small_mod (modulus U16 - v sign) (modulus U16) }
      logxor_v #U16 (v e) (UInt.ones 16);
      (==) { UInt.logxor_lemma_2 #16 (v e) }
      lognot_v #U16 (v e);
      (==) { UInt.lemma_lognot_value_mod #16 (v e) }
      modulus U16 - v e - 1;
      };
    assert (v (((lognot sign +. u16 1) ^. e) +. sign) == (modulus U16 - v e) % modulus U16);

    assert_norm (Math.Lib.powx (-1) 1 = -1) end


val lemma_mul_acc_comm:
  a:size_nat -> b:size_nat -> c:size_nat -> Lemma (a * b * c = c * a * b)
let lemma_mul_acc_comm a b c = ()


val lemma_matrix_index_repeati1:
  n1:size_nat -> n2:size_nat -> i:size_nat{i < n1} -> j:size_nat{j < n2} -> Lemma
  (2 * (i * n2 + j) + 2 <= 2 * n1 * n2)

let lemma_matrix_index_repeati1 n1 n2 i j =
  assert (i * n2 + j <= (n1 - 1) * n2 + (n2 - 1));
  calc (<=) {
    2 * (i * n2 + j) + 2;
    <= { Math.Lemmas.lemma_mult_le_right n2 i (n1 - 1) }
    2 * ((n1 - 1) * n2 + (n2 - 1)) + 2;
    == { }
    2 * (n1 - 1) * n2 + 2 * n2 - 2 + 2;
    == { }
     2 * n1 * n2;
  }


val lemma_matrix_index_repeati2:
  n1:size_nat -> n2:size_nat -> i:size_nat{i < n1} -> j:size_nat{j < n2} ->
  Lemma (2 * (n1 * j + i) + 2 <= 2 * n1 * n2)

let lemma_matrix_index_repeati2 n1 n2 i j =
  lemma_matrix_index_repeati1 n2 n1 j i


val lemma_matrix_index_repeati:
    n1:size_nat
  -> n2:size_nat{n1 * n2 <= max_size_t /\ n2 % 8 = 0}
  -> d:size_nat{d * n1 <= max_size_t /\ d * n1 * n2 / 8 <= max_size_t}
  -> i:size_nat{i < n1}
  -> j:size_nat{j < n2 / 8} -> Lemma
   (i * (n2 / 8) <= max_size_t /\
    i * (n2 / 8) + j <= max_size_t /\
    (i * (n2 / 8) + j) * d <= max_size_t /\
    (i * (n2 / 8) + j) * d + d <= d * n1 * n2 / 8)

let lemma_matrix_index_repeati n1 n2 d i j =
  calc (<=) {
    i * (n2 / 8) + j;
    <= { }
    (n1 - 1) * (n2 / 8) + j;
    <= { }
    (n1 - 1) * (n2 / 8) + (n2 / 8 - 1);
  };
  Math.Lemmas.lemma_mult_le_right d (i * (n2 / 8) + j) (n1 * (n2 / 8) - 1)
