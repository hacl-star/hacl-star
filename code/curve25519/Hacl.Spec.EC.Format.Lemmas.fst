module Hacl.Spec.EC.Format.Lemmas

open FStar.Mul
open FStar.Seq
open FStar.Endianness


#reset-options "--initial_fuel 0 --max_fuel 0"

val lemma_little_endian_split: n:nat -> k:lbytes n -> i:nat{i <= n} ->
  Lemma (little_endian (slice k 0 i) = little_endian k % pow2 (8*i)
         /\ little_endian (slice k i n) = little_endian k / pow2 (8*i))
let lemma_little_endian_split n k i =
  let k0 = slice k 0 i in
  let k1 = slice k i n in
  lemma_eq_intro (k0 @| k1) k;
  little_endian_append k0 k1;
  cut (little_endian k = little_endian k0 + pow2 (8 * i) * little_endian k1);
  lemma_little_endian_is_bounded k0;
  Math.Lemmas.lemma_div_mod (little_endian k) (pow2 (8*i));
  Math.Lemmas.modulo_lemma (little_endian k0) (pow2 (8*i));
  Math.Lemmas.lemma_mod_mul_distr_l (little_endian k0) (pow2 (8 * i) * little_endian k1) (pow2 (8*i));
  Math.Lemmas.lemma_mod_plus (little_endian k0) (little_endian k1) (pow2 (8*i));
  cut (little_endian k / pow2 (8*i) = little_endian k1)


val lemma_little_endian_of_partial_load: k:lbytes 32 -> i:nat -> j:nat{i <= j /\ j <= 32} ->
  Lemma (requires (True))
        (ensures (little_endian (slice k i j) = (little_endian k / pow2 (8*i)) % pow2 (8*(j - i))))
let lemma_little_endian_of_partial_load k i j =
  lemma_little_endian_split 32 k i;
  lemma_little_endian_split (32-i) (slice k i 32) (j - i);
  lemma_eq_intro (slice (slice k i 32) 0 (j-i)) (slice k i j)

val lemma_fexpand_i: x:nat -> d:pos -> d':pos{d' <= 12} ->
  Lemma ((((x / pow2 d) % pow2 64) / pow2 d') % pow2 51 = (x / pow2 (d+d')) % pow2 51)
let lemma_fexpand_i x d d' =
  Math.Lemmas.pow2_modulo_division_lemma_1 (x / pow2 d) d' 64;
  Math.Lemmas.division_multiplication_lemma (x) (pow2 d) (pow2 d');
  Math.Lemmas.pow2_plus d d';
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (x / pow2 (d+d')) 51 (64-d')

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val lemma_k: k:nat -> Lemma
  (k % pow2 255 = k % pow2 51 + pow2 51 * ((k / pow2 51) % pow2 51) + pow2 102 * ((k / pow2 102) % pow2 51) + pow2 153 * ((k / pow2 153) % pow2 51) + pow2 204 * ((k / pow2 204) % pow2 51))
let lemma_k k =
  Math.Lemmas.lemma_div_mod (k % pow2 255) (pow2 204);
  Math.Lemmas.pow2_modulo_modulo_lemma_1 k 204 255;
  Math.Lemmas.pow2_modulo_division_lemma_1 k 204 255;
  cut (k % pow2 255 = pow2 204 * ((k / pow2 204) % pow2 51) + (k % pow2 204));
  Math.Lemmas.lemma_div_mod (k % pow2 204) (pow2 153);
  Math.Lemmas.pow2_modulo_modulo_lemma_1 k 153 204;
  Math.Lemmas.pow2_modulo_division_lemma_1 k 153 204;
  cut (k % pow2 204 = pow2 153 * ((k / pow2 153) % pow2 51) + (k % pow2 153));
  Math.Lemmas.lemma_div_mod (k % pow2 153) (pow2 102);
  Math.Lemmas.pow2_modulo_modulo_lemma_1 k 102 153;
  Math.Lemmas.pow2_modulo_division_lemma_1 k 102 153;
  cut (k % pow2 153 = pow2 102 * ((k / pow2 102) % pow2 51) + (k % pow2 102));
  Math.Lemmas.lemma_div_mod (k % pow2 102) (pow2 51);
  Math.Lemmas.pow2_modulo_modulo_lemma_1 k 51 102;
  Math.Lemmas.pow2_modulo_division_lemma_1 k 51 102;
  cut (k % pow2 102 = pow2 51 * ((k / pow2 51) % pow2 51) + (k % pow2 51))


val lemma_fexpand: k:lbytes 32 -> Lemma
  (let i0 = little_endian (slice k 0 8) % pow2 51 in
   let i1 = (little_endian (slice k 6 14) / pow2 3) % pow2 51 in
   let i2 = (little_endian (slice k 12 20) / pow2 6) % pow2 51 in
   let i3 = (little_endian (slice k 19 27) / pow2 1) % pow2 51 in
   let i4 = (little_endian (slice k 24 32) / pow2 12) % pow2 51 in
   i0 + pow2 51 * i1 + pow2 102 * i2 + pow2 153 * i3 + pow2 204 * i4 = little_endian k % pow2 255)
let lemma_fexpand k =
  lemma_little_endian_of_partial_load k 0 8;
  lemma_little_endian_of_partial_load k 6 14;
  lemma_little_endian_of_partial_load k 12 20;
  lemma_little_endian_of_partial_load k 19 27;
  lemma_little_endian_of_partial_load k 24 32;
  assert_norm(pow2 0 = 1);
  let i0 = little_endian (slice k 0 8) % pow2 51 in
  cut (i0 = (little_endian k % pow2 64) % pow2 51);
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (little_endian k) 51 64;
  cut (i0 = little_endian k % pow2 51);
  let i1 = (little_endian (slice k 6 14) / pow2 3) % pow2 51 in
  let i2 = (little_endian (slice k 12 20) / pow2 6) % pow2 51 in
  let i3 = (little_endian (slice k 19 27) / pow2 1) % pow2 51 in
  let i4 = (little_endian (slice k 24 32) / pow2 12) % pow2 51 in
  lemma_fexpand_i (little_endian k) 48 3;
  lemma_fexpand_i (little_endian k) 96 6;
  lemma_fexpand_i (little_endian k) 152 1;
  lemma_fexpand_i (little_endian k) 192 12;
  cut (i1 = (little_endian k / pow2 51) % pow2 51);
  cut (i2 = (little_endian k / pow2 102) % pow2 51);
  cut (i3 = (little_endian k / pow2 153) % pow2 51);
  cut (i4 = (little_endian k / pow2 204) % pow2 51);
  lemma_k (little_endian k)
