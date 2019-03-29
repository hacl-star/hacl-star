module Hacl.Spec.EC.Format.Lemmas

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul
open FStar.Seq
open FStar.Old.Endianness


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 40"

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


let u51 = x:nat{x < pow2 51}

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 160"

#set-options "--z3rlimit 40"
val lemma_fcontract_base_i: s:nat -> s':nat -> a:nat{a >= 64} -> b:nat{b <= 39} -> c:nat{c <= 38} -> Lemma
  (pow2 a * ((s / pow2 b) + ((s' * pow2 c) % pow2 64)) = 
   pow2 a * (s / pow2 b) + pow2 (a+c) * (s' % pow2 (64 - c)))
let lemma_fcontract_base_i s s' a b c =
  Math.Lemmas.distributivity_add_right (pow2 a) (s / pow2 b) ((s' * pow2 c) % pow2 64);
  cut (pow2 a * ((s / pow2 b) + ((s' * pow2 c) % pow2 64)) = 
            (pow2 a * (s / pow2 b)) + pow2 a * ( (s' * pow2 c) % pow2 64));
  Math.Lemmas.pow2_multiplication_modulo_lemma_2 s' 64 c;
  cut (pow2 a * ( (s' * pow2 c) % pow2 64) = pow2 a * ( (s' % pow2 (64 - c)) * pow2 c));
  Math.Lemmas.paren_mul_right (pow2 a) (s' % pow2 (64-c)) (pow2 c);
  Math.Lemmas.pow2_plus a c(* ; *)
(*   cut (pow2 a * ( (s' * pow2 c) % pow2 64) = pow2 (a+c) * ( (s' % pow2 (64 - c)))); *)
(*   Math.Lemmas.pow2_multiplication_modulo_lemma_2 (s') (64 + a) (a+c) *)

(* b - c = 64 - c *)
(* c = a + c *)
(* b = 64 + a *)

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val lemma_fcontract_base_j: x:nat -> a:nat -> b:nat -> Lemma
  (pow2 a * (x % pow2 b) + (pow2 (a+b) * (x / pow2 b)) = pow2 a * x)
let lemma_fcontract_base_j x a b =
  Math.Lemmas.pow2_plus a b;
  Math.Lemmas.distributivity_add_right (pow2 a) (x % pow2 b) (pow2 b * (x / pow2 b));
  Math.Lemmas.lemma_div_mod x (pow2 b)


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"

val lemma_fcontract_base: s0:u51 -> s1:u51 -> s2:u51 -> s3:u51 -> s4:u51 -> Lemma
  ((s0 + ((pow2 51 * s1) % pow2 64))
   + pow2 64 * ((s1 / pow2 13) + ((s2 * (pow2 38)) % pow2 64))
   + pow2 128 * ((s2 / pow2 26) + ((s3 * (pow2 25)) % pow2 64))
   + pow2 192 * ((s3 / pow2 39) + ((s4 * (pow2 12)) % pow2 64))
   = s0 + pow2 51 * s1 + pow2 102 * s2 + pow2 153 * s3 + pow2 204 * s4)
let lemma_fcontract_base s0 s1 s2 s3 s4 =
  lemma_fcontract_base_i s1 s2 64 13 38;
  lemma_fcontract_base_i s2 s3 128 26 25;
  lemma_fcontract_base_i s3 s4 192 39 12;
  Math.Lemmas.pow2_multiplication_modulo_lemma_2 s1 64 51;
  cut ((pow2 51 * s1) % pow2 64 = (s1 % pow2 13) * pow2 51);
  cut (pow2 64 * ((s1 / pow2 13) + ((s2 * (pow2 38)) % pow2 64)) =
    pow2 64 * (s1 / pow2 13) + pow2 102 * (s2 % pow2 26));
  cut (pow2 128 * ((s2 / pow2 26) + ((s3 * (pow2 25)) % pow2 64)) =
    pow2 128 * (s2 / pow2 26) + pow2 153 * (s3 % pow2 39));
  cut (pow2 192 * ((s3 / pow2 39) + ((s4 * (pow2 12)) % pow2 64)) =
    pow2 192 * (s3 / pow2 39) + pow2 204 * (s4 % pow2 52));
  assert_norm(pow2 51 < pow2 52);
  Math.Lemmas.modulo_lemma s4 (pow2 52);
  lemma_fcontract_base_j s1 51 13;
  lemma_fcontract_base_j s2 102 26;
  lemma_fcontract_base_j s3 153 39
  
val lemma_fcontract_bounds: s:u51 -> s':u51 -> a:nat -> b:nat{a + b = 51} -> Lemma
  ( s / pow2 a + ((s' * pow2 b) % pow2 64) < pow2 64)
let lemma_fcontract_bounds s s' a b =
  Math.Lemmas.pow2_multiplication_modulo_lemma_2 s' 64 b;
  cut ((s' * pow2 b) % pow2 64 = (s' % pow2 (64 - b)) * pow2 b);
  Math.Lemmas.pow2_plus a b;
  Math.Lemmas.lemma_div_lt s 51 a;
  cut (s / pow2 a < pow2 b);
  cut (s' % pow2 (64 - b) <= pow2 (64 - b) - 1);
  cut (s / pow2 a + ((s' * pow2 b) % pow2 64) < pow2 b + (pow2 (64 - b) - 1) * pow2 b);
  Math.Lemmas.distributivity_sub_left (pow2 (64 - b)) 1 (pow2 b);
  Math.Lemmas.pow2_plus (64 - b) b


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val lemma_fcontract: s0:u51 -> s1:u51 -> s2:u51 -> s3:u51 -> s4:u51 -> Lemma
  (((s0 + ((pow2 51 * s1) % pow2 64))) < pow2 64
   /\ ((s1 / pow2 13) + ((s2 * (pow2 38)) % pow2 64)) < pow2 64
   /\ ((s2 / pow2 26) + ((s3 * (pow2 25)) % pow2 64)) < pow2 64
   /\ ((s3 / pow2 39) + ((s4 * (pow2 12)) % pow2 64)) < pow2 64
   (* /\ (s0 + pow2 51 * s1 + pow2 102 * s2 + pow2 153 * s3 + pow2 204 * s4) < pow2 256 *)
   /\ little_endian (little_bytes 8ul ((s0 + ((pow2 51 * s1) % pow2 64))) @|
   little_bytes 8ul ((s1 / pow2 13) + ((s2 * (pow2 38)) % pow2 64)) @|
   little_bytes 8ul ((s2 / pow2 26) + ((s3 * (pow2 25)) % pow2 64)) @|
   little_bytes 8ul ((s3 / pow2 39) + ((s4 * (pow2 12)) % pow2 64)))
   = (s0 + pow2 51 * s1 + pow2 102 * s2 + pow2 153 * s3 + pow2 204 * s4))
let lemma_fcontract s0 s1 s2 s3 s4 =
  assert_norm (pow2 0 = 1);
  lemma_fcontract_bounds s0 s1 0 51;
  lemma_fcontract_bounds s1 s2 13 38;
  lemma_fcontract_bounds s2 s3 26 25;
  lemma_fcontract_bounds s3 s4 39 12;
  cut (((s0 + ((pow2 51 * s1) % pow2 64))) < pow2 64);
  cut (((s1 / pow2 13) + ((s2 * (pow2 38)) % pow2 64)) < pow2 64);
  cut (((s2 / pow2 26) + ((s3 * (pow2 25)) % pow2 64)) < pow2 64);
  cut (((s3 / pow2 39) + ((s4 * (pow2 12)) % pow2 64)) < pow2 64);
  let k0 = little_bytes 8ul ((s0 + ((pow2 51 * s1) % pow2 64))) in
  let k1 = little_bytes 8ul ((s1 / pow2 13) + ((s2 * (pow2 38)) % pow2 64)) in
  let k2 = little_bytes 8ul ((s2 / pow2 26) + ((s3 * (pow2 25)) % pow2 64)) in
  let k3 = little_bytes 8ul ((s3 / pow2 39) + ((s4 * (pow2 12)) % pow2 64)) in
  little_endian_append k2 k3;
  little_endian_append k1 (k2 @| k3);
  Math.Lemmas.distributivity_add_left (pow2 64) ((s2 / pow2 26) + ((s3 * (pow2 25)) % pow2 64)) (pow2 64 * ((s3 / pow2 39) + ((s4 * (pow2 12)) % pow2 64)));
  Math.Lemmas.pow2_plus 64 64;
  little_endian_append k0 (k1 @| (k2 @| k3));
  Math.Lemmas.distributivity_add_left (pow2 64) ((s1 / pow2 13) + ((s2 * (pow2 38)) % pow2 64)) 
    (pow2 64 * ((s2 / pow2 26) + ((s3 * (pow2 25)) % pow2 64)) + (pow2 128 * ((s3 / pow2 39) + ((s4 * (pow2 12)) % pow2 64))));
  Math.Lemmas.distributivity_add_left (pow2 64) (pow2 64 * ((s2 / pow2 26) + ((s3 * (pow2 25)) % pow2 64))) (pow2 128 * ((s3 / pow2 39) + ((s4 * (pow2 12)) % pow2 64)));
  Math.Lemmas.pow2_plus 64 128;
  lemma_fcontract_base s0 s1 s2 s3 s4
