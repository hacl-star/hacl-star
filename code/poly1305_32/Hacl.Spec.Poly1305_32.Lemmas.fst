module Hacl.Spec.Poly1305_32.Lemmas

open FStar.Mul
open FStar.Math.Lemmas

#reset-options "--z3rlimit 100 --max_fuel 0 --smtencoding.nl_arith_repr native --smtencoding.l_arith_repr native"

private val lemma_fcontract_base_i: s:nat -> s':nat -> a:nat{a >= 32} -> b:nat{b <= 18} -> c:nat{c <= 26} -> Lemma
  (pow2 a * ((s / pow2 b) + ((s' * pow2 c) % pow2 32)) = 
   pow2 a * (s / pow2 b) + pow2 (a+c) * (s' % pow2 (32 - c)))
private let lemma_fcontract_base_i s s' a b c =
  Math.Lemmas.distributivity_add_right (pow2 a) (s / pow2 b) ((s' * pow2 c) % pow2 32);
  assert (pow2 a * ((s / pow2 b) + ((s' * pow2 c) % pow2 32)) = 
            (pow2 a * (s / pow2 b)) + pow2 a * ( (s' * pow2 c) % pow2 32));
  Math.Lemmas.pow2_multiplication_modulo_lemma_2 s' 32 c;
  assert (pow2 a * ( (s' * pow2 c) % pow2 32) = pow2 a * ( (s' % pow2 (32 - c)) * pow2 c));
  Math.Lemmas.paren_mul_right (pow2 a) (s' % pow2 (32-c)) (pow2 c);
  Math.Lemmas.pow2_plus a c


private val lemma_fcontract_base_j: x:nat -> a:nat -> b:nat -> Lemma
  (pow2 a * (x % pow2 b) + (pow2 (a+b) * (x / pow2 b)) = pow2 a * x)
private let lemma_fcontract_base_j x a b =
  Math.Lemmas.pow2_plus a b;
  Math.Lemmas.distributivity_add_right (pow2 a) (x % pow2 b) (pow2 b * (x / pow2 b));
  Math.Lemmas.lemma_div_mod x (pow2 b)

let u26 = x:nat{x < pow2 26}

private val lemma_fcontract_base: s0:u26 -> s1:u26 -> s2:u26 -> s3:u26 -> s4:u26 -> Lemma
  ((s0 + ((pow2 26 * s1) % pow2 32))
   + pow2 32 * ((s1 / pow2  6) + ((s2 * (pow2 20)) % pow2 32))
   + pow2 64 * ((s2 / pow2 12) + ((s3 * (pow2 14)) % pow2 32))
   + pow2 96 * ((s3 / pow2 18) + ((s4 * (pow2  8)) % pow2 32))
   = s0 + pow2 26 * s1 + pow2 52 * s2 + pow2 78 * s3 + pow2 104 * (s4 % pow2 24))
private let lemma_fcontract_base s0 s1 s2 s3 s4 =
  lemma_fcontract_base_i s1 s2 32 6 20;
  lemma_fcontract_base_i s2 s3 64 12 14;
  lemma_fcontract_base_i s3 s4 96 18 8;
  Math.Lemmas.pow2_multiplication_modulo_lemma_2 s1 32 26;
  pow2_plus 20 32;
  assert ((pow2 26 * s1) % pow2 32 = (s1 % pow2 6) * pow2 26);
  assert (pow2 32 * ((s1 / pow2 6) + ((s2 * (pow2 20)) % pow2 32)) =
    pow2 32 * (s1 / pow2 6) + pow2 52 * (s2 % pow2 12));
  assert (pow2 64 * ((s2 / pow2 12) + ((s3 * (pow2 14)) % pow2 32)) =
    pow2 64 * (s2 / pow2 12) + pow2 78 * (s3 % pow2 18));
  assert (pow2 96 * ((s3 / pow2 18) + ((s4 * (pow2  8)) % pow2 32)) =
    pow2 96 * (s3 / pow2 18) + pow2 104 * (s4 % pow2 24));
  assert_norm(pow2 26 < pow2 52);
  Math.Lemmas.modulo_lemma s4 (pow2 52);
  lemma_fcontract_base_j s1 26 6;
  lemma_fcontract_base_j s2 52 12;
  lemma_fcontract_base_j s3 78 18

#reset-options "--z3rlimit 100 --max_fuel 0"

val lemma_bignum_to_128:
  h0:nat{h0 < pow2 26} -> h1:nat{h1 < pow2 26} -> h2:nat{h2 < pow2 26} ->
  h3:nat{h3 < pow2 26} -> h4:nat{h4 < pow2 26} ->
  Lemma (((h4 * pow2 8) % pow2 32 + h3 / pow2 18) * pow2 96
          + ((h3 * pow2 14) % pow2 32 + h2 / pow2 12) * pow2 64
          + ((h2 * pow2 20) % pow2 32 + h1 / pow2 6) * pow2 32
          + ((h1 * pow2 26) % pow2 32) + h0
    = (h0 + pow2 26 * h1 + pow2 52 * h2 + pow2 78 * h3 + pow2 104 * h4) % pow2 128)
let lemma_bignum_to_128 h0 h1 h2 h3 h4 =
  assert_norm(pow2 26 = 0x4000000);
  assert_norm(pow2 52 = 0x10000000000000);
  assert_norm(pow2 78 = 0x40000000000000000000);
  assert_norm(pow2 104 = 0x100000000000000000000000000);
  lemma_fcontract_base h0 h1 h2 h3 h4;
  swap_mul ((h2 * pow2 20) % pow2 32 + h1 / pow2 6) (pow2 32);
  swap_mul ((h4 * pow2 8) % pow2 32 + h3 / pow2 18) (pow2 96);
  swap_mul ((h3 * pow2 14) % pow2 32 + h2 / pow2 12) (pow2 64);
  assert(((h4 * pow2 8) % pow2 32 + h3 / pow2 18) * pow2 96
          + ((h3 * pow2 14) % pow2 32 + h2 / pow2 12) * pow2 64
          + ((h2 * pow2 20) % pow2 32 + h1 / pow2 6) * pow2 32
          + ((h1 * pow2 26) % pow2 32) + h0 = h0 + pow2 26 * h1 + pow2 52 * h2 + pow2 78 * h3 + pow2 104 * (h4 % pow2 24));
  lemma_mod_plus_distr_l (pow2 104 * h4) (h0 + pow2 26 * h1 + pow2 52 * h2 + pow2 78 * h3) (pow2 128);
  pow2_multiplication_modulo_lemma_2 h4 128 104;
  swap_mul (pow2 104) (h4 % pow2 24);
  assert((pow2 104 * h4) % pow2 128 = pow2 104 * (h4 % pow2 24));
  assert_norm(pow2 26 - 1 + pow2 26 * (pow2 26 - 1) + pow2 52 * (pow2 26 - 1) + pow2 78 * (pow2 26 - 1) < pow2 104);
  assert( h0 + pow2 26 * h1 + pow2 52 * h2 + pow2 78 * h3 < pow2 104);
  assert((h0 + pow2 26 * h1 + pow2 52 * h2 + pow2 78 * h3 + pow2 104 * h4) % pow2 128 = 
    (((pow2 104 * h4) % pow2 128) + h0 + pow2 26 * h1 + pow2 52 * h2 + pow2 78 * h3) % pow2 128);
  assert(h4 % pow2 24 < pow2 24);
  assert_norm(pow2 104 * (pow2 24 - 1) = pow2 128 - pow2 104);
  assert(((pow2 104 * h4) % pow2 128) + h0 + pow2 26 * h1 + pow2 52 * h2 + pow2 78 * h3 < pow2 128);
  small_modulo_lemma_1 (h0 + pow2 26 * h1 + pow2 52 * h2 + pow2 78 * h3 + pow2 104 * (h4 % pow2 24)) (pow2 128)


private val lemma_fexpand_i: x:nat -> d:pos -> d':pos{d' <= 6} ->
  Lemma ((((x / pow2 d) % pow2 32) / pow2 d') % pow2 26 = (x / pow2 (d+d')) % pow2 26)
private let lemma_fexpand_i x d d' =
  Math.Lemmas.pow2_modulo_division_lemma_1 (x / pow2 d) d' 32;
  Math.Lemmas.division_multiplication_lemma (x) (pow2 d) (pow2 d');
  Math.Lemmas.pow2_plus d d';
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (x / pow2 (d+d')) 26 (32-d')

private val lemma_fexpand_i': x:nat -> d:pos -> d':pos{d' = 8} ->
  Lemma ((((x / pow2 d) % pow2 32) / pow2 d')  = (x / pow2 (d+d')) % pow2 24)
private let lemma_fexpand_i' x d d' =
  Math.Lemmas.pow2_modulo_division_lemma_1 (x / pow2 d) d' 32;
  assert( ((x / pow2 d) % pow2 32) / pow2 d' = (x / pow2 d / pow2 d') % pow2 (32 - d'));
  Math.Lemmas.division_multiplication_lemma (x) (pow2 d) (pow2 d');
  Math.Lemmas.pow2_plus d d';
  Math.Lemmas.pow2_modulo_modulo_lemma_2 (x / pow2 (d+d')) 26 (32-d')

val lemma_k: k:nat{k < pow2 128} -> Lemma
  (k  = k % pow2 26 + pow2 26 * ((k / pow2 26) % pow2 26) + pow2 52 * ((k / pow2 52) % pow2 26) + pow2 78 * ((k / pow2 78) % pow2 26) + pow2 104 * ((k / pow2 104)))
let lemma_k k =
  Math.Lemmas.lemma_div_mod (k % pow2 128) (pow2 104);
  Math.Lemmas.pow2_modulo_modulo_lemma_1 k 104 128;
  Math.Lemmas.pow2_modulo_division_lemma_1 k 104 128;
  lemma_div_lt k 128 104;
  small_modulo_lemma_1 (k / pow2 104) (pow2 24);
  small_modulo_lemma_1 (k) (pow2 128);
  cut (k % pow2 128 = pow2 104 * ((k / pow2 104)) + (k % pow2 104));
  Math.Lemmas.lemma_div_mod (k % pow2 104) (pow2 78);
  Math.Lemmas.pow2_modulo_modulo_lemma_1 k 78 104;
  Math.Lemmas.pow2_modulo_division_lemma_1 k 78 104;
  cut (k % pow2 104 = pow2 78 * ((k / pow2 78) % pow2 26) + (k % pow2 78));
  Math.Lemmas.lemma_div_mod (k % pow2 78) (pow2 52);
  Math.Lemmas.pow2_modulo_modulo_lemma_1 k 52 78;
  Math.Lemmas.pow2_modulo_division_lemma_1 k 52 78;
  cut (k % pow2 78 = pow2 52 * ((k / pow2 52) % pow2 26) + (k % pow2 52));
  Math.Lemmas.lemma_div_mod (k % pow2 52) (pow2 26);
  Math.Lemmas.pow2_modulo_modulo_lemma_1 k 26 52;
  Math.Lemmas.pow2_modulo_division_lemma_1 k 26 52;
  cut (k % pow2 52 = pow2 26 * ((k / pow2 26) % pow2 26) + (k % pow2 26))


private val lemma_k': k:nat -> Lemma
  (k % pow2 128  = k % pow2 26 + pow2 26 * ((k / pow2 26) % pow2 26) + pow2 52 * ((k / pow2 52) % pow2 26) + pow2 78 * ((k / pow2 78) % pow2 26) + pow2 104 * ((k / pow2 104) % pow2 24))
private let lemma_k' k =
  Math.Lemmas.lemma_div_mod (k % pow2 128) (pow2 104);
  Math.Lemmas.pow2_modulo_modulo_lemma_1 k 104 128;
  Math.Lemmas.pow2_modulo_division_lemma_1 k 104 128;
  assert (k % pow2 128 = pow2 104 * ((k / pow2 104) % pow2 24) + (k % pow2 104));
  Math.Lemmas.lemma_div_mod (k % pow2 104) (pow2 78);
  Math.Lemmas.pow2_modulo_modulo_lemma_1 k 78 104;
  Math.Lemmas.pow2_modulo_division_lemma_1 k 78 104;
  cut (k % pow2 104 = pow2 78 * ((k / pow2 78) % pow2 26) + (k % pow2 78));
  Math.Lemmas.lemma_div_mod (k % pow2 78) (pow2 52);
  Math.Lemmas.pow2_modulo_modulo_lemma_1 k 52 78;
  Math.Lemmas.pow2_modulo_division_lemma_1 k 52 78;
  cut (k % pow2 78 = pow2 52 * ((k / pow2 52) % pow2 26) + (k % pow2 52));
  Math.Lemmas.lemma_div_mod (k % pow2 52) (pow2 26);
  Math.Lemmas.pow2_modulo_modulo_lemma_1 k 26 52;
  Math.Lemmas.pow2_modulo_division_lemma_1 k 26 52;
  cut (k % pow2 52 = pow2 26 * ((k / pow2 26) % pow2 26) + (k % pow2 26))


open FStar.Endianness
open FStar.Seq

private val lemma_little_endian_split: n:nat -> k:lbytes n -> i:nat{i <= n} ->
  Lemma (little_endian (slice k 0 i) = little_endian k % pow2 (8*i)
         /\ little_endian (slice k i n) = little_endian k / pow2 (8*i))
private let lemma_little_endian_split n k i =
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


private val lemma_little_endian_of_partial_load: k:lbytes 16 -> i:nat -> j:nat{i <= j /\ j <= 16} ->
  Lemma (requires (True))
        (ensures (little_endian (slice k i j) = (little_endian k / pow2 (8*i)) % pow2 (8*(j - i))))
private let lemma_little_endian_of_partial_load k i j =
  lemma_little_endian_split 16 k i;
  lemma_little_endian_split (16-i) (slice k i 16) (j - i);
  lemma_eq_intro (slice (slice k i 16) 0 (j-i)) (slice k i j)


val lemma_fexpand: k:lbytes 16 -> Lemma
  (let i0 = little_endian (slice k 0 4) % pow2 26 in
   let i1 = (little_endian (slice k 3 7) / pow2 2) % pow2 26 in
   let i2 = (little_endian (slice k 6 10) / pow2 4) % pow2 26 in
   let i3 = (little_endian (slice k 9 13) / pow2 6) % pow2 26 in
   let i4 = (little_endian (slice k 12 16) / pow2 8) in
   i0 + pow2 26 * i1 + pow2 52 * i2 + pow2 78 * i3 + pow2 104 * i4 = little_endian k /\ i4 < pow2 24)
let lemma_fexpand k =
  lemma_little_endian_of_partial_load k 0 4;
  lemma_little_endian_of_partial_load k 3 7;
  lemma_little_endian_of_partial_load k 6 10;
  lemma_little_endian_of_partial_load k 9 13;
  lemma_little_endian_of_partial_load k 12 16;
  assert_norm(pow2 0 = 1);
  let i0 = little_endian (slice k 0 4) % pow2 26 in
  cut (i0 = (little_endian k % pow2 32) % pow2 26);
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (little_endian k) 26 32;
  cut (i0 = little_endian k % pow2 26);
  let i1 = (little_endian (slice k 3 7) / pow2 2) % pow2 26 in
  let i2 = (little_endian (slice k 6 10) / pow2 4) % pow2 26 in
  let i3 = (little_endian (slice k 9 13) / pow2 6) % pow2 26 in
  let i4 = (little_endian (slice k 12 16) / pow2 8) in
  assert_norm(pow2 32 / pow2 24 = pow2 8);
  lemma_div_lt (little_endian (slice k 12 16)) 32 8;
  small_modulo_lemma_1 (little_endian (slice k 12 16) / pow2 8) (pow2 24);
  assert(i4 = (little_endian (slice k 12 16) / pow2 8) % pow2 24);
  lemma_fexpand_i (little_endian k) 24 2;
  lemma_fexpand_i (little_endian k) 48 4;
  lemma_fexpand_i (little_endian k) 72 6;
  lemma_fexpand_i' (little_endian k) 96 8;
  assert (i1 = (little_endian k / pow2 26) % pow2 26);
  assert (i2 = (little_endian k / pow2 52) % pow2 26);
  assert (i3 = (little_endian k / pow2 78) % pow2 26);
  assert (i4 = (little_endian k / pow2 104) % pow2 24);
  assert_norm(pow2 128 / pow2 104 = pow2 24);
  lemma_div_lt (little_endian k) 128 104;
  small_modulo_lemma_1 (little_endian k / pow2 104) (pow2 24);
  lemma_k' (little_endian k);
  let lk = little_endian k in
  assert( lk % pow2 128 = i0 + pow2 26 * i1 + pow2 52 * i2 + pow2 78 * i3 + pow2 104 * i4);
  small_modulo_lemma_1 (little_endian k) (pow2 128);
  assert( lk = i0 + pow2 26 * i1 + pow2 52 * i2 + pow2 78 * i3 + pow2 104 * i4);
  assert( i4 < pow2 24)


val lemma_seval_mod_128:
  h0:nat{h0 < pow2 26} -> h1:nat{h1 < pow2 26} -> h2:nat{h2 < pow2 26} ->  h3:nat{h3 < pow2 26} -> h4:nat{h4 < pow2 26} ->
  Lemma ((h0 + pow2 26 * h1 + pow2 52 * h2 + pow2 78 * h3 + pow2 104 * h4) % pow2 128
         = h0 + pow2 26 * h1 + pow2 52 * h2 + pow2 78 * h3 + pow2 104 * (h4 % pow2 24))
let lemma_seval_mod_128 h0 h1 h2 h3 h4 =
  assert_norm(pow2 24 = 0x1000000);
  assert_norm(pow2 26 = 0x4000000);
  assert_norm(pow2 52 = 0x10000000000000);
  assert_norm(pow2 78 = 0x40000000000000000000);
  assert_norm(pow2 104 = 0x100000000000000000000000000);
  lemma_mod_plus_distr_l (pow2 104 * h4) (h0 + pow2 26 * h1 + pow2 52 * h2 + pow2 78 * h3) (pow2 128);
  Math.Lemmas.pow2_multiplication_modulo_lemma_2 h4 128 104;
  small_modulo_lemma_1 (h0 + pow2 26 * h1 + pow2 52 * h2 + pow2 78 * h3 + pow2 104 * (h4 % pow2 24)) (pow2 128)
