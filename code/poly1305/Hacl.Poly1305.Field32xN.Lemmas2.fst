module Hacl.Poly1305.Field32xN.Lemmas2

open Lib.IntTypes
open Lib.IntVector
open Lib.Sequence
open FStar.Mul

open Hacl.Spec.Poly1305.Vec
include Hacl.Spec.Poly1305.Field32xN

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val lemma_mult_le: a:nat -> b:nat -> c:nat -> d:nat -> Lemma
  (requires a <= b /\ c <= d)
  (ensures  a * c <= b * d)
let lemma_mult_le a b c d = ()

let load_tup64_lemma0_lo lo =
  calc (==) {
    v lo % pow2 26 + ((v lo / pow2 26) % pow2 26) * pow26 + v lo / pow2 52 * pow52;
  == { FStar.Math.Lemmas.pow2_modulo_modulo_lemma_1 (v lo) 26 52 }
    (v lo % pow2 52) % pow2 26 + ((v lo / pow2 26) % pow2 26) * pow2 26 + v lo / pow2 52 * pow2 52;
  == { FStar.Math.Lemmas.pow2_modulo_division_lemma_1 (v lo) 26 52 }
    (v lo % pow2 52) % pow2 26 + ((v lo % pow2 52) / pow2 26) * pow2 26 + v lo / pow2 52 * pow2 52;
  == { FStar.Math.Lemmas.euclidean_division_definition (v lo % pow2 52) (pow2 26) }
    (v lo % pow2 52) + v lo / pow2 52 * pow2 52;
  == { FStar.Math.Lemmas.euclidean_division_definition (v lo) (pow2 52) }
    v lo;
  }

let load_tup64_lemma0_hi hi =
  calc (==) {
    (v hi % pow2 14) * pow2 64 + (v hi / pow2 14) % pow2 26 * pow78 + v hi / pow2 40 * pow104;
    == {
      assert_norm (pow78 = pow2 14 * pow2 64);
      assert_norm (pow104 = pow2 40 * pow2 64)}
    (v hi % pow2 14) * pow2 64 + (v hi / pow2 14) % pow2 26 * pow2 14 * pow2 64 + v hi / pow2 40 * pow2 40 * pow2 64;
    == { }
    (v hi % pow2 14 + ((v hi / pow2 14) % pow2 26) * pow2 14 + (v hi / pow2 40) * pow2 40) * pow2 64;
  == { FStar.Math.Lemmas.pow2_modulo_division_lemma_1 (v hi) 14 40 }
    (v hi % pow2 14 + ((v hi % pow2 40) / pow2 14) * pow2 14 + (v hi / pow2 40) * pow2 40) * pow2 64;
  == { FStar.Math.Lemmas.pow2_modulo_modulo_lemma_1 (v hi) 14 40 }
    ((v hi % pow2 40) % pow2 14 + ((v hi % pow2 40) / pow2 14) * pow2 14 + (v hi / pow2 40) * pow2 40) * pow2 64;
  == { FStar.Math.Lemmas.euclidean_division_definition (v hi % pow2 40) (pow2 14) }
    (v hi % pow2 40 + (v hi / pow2 40) * pow2 40) * pow2 64;
  == { FStar.Math.Lemmas.euclidean_division_definition (v hi) (pow2 40) }
    v hi * pow2 64;
  }

#push-options"--z3rlimit 100"
let load_tup64_lemma0 f lo hi =
  let (f0, f1, f2, f3, f4) = f in
  calc (==) {
    as_nat5 f;
    == { }
    v f0 + v f1 * pow26 + v f2 * pow52 + v f3 * pow78 + v f4 * pow104;
    == { }
    v lo % pow2 26 + (v lo / pow2 26) % pow2 26 * pow26 +
    v lo / pow2 52 * pow52 + (v hi % pow2 14) * pow2 12 * pow52 +
    (v hi / pow2 14) % pow2 26 * pow78 + v hi / pow2 40 * pow104;
    == { load_tup64_lemma0_lo lo }
    v lo + (v hi % pow2 14) * pow2 12 * pow52 + (v hi / pow2 14) % pow2 26 * pow78 + v hi / pow2 40 * pow104;
    == { assert_norm (pow2 12 * pow52 = pow2 64) }
    v lo + (v hi % pow2 14) * pow2 64 + (v hi / pow2 14) % pow2 26 * pow78 + v hi / pow2 40 * pow104;
    == { load_tup64_lemma0_hi hi }
    v lo + v hi * pow2 64;
  };
  assert (as_nat5 f == v hi * pow2 64 + v lo)
#pop-options

let load_tup64_fits_lemma f lo hi =
  let (f0, f1, f2, f3, f4) = f in
  assert_norm (pow26 = pow2 26);
  FStar.Math.Lemmas.lemma_div_lt_nat (v lo) 64 52;
  lemma_mult_le (v hi % pow2 14) (pow2 14 - 1) (pow2 12) (pow2 12);
  assert_norm (pow2 14 * pow2 12 = pow2 26);
  FStar.Math.Lemmas.lemma_div_lt_nat (v hi) 64 40;
  assert_norm (pow2 24 < pow2 26)

let load_tup64_lemma_f2 lo hi =
  let f2 = (lo >>. 52ul) |. ((hi &. u64 0x3fff) <<. 12ul) in
  let tmp = (hi &. u64 0x3fff) in

  calc (==) {
    v (tmp <<. 12ul) % pow2 12;
  == { shift_left_lemma (hi &. u64 0x3fff) 12ul }
    (v tmp * pow2 12 % pow2 64) % pow2 12;
  == { assert_norm (pow2 64 = pow2 12 * pow2 52) }
    (v tmp * pow2 12 % (pow2 12 * pow2 52)) % pow2 12;
  == {FStar.Math.Lemmas.modulo_modulo_lemma (v tmp * pow2 12) (pow2 12) (pow2 52)}
    v tmp * pow2 12 % pow2 12;
  == {FStar.Math.Lemmas.multiple_modulo_lemma (v tmp) (pow2 12)}
    0;
  };
  assert (v (tmp <<. 12ul) % pow2 12 = 0);
  FStar.Math.Lemmas.lemma_div_lt (v lo) 64 52;
  assert (v (lo >>. 52ul) < pow2 12);
  logor_disjoint (lo >>. 52ul) ((hi &. u64 0x3fff) <<. 12ul) 12;

  calc (==) {
    v f2;
  == {  }
    v (lo >>. 52ul) + v ((hi &. u64 0x3fff) <<. 12ul);
  == { shift_right_lemma lo 52ul }
    v lo / pow2 52 + v ((hi &. u64 0x3fff) <<. 12ul);
  == { shift_left_lemma (hi &. u64 0x3fff) 12ul }
    v lo / pow2 52 + v (hi &. u64 0x3fff) * pow2 12 % pow2 64;
  };
  assert (v f2 == v lo / pow2 52 + v (hi &. u64 0x3fff) * pow2 12 % pow2 64);
  assert_norm (0x3fff = pow2 14 - 1);
  mod_mask_lemma hi 14ul;
  assert (v (mod_mask #U64 #SEC 14ul) == v (u64 0x3fff));
  assert (v f2 == v lo / pow2 52 + (v hi % pow2 14) * pow2 12 % pow2 64);

  assert (v hi % pow2 14 < pow2 14);
  assert_norm (pow2 14 * pow2 12 < pow2 64);
  FStar.Math.Lemmas.small_modulo_lemma_1 ((v hi % pow2 14) * pow2 12) (pow2 64);
  assert (v f2 == v lo / pow2 52 + (v hi % pow2 14) * pow2 12)

noextract
let load_tup64_lemma (lo hi : uint64) :
  Pure tup64_5
  (requires True)
  (ensures  fun f ->
    tup64_fits5 f (1, 1, 1, 1, 1) /\
    as_nat5 f < pow2 128 /\
    as_nat5 f % prime == v hi * pow2 64 + v lo)
=
  let mask26 = u64 0x3ffffff in
  assert_norm (0x3ffffff = pow2 26 - 1);
  assert_norm (0x3fff = pow2 14 - 1);

  let f0 = lo &. mask26 in
  mod_mask_lemma lo 26ul;
  assert (v (mod_mask #U64 #SEC 26ul) == v mask26);
  assert (v f0 == v lo % pow2 26);

  let f1 = (lo >>. 26ul) &. mask26 in
  assert (v f1 == (v lo / pow2 26) % pow2 26);

  let f2 = (lo >>. 52ul) |. ((hi &. u64 0x3fff) <<. 12ul) in
  load_tup64_lemma_f2 lo hi;
  assert (v f2 == v lo / pow2 52 + (v hi % pow2 14) * pow2 12);

  let f3 = (hi >>. 14ul) &. mask26 in
  assert (v f3 == (v hi / pow2 14) % pow2 26);

  let f4 = hi >>. 40ul in
  assert (v f4 == v hi / pow2 40);

  let f = (f0, f1, f2, f3, f4) in
  load_tup64_lemma0 f lo hi;
  load_tup64_fits_lemma f lo hi;
  assert (as_nat5 f < pow2 128);
  assert_norm (pow2 128 < prime);
  FStar.Math.Lemmas.small_modulo_lemma_1 (as_nat5 f) prime;
  assert (as_nat5 f % prime == v hi * pow2 64 + v lo);
  f


let load_felem5_lemma_i #w lo hi i =
  assert (as_tup64_i (load_felem5 #w lo hi) i == load_tup64_lemma (vec_v lo).[i] (vec_v hi).[i])

let load_tup64_4_compact_lemma_f2_mod lo hi =
  calc (<) {
    v lo / pow2 52 + (v hi % pow2 14) * pow2 12;
    < { Math.Lemmas.lemma_div_lt (v lo) 64 52 }
    pow2 12 + (v hi % pow2 14) * pow2 12;
    <= { Math.Lemmas.lemma_mult_le_right (pow2 12) (v hi % pow2 14) (pow2 14 - 1) }
    pow2 12 + (pow2 14 - 1) * pow2 12;
    == { Math.Lemmas.distributivity_sub_left (pow2 14) 1 (pow2 12); Math.Lemmas.pow2_plus 14 12 }
    pow2 26;
  };
  assert (v lo / pow2 52 + (v hi % pow2 14) * pow2 12 < pow2 26);
  Math.Lemmas.small_modulo_lemma_1 (v lo / pow2 52 + (v hi % pow2 14) * pow2 12) (pow2 26)

#push-options "--z3rlimit 100"
let load_tup64_4_compact_lemma_f2 lo hi =
  let t3 = (lo >>. 48ul) |. (hi <<. 16ul) in
  let f2 = (t3 >>. 4ul) &. u64 0x3ffffff in

  Math.Lemmas.lemma_div_lt (v lo) 64 48;
  logor_disjoint (lo >>. 48ul) (hi <<. 16ul) 16;
  assert (v t3 == v lo / pow2 48 + (v hi * pow2 16) % pow2 64);

  calc (==) {
    (v lo / pow2 48 + (v hi * pow2 16) % pow2 64) / pow2 4;
    == { Math.Lemmas.pow2_multiplication_modulo_lemma_2 (v hi) 64 16 }
    (v lo / pow2 48 + (v hi % pow2 48) * pow2 16) / pow2 4;
    == { Math.Lemmas.pow2_plus 12 4 }
    (v lo / pow2 48 + (v hi % pow2 48) * pow2 12 * pow2 4) / pow2 4;
    == { Math.Lemmas.division_addition_lemma (v lo / pow2 48) (pow2 4) ((v hi % pow2 48) * pow2 12) }
    (v lo / pow2 48) / pow2 4 + (v hi % pow2 48) * pow2 12;
    == { Math.Lemmas.division_multiplication_lemma (v lo) (pow2 48) (pow2 4); Math.Lemmas.pow2_plus 48 4 }
    v lo / pow2 52 + (v hi % pow2 48) * pow2 12;
    == { Math.Lemmas.pow2_multiplication_modulo_lemma_2 (v hi) 60 12 }
    v lo / pow2 52 + (v hi * pow2 12) % pow2 60;
  };
  assert (v (t3 >>. 4ul) == v lo / pow2 52 + (v hi * pow2 12) % pow2 60);
  assert_norm (0x3ffffff = pow2 26 - 1);
  mod_mask_lemma (t3 >>. 4ul) 26ul;
  assert (v (mod_mask #U64 #SEC 26ul) == v (u64 0x3ffffff));
  assert (v f2 == v (t3 >>. 4ul) % pow2 26);

  calc (==) {
    (v lo / pow2 52 + (v hi * pow2 12) % pow2 60) % pow2 26;
    == { Math.Lemmas.lemma_mod_plus_distr_r (v lo / pow2 52) ((v hi * pow2 12) % pow2 60) (pow2 26) }
    (v lo / pow2 52 + (v hi * pow2 12) % pow2 60 % pow2 26) % pow2 26;
    == { Math.Lemmas.pow2_modulo_modulo_lemma_1 (v hi * pow2 12) 26 60 }
    (v lo / pow2 52 + (v hi * pow2 12) % pow2 26) % pow2 26;
    == { Math.Lemmas.pow2_multiplication_modulo_lemma_2 (v hi) 26 12 }
    (v lo / pow2 52 + (v hi % pow2 14) * pow2 12) % pow2 26;
    == { load_tup64_4_compact_lemma_f2_mod lo hi }
    v lo / pow2 52 + (v hi % pow2 14) * pow2 12;
  };
  assert (v f2 == v lo / pow2 52 + (v hi % pow2 14) * pow2 12)
#pop-options

#push-options "--z3rlimit 200"
let load_tup64_4_compact_lemma_f3 lo hi =
  let t3 = (lo >>. 48ul) |. (hi <<. 16ul) in
  let f3 = (t3 >>. 30ul) &. u64 0x3ffffff in

  Math.Lemmas.lemma_div_lt (v lo) 64 48;
  logor_disjoint (lo >>. 48ul) (hi <<. 16ul) 16;
  assert (v t3 == v lo / pow2 48 + (v hi * pow2 16) % pow2 64);

  calc (==) {
    (v lo / pow2 48 + (v hi * pow2 16) % pow2 64) / pow2 30;
    == { Math.Lemmas.pow2_multiplication_modulo_lemma_2 (v hi) 64 16 }
    (v lo / pow2 48 + (v hi % pow2 48) * pow2 16) / pow2 30;
    == { Math.Lemmas.pow2_plus 16 14;
      Math.Lemmas.division_multiplication_lemma (v lo / pow2 48 + (v hi % pow2 48) * pow2 16) (pow2 16) (pow2 14) }
    ((v lo / pow2 48 + (v hi % pow2 48) * pow2 16) / pow2 16) / pow2 14;
    == { Math.Lemmas.division_addition_lemma (v lo / pow2 48) (pow2 16) (v hi % pow2 48) }
    ((v lo / pow2 48) / pow2 16 + (v hi % pow2 48)) / pow2 14;
    == { Math.Lemmas.division_multiplication_lemma (v lo) (pow2 48) (pow2 16); Math.Lemmas.pow2_plus 48 16 }
    (v lo / pow2 64 + (v hi % pow2 48)) / pow2 14;
    == { Math.Lemmas.small_div (v lo) (pow2 64) }
    (v hi % pow2 48) / pow2 14;
    == { Math.Lemmas.pow2_modulo_division_lemma_1 (v hi) 14 48 }
    (v hi / pow2 14) % pow2 34;
    };

  assert_norm (0x3ffffff = pow2 26 - 1);
  mod_mask_lemma (t3 >>. 4ul) 26ul;
  assert (v (mod_mask #U64 #SEC 26ul) == v (u64 0x3ffffff));
  assert (v f3 == v (t3 >>. 30ul) % pow2 26);
  assert (v f3 == ((v hi / pow2 14) % pow2 34) % pow2 26);
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (v hi / pow2 14) 26 34
#pop-options

let load_tup64_4_compact_lemma lo hi =
  let (l0, l1, l2, l3, l4) = load_tup64_4_compact lo hi in
  let (r0, r1, r2, r3, r4) = load_tup64_lemma lo hi in
  assert (l0 == r0 /\ l1 == r1 /\ l4 == r4);

  let mask26 = u64 0x3ffffff in
  let t3 = (lo >>. 48ul) |. (hi <<. 16ul) in
  let l2 = (t3 >>. 4ul) &. mask26 in
  load_tup64_4_compact_lemma_f2 lo hi;
  let r2 = (lo >>. 52ul) |. ((hi &. u64 0x3fff) <<. 12ul) in
  load_tup64_lemma_f2 lo hi;
  assert (v l2 == v r2);

  let r3 = (hi >>. 14ul) &. mask26 in
  mod_mask_lemma (hi >>. 14ul) 26ul;
  assert (v (mod_mask #U64 #SEC 26ul) == v mask26);
  assert (v r3 == (v hi / pow2 14) % pow2 26);

  let l3 = (t3 >>. 30ul) &. mask26 in
  load_tup64_4_compact_lemma_f3 lo hi

#push-options "--z3rlimit 200"
#restart-solver
let lemma_store_felem_lo f lo =
  let (f0, f1, f2, f3, f4) = f in
  assert_norm (max26 = pow2 26 - 1);
  let lo = f0 |. (f1 <<. 26ul) |. (f2 <<. 52ul) in
  assert (v (f1 <<. 26ul) == v f1 * pow2 26 % pow2 64);
  FStar.Math.Lemmas.modulo_lemma (v f1 * pow2 26) (pow2 64);
  FStar.Math.Lemmas.pow2_multiplication_modulo_lemma_1 (v f1) 26 26;
  logor_disjoint f0 (f1 <<. 26ul) 26;
  assert (v (f0 |. (f1 <<. 26ul)) == v f0 + v f1 * pow2 26);

  assert_norm (pow2 26 * pow2 26 = pow2 52);
  assert (v f0 + v f1 * pow2 26 < pow2 52);
  assert (((v f2 * pow2 52) % pow2 64) % pow2 52 = 0);
  logor_disjoint (f0 |. (f1 <<. 26ul)) (f2 <<. 52ul) 52
#pop-options

let lemma_store_felem_hi f hi =
  let (f0, f1, f2, f3, f4) = f in
  assert_norm (max26 = pow2 26 - 1);
  let hi = (f2 >>. 12ul) |. (f3 <<. 14ul) |. (f4 <<. 40ul) in
  FStar.Math.Lemmas.lemma_div_lt (v f2) 26 12;
  assert (v f2 / pow2 12 < pow2 14);

  assert (v (f3 <<. 14ul) == v f3 * pow2 14 % pow2 64);
  FStar.Math.Lemmas.lemma_mult_le_right (pow2 14) (v f3) (pow2 26);
  assert_norm (pow2 26 * pow2 14 = pow2 40);
  assert_norm (pow2 40 < pow2 64);
  FStar.Math.Lemmas.modulo_lemma (v f3 * pow2 14) (pow2 64);
  FStar.Math.Lemmas.pow2_multiplication_modulo_lemma_1 (v f3) 14 14;
  assert ((v f3 * pow2 14) % pow2 14 = 0);
  logor_disjoint (f2 >>. 12ul) (f3 <<. 14ul) 14;
  assert (v ((f2 >>. 12ul) |. (f3 <<. 14ul)) == v f2 / pow2 12 + v f3 * pow2 14);

  FStar.Math.Lemmas.lemma_mult_le_right (pow2 14) (v f3) (pow2 26 - 1);
  assert (v f2 / pow2 12 + v f3 * pow2 14 < pow2 40);
  FStar.Math.Lemmas.pow2_modulo_modulo_lemma_1 (v f4 * pow2 40) 40 64;
  assert (((v f4 * pow2 40) % pow2 64) % pow2 40 = (v f4 * pow2 40) % pow2 40);
  FStar.Math.Lemmas.pow2_multiplication_modulo_lemma_1 (v f4) 40 40;
  assert ((v f4 * pow2 40) % pow2 40 = 0);
  logor_disjoint ((f2 >>. 12ul) |. (f3 <<. 14ul)) (f4 <<. 40ul) 40

let lemma_tup64_pow2_128 f =
  let (f0, f1, f2, f3, f4) = f in
  let tmp = v f0 + v f1 * pow26 + v f2 * pow52 + v f3 * pow78 + (v f4 % pow2 24) * pow104 in
  assert (tmp <= pow2 26 - 1 + (pow2 26 - 1) * pow26 + (pow2 26 - 1) * pow52 +
    (pow2 26 - 1) * pow78 + (pow2 24 - 1) * pow104);
  assert (tmp <= pow2 24 * pow104 - 1);
  assert_norm (pow2 24 * pow104 = pow2 128)

let lemma_tup64_mod_pow2_128 f =
  let (f0, f1, f2, f3, f4) = f in
  let tmp = v f0 + v f1 * pow26 + v f2 * pow52 + v f3 * pow78 in

  calc (==) {
    (as_nat5 f) % pow2 128;
    == { }
    (v f0 + v f1 * pow26 + v f2 * pow52 + v f3 * pow78 + v f4 * pow104) % pow2 128;
    == { FStar.Math.Lemmas.lemma_mod_plus_distr_r tmp (v f4 * pow104) (pow2 128) }
    (tmp + (v f4 * pow104 % pow2 128)) % pow2 128;
    == { FStar.Math.Lemmas.pow2_multiplication_modulo_lemma_2 (v f4) 128 104 }
    (tmp + (v f4 % pow2 24) * pow104) % pow2 128;
    == { lemma_tup64_pow2_128 f; FStar.Math.Lemmas.modulo_lemma (tmp + (v f4 % pow2 24) * pow104) (pow2 128) }
    tmp + (v f4 % pow2 24) * pow104;
  };
  assert ((as_nat5 f) % pow2 128 == tmp + (v f4 % pow2 24) * pow104)

let store_tup64_lemma f =
  let (f0, f1, f2, f3, f4) = f in
  let lo = f0 |. (f1 <<. 26ul) |. (f2 <<. 52ul) in
  let hi = (f2 >>. 12ul) |. (f3 <<. 14ul) |. (f4 <<. 40ul) in
  lemma_store_felem_lo f lo;
  lemma_store_felem_hi f hi;

  assert (v lo == v f0 + v f1 * pow2 26 + (v f2 * pow2 52) % pow2 64);
  assert (v hi == v f2 / pow2 12 + v f3 * pow2 14 + (v f4 * pow2 40) % pow2 64);

  calc (==) {
    v lo + v hi * pow2 64;
    == { }
    v f0 + v f1 * pow2 26 + (v f2 * pow2 52) % pow2 64 +
    (v f2 / pow2 12 + v f3 * pow2 14 + (v f4 * pow2 40) % pow2 64) * pow2 64;
    == { }
    v f0 + v f1 * pow2 26 + (v f2 * pow2 52) % pow2 64 +
    v f2 / pow2 12 * pow2 64 + v f3 * pow2 14 * pow2 64 + (v f4 * pow2 40) % pow2 64 * pow2 64;
    == { FStar.Math.Lemmas.pow2_multiplication_modulo_lemma_2 (v f4) 64 40 }
    v f0 + v f1 * pow2 26 + (v f2 * pow2 52) % pow2 64 +
    v f2 / pow2 12 * pow2 64 + v f3 * pow2 14 * pow2 64 + (v f4 % pow2 24) * pow2 40 * pow2 64;
    == { FStar.Math.Lemmas.pow2_multiplication_modulo_lemma_2 (v f2) 64 52 }
    v f0 + v f1 * pow2 26 + (v f2 % pow2 12) * pow2 52 +
    v f2 / pow2 12 * pow2 64 + v f3 * pow2 14 * pow2 64 + (v f4 % pow2 24) * pow2 40 * pow2 64;
    == { assert_norm (pow2 40 * pow2 64 = pow104) }
    v f0 + v f1 * pow2 26 + (v f2 % pow2 12) * pow2 52 +
    v f2 / pow2 12 * pow2 64 + v f3 * pow2 14 * pow2 64 + (v f4 % pow2 24) * pow104;
    == { assert_norm (pow2 14 * pow2 64 = pow78) }
    v f0 + v f1 * pow2 26 + (v f2 % pow2 12) * pow2 52 +
    v f2 / pow2 12 * pow2 64 + v f3 * pow78 + (v f4 % pow2 24) * pow104;
    == { assert_norm (pow2 12 * pow52 = pow2 64) }
    v f0 + v f1 * pow2 26 + (v f2 % pow2 12 + v f2 / pow2 12 * pow2 12) * pow52 +
    v f3 * pow78 + (v f4 % pow2 24) * pow104;
    == { FStar.Math.Lemmas.euclidean_division_definition (v f2) (pow2 12) }
    v f0 + v f1 * pow2 26 + v f2 * pow52 + v f3 * pow78 + (v f4 % pow2 24) * pow104;
    == { lemma_tup64_mod_pow2_128 f }
    (as_nat5 f) % pow2 128;
    };
  assert (v lo + v hi * pow2 64 == (as_nat5 f) % pow2 128);
  lo, hi

#push-options "--max_ifuel 1"
let store_felem5_lemma #w f =
  let (lo, hi) = store_felem5 f in
  assert (store_tup64_lemma (as_tup64_i f 0) == (lo, hi))
#pop-options

let lemma_sum_lt_pow2_26 i a b =
  assert (a + b < pow2 (i % 26) + pow2 (i % 26));
  FStar.Math.Lemmas.pow2_le_compat 25 (i % 26);
  assert (a + b < pow2 25 + pow2 25);
  FStar.Math.Lemmas.pow2_double_sum 25;
  assert_norm (pow26 = pow2 26)

let lset_bit5_lemma_aux fi i =
  let b = u64 1 <<. size (i % 26) in
  FStar.Math.Lemmas.pow2_lt_compat 26 (i % 26);
  FStar.Math.Lemmas.pow2_lt_compat 64 26;
  FStar.Math.Lemmas.modulo_lemma (pow2 (i % 26)) (pow2 64);
  assert (v b == pow2 (i % 26));
  logor_disjoint fi b (i % 26);
  let out_i = fi |. b in
  assert (v out_i == v fi + v b);
  assert (v out_i == v fi + pow2 (i % 26));
  lemma_sum_lt_pow2_26 i (v fi) (v b);
  assert_norm (pow26 = pow2 26);
  assert (v out_i <= max26)

let lset_bit5_lemma0 f i =
  let b = u64 1 <<. size (i % 26) in
  let out = f.[0] <- f.[0] |. b in
  assert (v f.[i / 26] < pow2 (i % 26));
  lset_bit5_lemma_aux f.[0] i;
  assert (v out.[0] == v f.[0] + pow2 (i % 26));
  lemma_sum_lt_pow2_26 i (v f.[0]) (pow2 (i % 26));

  let (f0, f1, f2, f3, f4) = (f.[0], f.[1], f.[2], f.[3], f.[4]) in
  let (o0, o1, o2, o3, o4) = (out.[0], out.[1], out.[2], out.[3], out.[4]) in
  calc (==) {
    as_nat5 (o0, o1, o2, o3, o4);
    == { }
    v o0 + v o1 * pow26 + v o2 * pow52 + v o3 * pow78 + v o4 * pow104;
    == { }
    pow2 (i % 26) + as_nat5 (f0, f1, f2, f3, f4);
    == { FStar.Math.Lemmas.euclidean_division_definition i 26 }
    pow2 i + as_nat5 (f0, f1, f2, f3, f4);
    };
  assert (as_nat5 (o0, o1, o2, o3, o4) == pow2 i + as_nat5 (f0, f1, f2, f3, f4))


let lset_bit5_lemma1 f i =
  let b = u64 1 <<. size (i % 26) in
  let out = f.[1] <- f.[1] |. b in
  let (f0, f1, f2, f3, f4) = (f.[0], f.[1], f.[2], f.[3], f.[4]) in
  let (o0, o1, o2, o3, o4) = (out.[0], out.[1], out.[2], out.[3], out.[4]) in
  assert (v f1 * pow2 26 < pow2 i);
  FStar.Math.Lemmas.lemma_div_lt_nat (v f1 * pow2 26) i 26;
  assert (v f1 < pow2 (i - 26));
  assert (i - 26 == i % 26);
  assert (v f.[1] < pow2 (i % 26));
  lset_bit5_lemma_aux f.[1] i;
  assert (v out.[1] == v f.[1] + pow2 (i % 26));
  lemma_sum_lt_pow2_26 i (v f.[1]) (pow2 (i % 26));

  calc (==) {
    as_nat5 (o0, o1, o2, o3, o4);
    == { }
    v o0 + v o1 * pow26 + v o2 * pow52 + v o3 * pow78 + v o4 * pow104;
    == { }
    pow2 (i % 26) * pow26 + as_nat5 (f0, f1, f2, f3, f4);
    == { FStar.Math.Lemmas.pow2_plus (i % 26) 26 }
    pow2 (i % 26 + 26) + as_nat5 (f0, f1, f2, f3, f4);
    == { FStar.Math.Lemmas.euclidean_division_definition i 26 }
    pow2 i + as_nat5 (f0, f1, f2, f3, f4);
    };
  assert (as_nat5 (o0, o1, o2, o3, o4) == pow2 i + as_nat5 (f0, f1, f2, f3, f4))

let lset_bit5_lemma2 f i =
  let b = u64 1 <<. size (i % 26) in
  let out = f.[2] <- f.[2] |. b in
  let (f0, f1, f2, f3, f4) = (f.[0], f.[1], f.[2], f.[3], f.[4]) in
  let (o0, o1, o2, o3, o4) = (out.[0], out.[1], out.[2], out.[3], out.[4]) in
  assert (v f2 * pow52 < pow2 i);
  FStar.Math.Lemmas.lemma_div_lt_nat (v f2 * pow52) i 52;
  assert (v f2 < pow2 (i - 52));
  assert (i - 52 == i % 26);
  assert (v f.[2] < pow2 (i % 26));
  lset_bit5_lemma_aux f.[2] i;
  assert (v out.[2] == v f.[2] + pow2 (i % 26));
  lemma_sum_lt_pow2_26 i (v f.[2]) (pow2 (i % 26));

  calc (==) {
    as_nat5 (o0, o1, o2, o3, o4);
    == { }
    v o0 + v o1 * pow26 + v o2 * pow52 + v o3 * pow78 + v o4 * pow104;
    == { }
    pow2 (i % 26) * pow52 + as_nat5 (f0, f1, f2, f3, f4);
    == { FStar.Math.Lemmas.pow2_plus (i % 26) 52 }
    pow2 (i % 26 + 52) + as_nat5 (f0, f1, f2, f3, f4);
    == { FStar.Math.Lemmas.euclidean_division_definition i 26 }
    pow2 i + as_nat5 (f0, f1, f2, f3, f4);
    };
  assert (as_nat5 (o0, o1, o2, o3, o4) == pow2 i + as_nat5 (f0, f1, f2, f3, f4))

let lset_bit5_lemma3 f i =
  let b = u64 1 <<. size (i % 26) in
  let out = f.[3] <- f.[3] |. b in
  let (f0, f1, f2, f3, f4) = (f.[0], f.[1], f.[2], f.[3], f.[4]) in
  let (o0, o1, o2, o3, o4) = (out.[0], out.[1], out.[2], out.[3], out.[4]) in
  assert (v f3 * pow78 < pow2 i);
  FStar.Math.Lemmas.lemma_div_lt_nat (v f3 * pow78) i 78;
  assert (v f3 < pow2 (i - 78));
  assert (i - 78 == i % 26);
  assert (v f.[3] < pow2 (i % 26));
  lset_bit5_lemma_aux f.[3] i;
  assert (v out.[3] == v f.[3] + pow2 (i % 26));
  lemma_sum_lt_pow2_26 i (v f.[3]) (pow2 (i % 26));

  calc (==) {
    as_nat5 (o0, o1, o2, o3, o4);
    == { }
    v o0 + v o1 * pow26 + v o2 * pow52 + v o3 * pow78 + v o4 * pow104;
    == { }
    pow2 (i % 26) * pow78 + as_nat5 (f0, f1, f2, f3, f4);
    == { FStar.Math.Lemmas.pow2_plus (i % 26) 78 }
    pow2 (i % 26 + 78) + as_nat5 (f0, f1, f2, f3, f4);
    == { FStar.Math.Lemmas.euclidean_division_definition i 26 }
    pow2 i + as_nat5 (f0, f1, f2, f3, f4);
    };
  assert (as_nat5 (o0, o1, o2, o3, o4) == pow2 i + as_nat5 (f0, f1, f2, f3, f4))

let lset_bit5_lemma4 f i =
  let b = u64 1 <<. size (i % 26) in
  let out = f.[4] <- f.[4] |. b in
  let (f0, f1, f2, f3, f4) = (f.[0], f.[1], f.[2], f.[3], f.[4]) in
  let (o0, o1, o2, o3, o4) = (out.[0], out.[1], out.[2], out.[3], out.[4]) in
  assert (v f4 * pow104 < pow2 i);
  FStar.Math.Lemmas.lemma_div_lt_nat (v f4 * pow104) i 104;
  assert (v f4 < pow2 (i - 104));
  assert (i - 104 == i % 26);
  assert (v f.[4] < pow2 (i % 26));
  lset_bit5_lemma_aux f.[4] i;
  assert (v out.[4] == v f.[4] + pow2 (i % 26));
  lemma_sum_lt_pow2_26 i (v f.[4]) (pow2 (i % 26));

  calc (==) {
    as_nat5 (o0, o1, o2, o3, o4);
    == { }
    v o0 + v o1 * pow26 + v o2 * pow52 + v o3 * pow78 + v o4 * pow104;
    == { }
    pow2 (i % 26) * pow104 + as_nat5 (f0, f1, f2, f3, f4);
    == { FStar.Math.Lemmas.pow2_plus (i % 26) 104 }
    pow2 (i % 26 + 104) + as_nat5 (f0, f1, f2, f3, f4);
    == { FStar.Math.Lemmas.euclidean_division_definition i 26 }
    pow2 i + as_nat5 (f0, f1, f2, f3, f4);
    };
  assert (as_nat5 (o0, o1, o2, o3, o4) == pow2 i + as_nat5 (f0, f1, f2, f3, f4))

let lset_bit5_ f i =
  let ind = i / 26 in
  let j = i % 26 in
  FStar.Math.Lemmas.euclidean_division_definition i 26;
  assert (i == ind * 26 + j);

  match ind with
  | 0 -> lset_bit5_lemma0 f i
  | 1 -> lset_bit5_lemma1 f i
  | 2 -> lset_bit5_lemma2 f i
  | 3 -> lset_bit5_lemma3 f i
  | 4 -> lset_bit5_lemma4 f i

let lset_bit5 f i =
  let b = u64 1 <<. size (i % 26) in
  let out = f.[i / 26] <- f.[i / 26] |. b in
  lset_bit5_ f i;
  let out = (out.[0], out.[1], out.[2], out.[3], out.[4]) in
  let f = (f.[0], f.[1], f.[2], f.[3], f.[4]) in
  assert (as_nat5 out % prime == (pow2 i + as_nat5 f) % prime);
  FStar.Math.Lemmas.lemma_mod_plus_distr_r (pow2 i) (as_nat5 f) prime

let set_bit5_lemma_k #w f i k =
  let lf = create 5 (u64 0) in
  let lf = lf.[0] <- (vec_v f.[0]).[k] in
  let lf = lf.[1] <- (vec_v f.[1]).[k] in
  let lf = lf.[2] <- (vec_v f.[2]).[k] in
  let lf = lf.[3] <- (vec_v f.[3]).[k] in
  let lf = lf.[4] <- (vec_v f.[4]).[k] in
  lset_bit5 lf i
