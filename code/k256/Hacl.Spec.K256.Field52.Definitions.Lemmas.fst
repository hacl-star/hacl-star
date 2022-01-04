module Hacl.Spec.K256.Field52.Definitions.Lemmas

open FStar.Mul
open Lib.IntTypes

open Hacl.Spec.K256.Field52.Definitions

module S = Spec.K256

#set-options "--z3rlimit 100 --fuel 0 --ifuel 0"

val lemma_prime : unit -> Lemma (pow2 256 % S.prime = 0x1000003D1)
let lemma_prime () = ()

val lemma_pow2_256_minus_prime : unit -> Lemma (pow2 256 - S.prime = 0x1000003D1)
let lemma_pow2_256_minus_prime () = ()



val lemma_as_nat_bound_f4_lt_powa: f:felem5 -> a:nat -> Lemma
  (requires (let (f0,f1,f2,f3,f4) = f in
    felem_fits5 f (1,1,1,1,1) /\ v f4 < pow2 a))
  (ensures as_nat5 f <= pow2 (208 + a) - 1)

let lemma_as_nat_bound_f4_lt_powa f a =
  let (f0,f1,f2,f3,f4) = f in
  calc (<=) { //as_nat5 f ==
    v f0 + v f1 * pow52 + v f2 * pow104 + v f3 * pow156 + v f4 * pow208;
    (<=) { }
    pow2 52 - 1 + v f1 * pow52 + v f2 * pow104 + v f3 * pow156 + v f4 * pow208;
    (<=) {
      Math.Lemmas.lemma_mult_le_right pow52 (v f1) (pow2 52 - 1);
      Math.Lemmas.distributivity_sub_left (pow2 52) 1 pow52 }
    pow2 52 * pow52 + v f2 * pow104 + v f3 * pow156 + v f4 * pow208 - 1;
    (<=) {
      Math.Lemmas.lemma_mult_le_right pow104 (v f2) (pow2 52 - 1);
      Math.Lemmas.distributivity_sub_left (pow2 52) 1 pow104;
      Math.Lemmas.pow2_plus 52 52 }
    pow2 52 * pow104 + v f3 * pow156 + v f4 * pow208 - 1;
    (<=) {
      Math.Lemmas.lemma_mult_le_right pow156 (v f3) (pow2 52 - 1);
      Math.Lemmas.distributivity_sub_left (pow2 52) 1 pow156;
      Math.Lemmas.pow2_plus 52 104 }
    pow2 52 * pow156 + v f4 * pow208 - 1;
    (<=) {
      Math.Lemmas.lemma_mult_le_right pow208 (v f4) (pow2 a - 1);
      Math.Lemmas.distributivity_sub_left (pow2 a) 1 pow208;
      Math.Lemmas.pow2_plus 52 156;
      Math.Lemmas.pow2_plus a 208 }
    pow2 (208 + a) - 1;
    }


val lemma_as_nat_bound: f:felem5 -> Lemma
  (requires felem_fits5 f (1,1,1,1,1))
  (ensures as_nat5 f < pow2 256)

let lemma_as_nat_bound f =
  lemma_as_nat_bound_f4_lt_powa f 48


val lemma_as_nat_bound_f4_lt_pow12: f:felem5 -> Lemma
  (requires (let (f0,f1,f2,f3,f4) = f in
    felem_fits5 f (1,1,1,1,1) /\ v f4 < pow2 12))
  (ensures as_nat5 f <= pow2 220 - 1)

let lemma_as_nat_bound_f4_lt_pow12 f =
  lemma_as_nat_bound_f4_lt_powa f 12


val lemma_as_nat_decompose: f:felem5 -> Lemma
  (requires felem_fits5 f (1,1,1,1,1))
  (ensures (let (f0,f1,f2,f3,f4) = f in
    v f4 = as_nat5 f / pow208 /\
    v f3 = as_nat5 f % pow208 / pow156 /\
    v f2 = as_nat5 f % pow156 / pow104 /\
    v f1 = as_nat5 f % pow104 / pow52 /\
    v f0 = as_nat5 f % pow52))

let lemma_as_nat_decompose f =
  let (f0,f1,f2,f3,f4) = f in
  lemma_as_nat_bound f;

  Math.Lemmas.euclidean_division_definition (as_nat5 f) pow208;
  assert (v f4 = as_nat5 f / pow208);

  Math.Lemmas.euclidean_division_definition (as_nat5 f % pow208) pow156;
  assert (v f3 = as_nat5 f % pow208 / pow156);

  Math.Lemmas.pow2_modulo_modulo_lemma_1 (as_nat5 f) 156 208;
  assert (as_nat5 f % pow208 % pow156 == as_nat5 f % pow156);
  Math.Lemmas.euclidean_division_definition (as_nat5 f % pow156) pow104;
  assert (v f2 = as_nat5 f % pow156 / pow104);

  Math.Lemmas.pow2_modulo_modulo_lemma_1 (as_nat5 f) 104 156;
  assert (as_nat5 f % pow156 % pow104 == as_nat5 f % pow104);
  Math.Lemmas.euclidean_division_definition (as_nat5 f % pow104) pow52;
  assert (v f1 = as_nat5 f % pow104 / pow52);

  Math.Lemmas.pow2_modulo_modulo_lemma_1 (as_nat5 f) 52 104;
  assert (as_nat5 f % pow104 % pow52 == as_nat5 f % pow52);
  assert (v f0 = as_nat5 f % pow52)


#push-options "--ifuel 1"
val as_nat_inj (f1 f2: felem5) : Lemma
  (requires
    felem_fits5 f1 (1,1,1,1,1) /\ felem_fits5 f2 (1,1,1,1,1) /\
    as_nat5 f1 == as_nat5 f2)
  (ensures
   (let (a0,a1,a2,a3,a4) = f1 in let (b0,b1,b2,b3,b4) = f2 in
    a0 == b0 /\ a1 == b1 /\ a2 == b2 /\ a3 == b3 /\ a4 == b4))

let as_nat_inj f1 f2 =
  lemma_as_nat_decompose f1;
  lemma_as_nat_decompose f2
#pop-options


val lemma_normalize_x_le_1: t4:uint64 -> Lemma
  (requires felem_fits_last1 t4 2)
  (ensures  v t4 / pow2 48 <= 1)

let lemma_normalize_x_le_1 t4 =
  assert (v t4 <= 2 * (pow2 48 - 1));
  Math.Lemmas.distributivity_add_right 2 (pow2 48) 1;
  assert (v t4 <= 2 * pow2 48 - 2);
  Math.Lemmas.lemma_div_le (v t4) (2 * pow2 48 - 2) (pow2 48);
  Math.Lemmas.division_addition_lemma (-2) (pow2 48) 2;
  assert (v t4 / pow2 48 <= 1)


val lemma_div_pow48: t4:uint64 -> Lemma
  (requires felem_fits_last1 t4 2)
  (ensures  v t4 / pow2 48 == (if v t4 < pow2 48 then 0 else 1))

let lemma_div_pow48 t4 =
  if v t4 < pow2 48 then
    Math.Lemmas.small_div (v t4) (pow2 48)
  else begin
    lemma_normalize_x_le_1 t4;
    assert (v t4 / pow2 48 <= 1);
    Math.Lemmas.lemma_div_le (pow2 48) (v t4) (pow2 48);
    assert (1 <= v t4 / pow2 48) end
