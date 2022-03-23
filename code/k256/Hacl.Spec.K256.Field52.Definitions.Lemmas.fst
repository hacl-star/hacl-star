module Hacl.Spec.K256.Field52.Definitions.Lemmas

open FStar.Mul
open Lib.IntTypes

open Hacl.Spec.K256.Field52.Definitions

module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence

module S = Spec.K256
module ML = Hacl.Spec.K256.MathLemmas

#set-options "--z3rlimit 100 --fuel 0 --ifuel 0"

val lemma_as_nat_mod2: x:felem5 ->
  Lemma (let (x0,x1,x2,x3,x4) = x in as_nat5 x % 2 = v x0 % 2)
let lemma_as_nat_mod2 x =
  let (x0,x1,x2,x3,x4) = x in
  assert (as_nat5 x = v x0 + v x1 * pow52 + v x2 * pow104 + v x3 * pow156 + v x4 * pow208);
  assert (as_nat5 x % 2 = (v x0 + v x1 * pow52 + v x2 * pow104 + v x3 * pow156 + v x4 * pow208) % 2);
  ML.lemma_a_plus_b_pow2_mod2 (v x0 + v x1 * pow52 + v x2 * pow104 + v x3 * pow156) (v x4) 208;
  ML.lemma_a_plus_b_pow2_mod2 (v x0 + v x1 * pow52 + v x2 * pow104) (v x3) 156;
  ML.lemma_a_plus_b_pow2_mod2 (v x0 + v x1 * pow52) (v x2) 104;
  ML.lemma_a_plus_b_pow2_mod2 (v x0) (v x1) 52;
  assert (as_nat5 x % 2 = v x0 % 2)


val lemma_nat_from_bytes_be_mod2: f:LSeq.lseq uint8 32 ->
  Lemma (BSeq.nat_from_bytes_be f % 2 = v (LSeq.index f 31) % 2)

let lemma_nat_from_bytes_be_mod2 f =
  let x0 = LSeq.index f 31 in
  BSeq.nat_from_intseq_be_slice_lemma f 31;
  BSeq.nat_from_intseq_be_lemma0 (LSeq.slice f 31 32);
  assert (BSeq.nat_from_intseq_be f == v x0 + pow2 8 * BSeq.nat_from_intseq_be (LSeq.slice f 0 31));
  ML.lemma_a_plus_b_pow2_mod2 (v x0) (BSeq.nat_from_intseq_be (LSeq.slice f 0 31)) 8


val unfold_nat_from_uint64_four: b:LSeq.lseq uint64 4 ->
  Lemma (BSeq.nat_from_intseq_be b ==
    v (LSeq.index b 3) + v (LSeq.index b 2) * pow2 64 +
    v (LSeq.index b 1) * pow2 128 + v (LSeq.index b 0) * pow2 192)

let unfold_nat_from_uint64_four b =
  let b0 = v (LSeq.index b 0) in
  let b1 = v (LSeq.index b 1) in
  let b2 = v (LSeq.index b 2) in
  let b3 = v (LSeq.index b 3) in

  let res = BSeq.nat_from_intseq_be b in
  BSeq.nat_from_intseq_be_slice_lemma b 3;
  BSeq.nat_from_intseq_be_lemma0 (Seq.slice b 3 4);
  assert (res == b3 + pow2 64 * (BSeq.nat_from_intseq_be (Seq.slice b 0 3)));

  BSeq.nat_from_intseq_be_slice_lemma #U64 #SEC #3 (Seq.slice b 0 3) 2;
  BSeq.nat_from_intseq_be_lemma0 (Seq.slice b 2 3);
  assert (BSeq.nat_from_intseq_be (Seq.slice b 0 3) == b2 + pow2 64 * (BSeq.nat_from_intseq_be (Seq.slice b 0 2)));

  BSeq.nat_from_intseq_be_slice_lemma #U64 #SEC #2 (Seq.slice b 0 2) 1;
  BSeq.nat_from_intseq_be_lemma0 (Seq.slice b 1 2);
  assert (BSeq.nat_from_intseq_be (Seq.slice b 0 2) == b1 + pow2 64 * (BSeq.nat_from_intseq_be (Seq.slice b 0 1)));

  BSeq.nat_from_intseq_be_lemma0 (Seq.slice b 0 1);
  assert (res == b3 + pow2 64 * (b2 + pow2 64 * (b1 + pow2 64 * b0)));
  ML.lemma_as_nat64_horner b3 b2 b1 b0


val lemma_prime : unit -> Lemma (pow2 256 % S.prime = 0x1000003D1)
let lemma_prime () = ()

val lemma_pow2_256_minus_prime : unit -> Lemma (pow2 256 - S.prime = 0x1000003D1)
let lemma_pow2_256_minus_prime () = ()

val lemma_pow2_260_mod_prime: unit -> Lemma (pow2 260 % S.prime = 0x1000003D10)
let lemma_pow2_260_mod_prime () =
  calc (==) {
    pow2 260 % S.prime;
    (==) { Math.Lemmas.pow2_plus 256 4 }
    pow2 256 * pow2 4 % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (pow2 256) (pow2 4) S.prime }
    (pow2 256 % S.prime) * pow2 4 % S.prime;
    (==) { lemma_prime () }
    0x1000003D1 * pow2 4 % S.prime;
    (==) { assert_norm (0x1000003D1 * pow2 4 = 0x1000003D10) }
    0x1000003D10 % S.prime;
    (==) { Math.Lemmas.small_mod 0x1000003D10 S.prime }
    0x1000003D10;
  }


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
  calc (==) {
    (2 * (pow2 48 - 1)) / pow2 48;
    (==) { Math.Lemmas.distributivity_add_right 2 (pow2 48) 1 }
    (2 * pow2 48 - 2) / pow2 48;
    (==) { Math.Lemmas.division_addition_lemma (-2) (pow2 48) 2 }
    (-2) / pow2 48 + 2;
    (==) { assert_norm ((-2) / pow2 48 = -1) }
    1;
  };

  assert (v t4 <= 2 * (pow2 48 - 1));
  Math.Lemmas.lemma_div_le (v t4) (2 * pow2 48 - 2) (pow2 48);
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


val lemma_mask52: a:uint64 ->
  Lemma (let r = a &. mask52 in
    v r = v a % pow2 52 /\ felem_fits1 r 1)

let lemma_mask52 a =
  let r = a &. mask52 in
  assert_norm (v mask52 = pow2 52 - 1);
  mod_mask_lemma a 52ul;
  assert (v (mod_mask #U64 #SEC 52ul) == v mask52);
  assert (v r = v a % pow2 52);
  assert (felem_fits1 r 1)


val lemma_mask48: a:uint64 ->
  Lemma (let r = a &. mask48 in
    v r = v a % pow2 48 /\ felem_fits_last1 r 1)

let lemma_mask48 a =
  let r = a &. mask48 in
  assert_norm (v mask48 = pow2 48 - 1);
  mod_mask_lemma a 48ul;
  assert (v (mod_mask #U64 #SEC 48ul) == v mask48);
  assert (v r = v a % pow2 48);
  assert (felem_fits_last1 r 1)


val lemma_add_rsh52: m1:scale64 -> m2:scale64 -> a:uint64 -> b:uint64 -> Lemma
  (requires felem_fits1 a m1 /\ felem_fits1 b m2 /\ m1 + 1 <= 4096)
  (ensures (let c = a +. (b >>. 52ul) in
     felem_fits1 c (m1 + 1) /\ v c = v a + v b / pow2 52))

let lemma_add_rsh52 m1 m2 a b =
  let c = a +. (b >>. 52ul) in
  calc (<) {
    v a + v b / pow2 52;
    (<) { Math.Lemmas.lemma_div_lt (v b) 64 52 }
    m1 * max52 + pow2 12;
    (<=) { Math.Lemmas.pow2_lt_compat 52 12 }
    m1 * max52 + max52;
    (==) { Math.Lemmas.distributivity_add_left m1 1 max52 }
    (m1 + 1) * max52;
  };

  Math.Lemmas.lemma_mult_le_right max52 (m1 + 1) 4096;
  assert_norm (4096 * max52 < pow2 64);
  Math.Lemmas.small_mod (v a + v b / pow2 52) (pow2 64);
  assert (v c = v a + v b / pow2 52);
  assert (felem_fits1 c (m1 + 1))


val lemma_add_rsh52_last: m1:scale64_last -> m2:scale64 -> a:uint64 -> b:uint64 -> Lemma
  (requires felem_fits_last1 a m1 /\ felem_fits1 b m2 /\ m1 + 1 <= 65536)
  (ensures (let c = a +. (b >>. 52ul) in
    felem_fits_last1 c (m1 + 1) /\ v c = v a + v b / pow2 52))

let lemma_add_rsh52_last m1 m2 a b =
  let c = a +. (b >>. 52ul) in
  calc (<) {
    v a + v b / pow2 52;
    (<) { Math.Lemmas.lemma_div_lt (v b) 64 52 }
    m1 * max48 + pow2 12;
    (<=) { Math.Lemmas.pow2_lt_compat 48 12 }
    m1 * max48 + max48;
    (==) { Math.Lemmas.distributivity_add_left m1 1 max48 }
    (m1 + 1) * max48;
  };

  Math.Lemmas.lemma_mult_le_right max48 (m1 + 1) 65536;
  assert_norm (65536 * max48 < pow2 64);
  Math.Lemmas.small_mod (v a + v b / pow2 52) (pow2 64);
  assert (v c = v a + v b / pow2 52);
  assert (felem_fits_last1 c (m1 + 1))


val lemma_carry52: m1:scale64 -> m2:scale64 -> a:uint64 -> b:uint64 -> Lemma
  (requires felem_fits1 a m1 /\ felem_fits1 b m2 /\ m1 + 1 <= 4096)
  (ensures
    (let c = a +. (b >>. 52ul) in let d = b &. mask52 in
     felem_fits1 d 1 /\ felem_fits1 c (m1 + 1) /\
     v d = v b % pow2 52 /\ v c = v a + v b / pow2 52))

let lemma_carry52 m1 m2 a b =
  lemma_mask52 b;
  lemma_add_rsh52 m1 m2 a b


val lemma_carry_last52: m1:scale64_last -> m2:scale64 -> a:uint64 -> b:uint64 -> Lemma
  (requires felem_fits_last1 a m1 /\ felem_fits1 b m2 /\ m1 + 1 <= 65536)
  (ensures
    (let c = a +. (b >>. 52ul) in let d = b &. mask52 in
     felem_fits1 d 1 /\ felem_fits_last1 c (m1 + 1) /\
     v d = v b % pow2 52 /\ v c = v a + v b / pow2 52))

let lemma_carry_last52 m1 m2 a b =
  lemma_mask52 b;
  lemma_add_rsh52_last m1 m2 a b


val lemma_small_sub_mod: a:nat -> n:pos -> Lemma
  (requires n <= a /\ a < 2 * n)
  (ensures  a % n = a - n)

let lemma_small_sub_mod a n =
  calc (==) {
    a % n;
    (==) { Math.Lemmas.sub_div_mod_1 a n }
    (a - n) % n;
    (==) { Math.Lemmas.small_mod (a - n) n }
    a - n;
  }


val carry_last_small_mod_lemma: t4:uint64 -> t3':uint64 -> Lemma
  (requires felem_fits_last1 t4 1 /\
    v (t4 +. (t3' >>. 52ul)) == v t4 + v t3' / pow2 52)
  (ensures  (let r = t4 +. (t3' >>. 52ul) in
    felem_fits_last1 r 2 /\
    v r < v t4 + pow2 12 /\ (v r >= pow2 48 ==> v r % pow2 48 < pow2 12)))

let carry_last_small_mod_lemma t4 t3' =
  let r = t4 +. (t3' >>. 52ul) in
  assert (v r = v t4 + v t3' / pow2 52);
  Math.Lemmas.lemma_div_lt (v t3') 64 52;
  assert (v r < v t4 + pow2 12);
  Math.Lemmas.pow2_lt_compat 48 12;
  assert (felem_fits_last1 r 2);

  if v r >= pow2 48 then begin
    lemma_small_sub_mod (v r) (pow2 48);
    assert (v r % pow2 48 = v r - pow2 48);
    assert (v r % pow2 48 < pow2 12) end


val lemma_a_plus_b_mul_pow256 (a b:int) :
  Lemma ((a + b * pow2 256) % S.prime == (a + b * 0x1000003D1) % S.prime)

let lemma_a_plus_b_mul_pow256 a b =
  calc (==) {
    (a + b * pow2 256) % S.prime;
    (==) { Math.Lemmas.lemma_mod_plus_distr_r a (b * pow2 256) S.prime }
    (a + b * pow2 256 % S.prime) % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r b (pow2 256) S.prime }
    (a + b * (pow2 256 % S.prime) % S.prime) % S.prime;
    (==) { lemma_prime () }
    (a + b * 0x1000003D1 % S.prime) % S.prime;
    (==) { Math.Lemmas.lemma_mod_plus_distr_r a (b * 0x1000003D1) S.prime }
    (a + b * 0x1000003D1) % S.prime;
  }


val as_nat_mod_prime (t0 t1 t2 t3 t4:int) : Lemma
  ((t0 + t1 * pow52 + t2 * pow104 + t3 * pow156 + t4 * pow208) % S.prime =
   (t0 + t1 * pow52 + t2 * pow104 + t3 * pow156 + (t4 % pow2 48) * pow208 + t4 / pow2 48 * 0x1000003D1) % S.prime)

let as_nat_mod_prime t0 t1 t2 t3 t4 =
  calc (==) {
    (t0 + t1 * pow52 + t2 * pow104 + t3 * pow156 + t4 * pow208) % S.prime;
    (==) { Math.Lemmas.euclidean_division_definition t4 (pow2 48) }
    (t0 + t1 * pow52 + t2 * pow104 + t3 * pow156 + (t4 / pow2 48 * pow2 48 + t4 % pow2 48) * pow208) % S.prime;
    (==) { Math.Lemmas.distributivity_add_left (t4 / pow2 48 * pow2 48) (t4 % pow2 48) pow208 }
    (t0 + t1 * pow52 + t2 * pow104 + t3 * pow156 + t4 / pow2 48 * pow2 48 * pow208 + t4 % pow2 48 * pow208) % S.prime;
    (==) { Math.Lemmas.paren_mul_right (t4 / pow2 48) (pow2 48) pow208; Math.Lemmas.pow2_plus 48 208 }
    (t0 + t1 * pow52 + t2 * pow104 + t3 * pow156 + t4 / pow2 48 * pow2 256 + t4 % pow2 48 * pow208) % S.prime;
    (==) { lemma_a_plus_b_mul_pow256 (t0 + t1 * pow52 + t2 * pow104 + t3 * pow156 + t4 % pow2 48 * pow208) (t4 / pow2 48) }
    (t0 + t1 * pow52 + t2 * pow104 + t3 * pow156 + t4 % pow2 48 * pow208 + t4 / pow2 48 * 0x1000003D1) % S.prime;
  }
