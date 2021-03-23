module Hacl.Spec.AlmostMontgomery.Lemmas

open FStar.Mul

open Lib.IntTypes
open Lib.LoopCombinators

module M = Hacl.Spec.Montgomery.Lemmas

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

///  High-level specification of Almost Montgomery Multiplication

val almost_mont_reduction: pbits:pos -> rLen:nat -> n:pos -> mu:nat -> c:nat -> int
let almost_mont_reduction pbits rLen n mu c =
  let res = M.mont_reduction_loop_div_r pbits rLen n mu c in
  if res < pow2 (pbits * rLen) then res else res - n

val almost_mont_mul: pbits:pos -> rLen:nat -> n:pos -> mu:nat -> a:nat -> b:nat -> int
let almost_mont_mul pbits rLen n mu a b =
  let c = a * b in
  almost_mont_reduction pbits rLen n mu c

val almost_mont_sqr: pbits:pos -> rLen:nat -> n:pos -> mu:nat -> a:nat -> int
let almost_mont_sqr pbits rLen n mu a =
  let c = a * a in
  almost_mont_reduction pbits rLen n mu c


///  Lemma (almost_mont_mul pbits rLen n mu a b % n == a * b * d % n)

val lemma_fits_c_lt_rr: c:nat -> r:pos -> n:pos -> Lemma
  (requires c < r * r)
  (ensures (c - n) / r < r)

let lemma_fits_c_lt_rr c r n =
  assert (c < r * r);
  Math.Lemmas.cancel_mul_div r r;
  assert (c / r < r);
  Math.Lemmas.lemma_div_le (c - n) c r


val almost_mont_reduction_lemma: pbits:pos -> rLen:nat -> n:pos -> d:int -> mu:nat -> c:nat -> Lemma
  (requires (let r = pow2 (pbits * rLen) in
    (1 + n * mu) % pow2 pbits == 0 /\ r * d % n == 1 /\ c < r * r))
  (ensures  (let res = almost_mont_reduction pbits rLen n mu c in
    let r = pow2 (pbits * rLen) in
    res % n == c * d % n /\ res < r))

let almost_mont_reduction_lemma pbits rLen n d mu c =
  let r = pow2 (pbits * rLen) in
  let res = M.mont_reduction_loop_div_r pbits rLen n mu c in
  M.mont_reduction_loop_div_r_lemma pbits rLen n d mu c;
  assert (res % n == c * d % n /\ res <= (c - n) / r + n);

  let res1 = if res < r then res else res - n in
  if res < r then ()
  else begin
    assert (res1 % n == (res - n) % n);
    Math.Lemmas.lemma_mod_sub res n 1;
    assert (res1 % n == res % n);
    assert (res1 <= (c - n) / r);
    lemma_fits_c_lt_rr c r n end


val almost_mont_mul_lemma: pbits:pos -> rLen:nat -> n:pos -> d:int-> mu:nat -> a:nat -> b:nat -> Lemma
  (requires (let r = pow2 (pbits * rLen) in
    (1 + n * mu) % pow2 pbits == 0 /\ r * d % n == 1 /\ a < r /\ b < r /\ n < r))
  (ensures  (let res = almost_mont_mul pbits rLen n mu a b in
    let r = pow2 (pbits * rLen) in
    res % n == a * b * d % n /\ res < r))

let almost_mont_mul_lemma pbits rLen n d mu a b =
  let r = pow2 (pbits * rLen) in
  let res = almost_mont_mul pbits rLen n mu a b in
  Math.Lemmas.lemma_mult_lt_sqr a b r;
  assert (a * b < r * r);
  almost_mont_reduction_lemma pbits rLen n d mu (a * b)


///  Properties

val from_almost_mont_mul_lemma: pbits:pos -> rLen:pos -> n:pos -> mu:nat -> aM:nat -> bM:nat -> Lemma
  (requires (let r = pow2 (pbits * rLen) in
    M.mont_pre pbits rLen n mu /\ aM < r /\ bM < r))
  (ensures
   (let cM = almost_mont_mul pbits rLen n mu aM bM in
    let c = M.from_mont pbits rLen n mu cM in
    let a = M.from_mont pbits rLen n mu aM in
    let b = M.from_mont pbits rLen n mu bM in
    c == a * b % n))

let from_almost_mont_mul_lemma pbits rLen n mu aM bM =
  let r = pow2 (pbits * rLen) in
  let d, _ = M.eea_pow2_odd (pbits * rLen) n in
  M.mont_preconditions pbits rLen n mu;
  assert (r * d % n == 1 /\ n < r /\ (1 + n * mu) % pow2 pbits == 0);

  let cM = almost_mont_mul pbits rLen n mu aM bM in
  let c = M.from_mont pbits rLen n mu cM in
  let a = M.from_mont pbits rLen n mu aM in
  let b = M.from_mont pbits rLen n mu bM in

  almost_mont_mul_lemma pbits rLen n d mu aM bM;
  //assert (cM % n == aM * bM * d % n);
  M.from_mont_lemma pbits rLen n d mu cM;
  //assert (c == cM * d % n);

  calc (==) { //c
    cM * d % n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l cM d n }
    (aM * bM * d % n) * d % n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (aM * bM * d) d n }
    aM * bM * d * d % n;
    (==) { Math.Lemmas.paren_mul_right aM bM d }
    aM * (bM * d) * d % n;
    (==) {
      Math.Lemmas.paren_mul_right aM (bM * d) d;
      Math.Lemmas.swap_mul (bM * d) d;
      Math.Lemmas.paren_mul_right aM d (bM * d) }
    aM * d * (bM * d) % n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (aM * d) (bM * d) n }
    (aM * d % n) * (bM * d) % n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r (aM * d % n) (bM * d) n }
    (aM * d % n) * (bM * d % n) % n;
    };

  M.from_mont_lemma pbits rLen n d mu aM;
  M.from_mont_lemma pbits rLen n d mu bM
