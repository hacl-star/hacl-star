module Hacl.Spec.Exponentiation.Lemmas

open FStar.Mul
open Lib.NatMod

module M = Hacl.Spec.Montgomery.Lemmas
module Loops = Lib.LoopCombinators
module LE = Lib.Exponentiation

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(* Modular exponentiation with Montgomery arithmetic *)
val oneM: n:pos -> r:pos -> nat_mod n
let oneM n r = 1 * r % n

val fmul_mont: n:pos -> d:int -> a:nat_mod n -> b:nat_mod n -> nat_mod n
let fmul_mont n d a b = a * b * d % n

val lemma_one_mont: n:pos -> r:pos -> d:int{r * d % n = 1} -> a:nat_mod n ->
  Lemma (fmul_mont n d a (oneM n r) == a)
let lemma_one_mont n r d a =
  calc (==) {
    a * (1 * r % n) * d % n;
    (==) { M.lemma_mod_mul_distr3 a r d n }
    a * r * d % n;
    (==) { Math.Lemmas.paren_mul_right a r d; Math.Lemmas.lemma_mod_mul_distr_r a (r * d) n }
    a * (r * d % n) % n;
    (==) { assert (r * d % n = 1) }
    a % n;
    (==) { Math.Lemmas.small_mod a n }
    a;
    }

val lemma_fmul_assoc_mont: n:pos -> d:int -> a:nat_mod n -> b:nat_mod n -> c:nat_mod n ->
  Lemma (fmul_mont n d (fmul_mont n d a b) c == fmul_mont n d a (fmul_mont n d b c))
let lemma_fmul_assoc_mont n d a b c =
  calc (==) {
    fmul_mont n d (fmul_mont n d a b) c;
    (==) { }
    (a * b * d % n) * c * d % n;
    (==) { Math.Lemmas.paren_mul_right (a * b * d % n) c d }
    (a * b * d % n) * (c * d) % n;
    (==) { M.lemma_mod_mul_distr3 1 (a * b * d) (c * d) n }
    a * b * d * (c * d) % n;
    (==) { Math.Lemmas.paren_mul_right (a * b * d) c d }
    a * b * d * c * d % n;
    (==) { Math.Lemmas.paren_mul_right a b d; Math.Lemmas.paren_mul_right a (b * d) c }
    a * (b * d * c) * d % n;
    (==) { Math.Lemmas.paren_mul_right b d c; Math.Lemmas.paren_mul_right b c d }
    a * (b * c * d) * d % n;
    (==) { M.lemma_mod_mul_distr3 a (b * c * d) d n }
    fmul_mont n d a (fmul_mont n d b c);
    }


val lemma_fmul_comm_mont: n:pos -> d:int -> a:nat_mod n -> b:nat_mod n ->
  Lemma (fmul_mont n d a b == fmul_mont n d a b)
let lemma_fmul_comm_mont n d a b = ()

let mk_nat_mont_group (n:pos) (r:nat) (d:int{r * d % n = 1}) : LE.exp (nat_mod n) = {
  LE.one = oneM n r;
  LE.fmul = fmul_mont n d;
  LE.lemma_one = lemma_one_mont n r d;
  LE.lemma_fmul_assoc = lemma_fmul_assoc_mont n d;
  LE.lemma_fmul_comm = lemma_fmul_comm_mont n d;
  }


val pow_nat_mont_is_pow: n:pos -> r:nat -> d:int{r * d % n = 1} -> aM:nat_mod n -> b:pos ->
  Lemma (pow aM b * oneM n r * pow d b % n == LE.pow (mk_nat_mont_group n r d) aM b)

let rec pow_nat_mont_is_pow n r d aM b =
  let k = mk_nat_mont_group n r d in
  if b = 1 then begin
    calc (==) {
      pow aM b * oneM n r * pow d b % n;
      (==) { lemma_pow1 aM; lemma_pow1 d }
      aM * oneM n r * d % n;
      (==) { M.lemma_mod_mul_distr3 aM r d n }
      aM * r * d % n;
      (==) { Math.Lemmas.paren_mul_right aM r d; Math.Lemmas.lemma_mod_mul_distr_r aM (r * d) n }
      aM % n;
      (==) { Math.Lemmas.small_mod aM n }
      aM;
      (==) { LE.lemma_pow1 k aM }
      LE.pow k aM b;
      }; () end
  else begin
    calc (==) {
      pow aM b * oneM n r * pow d b % n;
      (==) { lemma_pow_unfold aM b; lemma_pow_unfold d b }
      aM * pow aM (b - 1) * oneM n r * (d * pow d (b - 1)) % n;
      (==) { Math.Lemmas.paren_mul_right aM (pow aM (b - 1)) (oneM n r) }
      aM * (pow aM (b - 1) * oneM n r) * (d * pow d (b - 1)) % n;
      (==) { Math.Lemmas.paren_mul_right (aM * (pow aM (b - 1) * oneM n r)) (pow d (b - 1)) d }
      (aM * (pow aM (b - 1) * oneM n r) * pow d (b - 1)) * d % n;
      (==) { Math.Lemmas.paren_mul_right aM (pow aM (b - 1) * oneM n r) (pow d (b - 1)) }
      aM * (pow aM (b - 1) * oneM n r * pow d (b - 1)) * d % n;
      (==) { M.lemma_mod_mul_distr3 aM (pow aM (b - 1) * oneM n r * pow d (b - 1)) d n }
      aM * (pow aM (b - 1) * oneM n r * pow d (b - 1) % n) * d % n;
      (==) { pow_nat_mont_is_pow n r d aM (b - 1) }
      aM * (LE.pow k aM (b - 1)) * d % n;
      (==) { LE.lemma_pow_unfold k aM b }
      LE.pow k aM b;
      }; () end


val mont_mod_exp: n:pos -> r:pos -> d:int{r * d % n == 1} -> a:nat_mod n -> b:pos -> nat_mod n
let mont_mod_exp n r d a b =
  let aM = a * r % n in
  let accM = LE.pow (mk_nat_mont_group n r d) aM b in
  let acc = accM * d % n in
  acc


val mont_mod_exp_lemma_before_to_mont: n:pos -> r:pos -> d:int{r * d % n == 1} -> a:nat_mod n -> b:pos ->
  Lemma (pow (a * r % n) b * oneM n r * pow d b % n == pow a b * oneM n r % n)

let mont_mod_exp_lemma_before_to_mont n r d a b =
  let aM = a * r % n in
  let accM0 = oneM n r in
  calc (==) {
    pow aM b * accM0 * pow d b % n;
    (==) { Math.Lemmas.paren_mul_right (pow aM b) accM0 (pow d b);
      Math.Lemmas.paren_mul_right (pow aM b) (pow d b) accM0 }
    pow aM b * pow d b * accM0 % n;
    (==) { lemma_pow_mul_base aM d b }
    pow (aM * d) b * accM0 % n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (pow (aM * d) b) accM0 n }
    pow (aM * d) b % n * accM0 % n;
    (==) { lemma_pow_mod_base (aM * d) b n }
    pow (aM * d % n) b % n * accM0 % n;
    (==) { M.lemma_mont_id n r d a }
    pow (a % n) b % n * accM0 % n;
    (==) { lemma_pow_mod_base a b n }
    pow a b % n * accM0 % n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (pow a b) accM0 n }
    pow a b * accM0 % n;
  };
  assert (pow aM b * accM0 * pow d b % n == pow a b * accM0 % n)


val mont_mod_exp_lemma_after_to_mont: n:pos -> r:pos -> d:int{r * d % n == 1} -> a:nat_mod n -> b:pos ->
  Lemma (pow a b * oneM n r % n * d % n == pow a b % n)

let mont_mod_exp_lemma_after_to_mont n r d a b =
  let accM0 = oneM n r in
  calc (==) {
    pow a b * accM0 % n * d % n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (pow a b * accM0) d n }
    pow a b * accM0 * d % n;
    (==) { Math.Lemmas.paren_mul_right (pow a b) accM0 d }
    pow a b * (accM0 * d) % n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r (pow a b) (accM0 * d) n }
    pow a b * (accM0 * d % n) % n;
    (==) { M.lemma_mont_id n r d 1 }
    pow a b * (1 % n) % n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r (pow a b) 1 n }
    pow a b % n;
  }


val mont_mod_exp_lemma: n:pos -> r:pos -> d:int{r * d % n == 1} -> a:nat_mod n -> b:pos ->
  Lemma (mont_mod_exp n r d a b == pow a b % n)

let mont_mod_exp_lemma n r d a b =
  let k = mk_nat_mont_group n r d in
  let aM = a * r % n in
  calc (==) {
    LE.pow k aM b * d % n;
    (==) { pow_nat_mont_is_pow n r d aM b }
    pow aM b * oneM n r * pow d b % n * d % n;
    (==) { mont_mod_exp_lemma_before_to_mont n r d a b }
    pow a b * oneM n r % n * d % n;
    (==) { mont_mod_exp_lemma_after_to_mont n r d a b }
    pow a b % n;
    }


///  A righ-to-left binary method with Montgomery arithmetic
///  using functions defined in Hacl.Spec.Montgomery.Lemmas

val mod_exp_mont_f_ll:
    pbits:pos -> rLen:nat
  -> n:pos -> mu:nat
  -> bBits:nat -> b:nat{b < pow2 bBits}
  -> i:nat{i < bBits} -> tuple2 nat nat ->
  tuple2 nat nat

let mod_exp_mont_f_ll pbits rLen n mu bBits b i (aM, accM) =
  let accM = if (b / pow2 i % 2 = 1) then M.mont_mul pbits rLen n mu accM aM else accM in
  let aM = M.mont_mul pbits rLen n mu aM aM in
  (aM, accM)


val mod_exp_mont_ll:
    pbits:pos -> rLen:nat
  -> n:pos -> mu:nat
  -> a:nat -> bBits:nat -> b:pos{b < pow2 bBits} ->
  nat

let mod_exp_mont_ll pbits rLen n mu a bBits b =
  let aM = M.to_mont pbits rLen n mu a in
  let accM = M.to_mont pbits rLen n mu 1 in
  let (aM, accM) = Loops.repeati bBits (mod_exp_mont_f_ll pbits rLen n mu bBits b) (aM, accM) in
  M.from_mont pbits rLen n mu accM


val mod_exp_mont_ll_lemma_loop:
    pbits:pos -> rLen:nat
  -> n:pos -> d:int -> mu:nat
  -> bBits:nat -> b:pos{b < pow2 bBits}
  -> i:nat{i <= bBits}
  -> aM0:nat_mod n -> accM0:nat_mod n -> Lemma
  (requires
    (1 + n * mu) % pow2 pbits == 0 /\
    pow2 (pbits * rLen) * d % n == 1 /\
    n < pow2 (pbits * rLen))
  (ensures
    (let r = pow2 (pbits * rLen) in
     let k = mk_nat_mont_group n r d in
     let aM1, accM1 = Loops.repeati i (mod_exp_mont_f_ll pbits rLen n mu bBits b) (aM0, accM0) in
     let aM2, accM2 = Loops.repeati i (LE.exp_rl_f k bBits b) (aM0, accM0) in
     aM1 == aM2 /\ accM1 == accM2))

let rec mod_exp_mont_ll_lemma_loop pbits rLen n d mu bBits b i aM0 accM0 =
  let r = pow2 (pbits * rLen) in
  let k = mk_nat_mont_group n r d in
  let aM1, accM1 = Loops.repeati i (mod_exp_mont_f_ll pbits rLen n mu bBits b) (aM0, accM0) in
  let aM2, accM2 = Loops.repeati i (LE.exp_rl_f k bBits b) (aM0, accM0) in

  if i = 0 then begin
    Loops.eq_repeati0 i (mod_exp_mont_f_ll pbits rLen n mu bBits b) (aM0, accM0);
    Loops.eq_repeati0 i (LE.exp_rl_f k bBits b) (aM0, accM0);
    () end
  else begin
    let aM3, accM3 = Loops.repeati (i - 1) (mod_exp_mont_f_ll pbits rLen n mu bBits b) (aM0, accM0) in
    let aM4, accM4 = Loops.repeati (i - 1) (LE.exp_rl_f k bBits b) (aM0, accM0) in
    Loops.unfold_repeati i (mod_exp_mont_f_ll pbits rLen n mu bBits b) (aM0, accM0) (i - 1);
    Loops.unfold_repeati i (LE.exp_rl_f k bBits b) (aM0, accM0) (i - 1);
    mod_exp_mont_ll_lemma_loop pbits rLen n d mu bBits b (i - 1) aM0 accM0;
    assert (aM3 == aM4 /\ accM3 == accM4);
    Math.Lemmas.lemma_mult_lt_sqr aM3 aM3 n;
    M.mont_reduction_lemma pbits rLen n d mu (aM3 * aM3);

    Math.Lemmas.lemma_mult_lt_sqr accM3 aM3 n;
    M.mont_reduction_lemma pbits rLen n d mu (accM3 * aM3);
    () end


val mod_exp_mont_ll_lemma_eval:
    pbits:pos -> rLen:nat
  -> n:pos -> d:int -> mu:nat
  -> a:nat_mod n
  -> bBits:nat -> b:pos{b < pow2 bBits} -> Lemma
  (requires
    (1 + n * mu) % pow2 pbits == 0 /\
    pow2 (pbits * rLen) * d % n == 1 /\
    1 < n /\ n < pow2 (pbits * rLen))
  (ensures mod_exp_mont_ll pbits rLen n mu a bBits b == pow a b % n)

let mod_exp_mont_ll_lemma_eval pbits rLen n d mu a bBits b =
  let r = pow2 (pbits * rLen) in
  let k = mk_nat_mont_group n r d in

  let aM0 = M.to_mont pbits rLen n mu a in
  let accM0 = M.to_mont pbits rLen n mu 1 in
  M.to_mont_lemma pbits rLen n d mu a;
  M.to_mont_lemma pbits rLen n d mu 1;
  assert (aM0 == a * r % n);
  assert (accM0 == 1 * r % n);

  let (aM1, accM1) = Loops.repeati bBits (mod_exp_mont_f_ll pbits rLen n mu bBits b) (aM0, accM0) in
  mod_exp_mont_ll_lemma_loop pbits rLen n d mu bBits b bBits aM0 accM0;
  LE.exp_rl_lemma k aM0 bBits b;
  assert (accM1 == LE.pow k aM0 b);

  let res = M.from_mont pbits rLen n mu accM1 in
  M.from_mont_lemma pbits rLen n d mu accM1;
  assert (res == accM1 * d % n);

  calc (==) {
    LE.pow k aM0 b * d % n;
    (==) { pow_nat_mont_is_pow n r d aM0 b }
    pow aM0 b * oneM n r * pow d b % n * d % n;
    (==) { mont_mod_exp_lemma_before_to_mont n r d a b }
    pow a b * oneM n r % n * d % n;
    (==) { mont_mod_exp_lemma_after_to_mont n r d a b }
    pow a b % n;
    }


val mod_exp_mont_ll_lemma:
    pbits:pos -> rLen:nat
  -> n:pos -> d:int -> mu:nat
  -> a:nat_mod n
  -> bBits:nat -> b:pos{b < pow2 bBits} -> Lemma
  (requires
    (1 + n * mu) % pow2 pbits == 0 /\
    pow2 (pbits * rLen) * d % n == 1 /\
    1 < n /\ n < pow2 (pbits * rLen))
  (ensures mod_exp_mont_ll pbits rLen n mu a bBits b == pow_mod #n a b)

let mod_exp_mont_ll_lemma pbits rLen n d mu a bBits b =
  mod_exp_mont_ll_lemma_eval pbits rLen n d mu a bBits b;
  lemma_pow_mod #n a b


///  Montgomery ladder for exponentiation with Montgomery arithmetic and
///  conditional swap using functions defined in Hacl.Spec.Montgomery.Lemmas

val mod_exp_mont_ladder_swap_f_ll:
    pbits:pos -> rLen:nat
  -> n:pos -> mu:nat
  -> bBits:nat -> b:nat{b < pow2 bBits}
  -> i:nat{i < bBits} -> tuple3 nat nat nat ->
  tuple3 nat nat nat

let mod_exp_mont_ladder_swap_f_ll pbits rLen n mu bBits b i (rM0, rM1, privbit) =
  let bit = b / pow2 (bBits - i - 1) % 2 in
  let sw = (bit + privbit) % 2 in
  let rM0, rM1 = LE.cswap sw rM0 rM1 in
  let rM0, rM1 = (M.mont_mul pbits rLen n mu rM0 rM0, M.mont_mul pbits rLen n mu rM1 rM0) in
  (rM0, rM1, bit)


val mod_exp_mont_ladder_swap_ll:
    pbits:pos -> rLen:nat
  -> n:pos -> mu:nat
  -> a:nat -> bBits:nat -> b:nat{b < pow2 bBits} ->
  nat

let mod_exp_mont_ladder_swap_ll pbits rLen n mu a bBits b =
  let rM0 = M.to_mont pbits rLen n mu 1 in
  let rM1 = M.to_mont pbits rLen n mu a in
  let sw = 0 in
  let (rM0', rM1', sw') = Loops.repeati bBits (mod_exp_mont_ladder_swap_f_ll pbits rLen n mu bBits b) (rM0, rM1, sw) in
  let rM0', rM1' = LE.cswap sw' rM0' rM1' in
  M.from_mont pbits rLen n mu rM0'


val mod_exp_mont_lader_swap_ll_lemma_loop:
    pbits:pos -> rLen:nat
  -> n:pos -> d:int -> mu:nat
  -> bBits:nat -> b:pos{b < pow2 bBits}
  -> i:nat{i <= bBits}
  -> rM0:nat_mod n -> rM1:nat_mod n -> sw0:nat -> Lemma
  (requires
    (1 + n * mu) % pow2 pbits == 0 /\
    pow2 (pbits * rLen) * d % n == 1 /\
    n < pow2 (pbits * rLen) /\
    sw0 == b / pow2 bBits % 2)
  (ensures
    (let r = pow2 (pbits * rLen) in
     let k = mk_nat_mont_group n r d in
     let (rM0', rM1', sw') = Loops.repeati i (mod_exp_mont_ladder_swap_f_ll pbits rLen n mu bBits b) (rM0, rM1, sw0) in
     let (rM0'', rM1'', sw'') = Loops.repeati i (LE.exp_mont_ladder_swap_f k bBits b) (rM0, rM1, sw0) in
     rM0' == rM0'' /\ rM1' == rM1'' /\ sw' == sw''))

let rec mod_exp_mont_lader_swap_ll_lemma_loop pbits rLen n d mu bBits b i rM0 rM1 sw0 =
  let r = pow2 (pbits * rLen) in
  let k = mk_nat_mont_group n r d in
  let (rM0', rM1', sw') = Loops.repeati i (mod_exp_mont_ladder_swap_f_ll pbits rLen n mu bBits b) (rM0, rM1, sw0) in
  let (rM0'', rM1'', sw'') = Loops.repeati i (LE.exp_mont_ladder_swap_f k bBits b) (rM0, rM1, sw0) in

  if i = 0 then begin
    Loops.eq_repeati0 i (mod_exp_mont_ladder_swap_f_ll pbits rLen n mu bBits b) (rM0, rM1, sw0);
    Loops.eq_repeati0 i (LE.exp_mont_ladder_swap_f k bBits b) (rM0, rM1, sw0);
    () end
  else begin
    let (rM2, rM3, sw1) = Loops.repeati (i - 1) (mod_exp_mont_ladder_swap_f_ll pbits rLen n mu bBits b) (rM0, rM1, sw0) in
    let (rM2', rM3', sw1') = Loops.repeati (i - 1) (LE.exp_mont_ladder_swap_f k bBits b) (rM0, rM1, sw0) in
    Loops.unfold_repeati i (mod_exp_mont_ladder_swap_f_ll pbits rLen n mu bBits b) (rM0, rM1, sw0) (i - 1);
    Loops.unfold_repeati i (LE.exp_mont_ladder_swap_f k bBits b) (rM0, rM1, sw0) (i - 1);
    mod_exp_mont_lader_swap_ll_lemma_loop pbits rLen n d mu bBits b (i - 1) rM0 rM1 sw0;
    assert (rM2 == rM2' /\ rM3 == rM3' /\ sw1 == sw1');

    let bit = b / pow2 (bBits - i) % 2 in
    let sw = (bit + sw1) % 2 in
    let rM2, rM3 = LE.cswap sw rM2 rM3 in

    Math.Lemmas.lemma_mult_lt_sqr rM2 rM2 n;
    M.mont_reduction_lemma pbits rLen n d mu (rM2 * rM2);

    Math.Lemmas.lemma_mult_lt_sqr rM3 rM2 n;
    M.mont_reduction_lemma pbits rLen n d mu (rM3 * rM2);
    () end


val mod_exp_mont_ladder_swap_ll_lemma_eval:
    pbits:pos -> rLen:nat
  -> n:pos -> d:int -> mu:nat
  -> a:nat_mod n
  -> bBits:nat -> b:pos{b < pow2 bBits} -> Lemma
  (requires
    (1 + n * mu) % pow2 pbits == 0 /\
    pow2 (pbits * rLen) * d % n == 1 /\
    1 < n /\ n < pow2 (pbits * rLen))
  (ensures mod_exp_mont_ladder_swap_ll pbits rLen n mu a bBits b == pow a b % n)

let mod_exp_mont_ladder_swap_ll_lemma_eval pbits rLen n d mu a bBits b =
  let r = pow2 (pbits * rLen) in
  let k = mk_nat_mont_group n r d in

  let rM0 = M.to_mont pbits rLen n mu 1 in
  let rM1 = M.to_mont pbits rLen n mu a in
  M.to_mont_lemma pbits rLen n d mu 1;
  M.to_mont_lemma pbits rLen n d mu a;
  assert (rM0 == oneM n r);
  assert (rM1 == a * r % n);

  let sw0 = 0 in
  Math.Lemmas.small_div b (pow2 bBits);
  assert (sw0 == b / pow2 bBits % 2);
  let (rM0', rM1', sw') = Loops.repeati bBits (mod_exp_mont_ladder_swap_f_ll pbits rLen n mu bBits b) (rM0, rM1, sw0) in
  let (rM0'', rM1'', sw'') = Loops.repeati bBits (LE.exp_mont_ladder_swap_f k bBits b) (rM0, rM1, sw0) in
  mod_exp_mont_lader_swap_ll_lemma_loop pbits rLen n d mu bBits b bBits rM0 rM1 sw0;
  assert (rM0' == rM0'' /\ rM1' == rM1'' /\ sw' == sw'');

  let rM0', rM1' = LE.cswap sw' rM0' rM1' in
  LE.exp_mont_ladder_swap_lemma k rM1 bBits b;
  LE.exp_mont_ladder_lemma k rM1 bBits b;
  assert (rM0' == LE.pow k rM1 b);

  let res = M.from_mont pbits rLen n mu rM0' in
  M.from_mont_lemma pbits rLen n d mu rM0';
  assert (res == rM0' * d % n);

  calc (==) {
    LE.pow k rM1 b * d % n;
    (==) { pow_nat_mont_is_pow n r d rM1 b }
    pow rM1 b * oneM n r * pow d b % n * d % n;
    (==) { mont_mod_exp_lemma_before_to_mont n r d a b }
    pow a b * oneM n r % n * d % n;
    (==) { mont_mod_exp_lemma_after_to_mont n r d a b }
    pow a b % n;
    }


val mod_exp_mont_ladder_swap_ll_lemma:
    pbits:pos -> rLen:nat
  -> n:pos -> d:int -> mu:nat
  -> a:nat_mod n
  -> bBits:nat -> b:pos{b < pow2 bBits} -> Lemma
  (requires
    (1 + n * mu) % pow2 pbits == 0 /\
    pow2 (pbits * rLen) * d % n == 1 /\
    1 < n /\ n < pow2 (pbits * rLen))
  (ensures mod_exp_mont_ladder_swap_ll pbits rLen n mu a bBits b == pow_mod #n a b)

let mod_exp_mont_ladder_swap_ll_lemma pbits rLen n d mu a bBits b =
  mod_exp_mont_ladder_swap_ll_lemma_eval pbits rLen n d mu a bBits b;
  lemma_pow_mod #n a b
