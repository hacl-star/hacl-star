module Hacl.Spec.Exponentiation.Lemmas

open FStar.Mul
open Lib.NatMod
open Lib.Sequence

module Loops = Lib.LoopCombinators
module LE = Lib.Exponentiation
module LSeq = Lib.Sequence
module M = Hacl.Spec.Montgomery.Lemmas

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


val mod_exp_mont: n:pos -> r:pos -> d:int{r * d % n == 1} -> a:nat_mod n -> b:pos -> nat_mod n
let mod_exp_mont n r d a b =
  let aM = a * r % n in
  let accM = LE.pow (mk_nat_mont_group n r d) aM b in
  let acc = accM * d % n in
  acc


val mod_exp_mont_lemma_before_to_mont: n:pos -> r:pos -> d:int{r * d % n == 1} -> a:nat_mod n -> b:pos ->
  Lemma (pow (a * r % n) b * oneM n r * pow d b % n == pow a b * oneM n r % n)

let mod_exp_mont_lemma_before_to_mont n r d a b =
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


val mod_exp_mont_lemma_after_to_mont: n:pos -> r:pos -> d:int{r * d % n == 1} -> a:nat_mod n -> b:pos ->
  Lemma (pow a b * oneM n r % n * d % n == pow a b % n)

let mod_exp_mont_lemma_after_to_mont n r d a b =
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


val mod_exp_mont_lemma: n:pos -> r:pos -> d:int{r * d % n == 1} -> a:nat_mod n -> b:pos ->
  Lemma (mod_exp_mont n r d a b == pow a b % n)

let mod_exp_mont_lemma n r d a b =
  let k = mk_nat_mont_group n r d in
  let aM = a * r % n in
  calc (==) {
    LE.pow k aM b * d % n;
    (==) { pow_nat_mont_is_pow n r d aM b }
    pow aM b * oneM n r * pow d b % n * d % n;
    (==) { mod_exp_mont_lemma_before_to_mont n r d a b }
    pow a b * oneM n r % n * d % n;
    (==) { mod_exp_mont_lemma_after_to_mont n r d a b }
    pow a b % n;
    }

(* Modular exponentiation with Montgomery arithmetic
   using functions from Hacl.Spec.Montgomery.Lemmas *)

let mont_pre (pbits:pos) (rLen:nat) (n:pos) (mu:nat) =
  (1 + n * mu) % pow2 pbits == 0 /\
  1 < n /\ n < pow2 (pbits * rLen) /\ n % 2 = 1

val oneM_ll: pbits:pos -> rLen:pos -> n:pos -> mu:nat{mont_pre pbits rLen n mu} -> nat_mod n
let oneM_ll pbits rLen n mu =
  let d, k = M.eea_pow2_odd (pbits * rLen) n in
  M.mont_preconditions_d pbits rLen n;
  M.to_mont_lemma pbits rLen n d mu 1;
  M.to_mont pbits rLen n mu 1

val fmul_mont_ll: pbits:pos -> rLen:nat -> n:pos -> mu:nat{mont_pre pbits rLen n mu}
  -> a:nat_mod n -> b:nat_mod n -> nat_mod n
let fmul_mont_ll pbits rLen n mu a b =
  let d, k = M.eea_pow2_odd (pbits * rLen) n in
  M.mont_preconditions_d pbits rLen n;
  M.mont_mul_lemma pbits rLen n d mu a b;
  M.mont_mul pbits rLen n mu a b


val lemma_one_mont_ll: pbits:pos -> rLen:nat -> n:pos -> mu:nat{mont_pre pbits rLen n mu} -> a:nat_mod n ->
  Lemma (fmul_mont_ll pbits rLen n mu a (oneM_ll pbits rLen n mu) == a)
let lemma_one_mont_ll pbits rLen n mu a =
  let r = pow2 (pbits * rLen) in
  let d, k = M.eea_pow2_odd (pbits * rLen) n in
  M.mont_preconditions_d pbits rLen n;

  let oneM = oneM_ll pbits rLen n mu in
  M.to_mont_lemma pbits rLen n d mu 1;
  assert (oneM == 1 * r % n);
  M.mont_mul_lemma pbits rLen n d mu a oneM;
  lemma_one_mont n r d a


val lemma_fmul_assoc_mont_ll: pbits:pos -> rLen:nat -> n:pos -> mu:nat{mont_pre pbits rLen n mu}
  -> a:nat_mod n -> b:nat_mod n -> c:nat_mod n ->
  Lemma (fmul_mont_ll pbits rLen n mu (fmul_mont_ll pbits rLen n mu a b) c ==
    fmul_mont_ll pbits rLen n mu a (fmul_mont_ll pbits rLen n mu b c))

let lemma_fmul_assoc_mont_ll pbits rLen n mu a b c =
  let r = pow2 (pbits * rLen) in
  let d, k = M.eea_pow2_odd (pbits * rLen) n in
  M.mont_preconditions_d pbits rLen n;

  M.mont_mul_lemma pbits rLen n d mu a b;
  M.mont_mul_lemma pbits rLen n d mu (fmul_mont_ll pbits rLen n mu a b) c;
  M.mont_mul_lemma pbits rLen n d mu b c;
  M.mont_mul_lemma pbits rLen n d mu a (fmul_mont_ll pbits rLen n mu b c);
  lemma_fmul_assoc_mont n d a b c


val lemma_fmul_comm_mont_ll: pbits:pos -> rLen:nat -> n:pos -> mu:nat{mont_pre pbits rLen n mu}
  -> a:nat_mod n -> b:nat_mod n ->
  Lemma (fmul_mont_ll pbits rLen n mu a b == fmul_mont_ll pbits rLen n mu b a)

let lemma_fmul_comm_mont_ll pbits rLen n mu a b =
  let r = pow2 (pbits * rLen) in
  let d, k = M.eea_pow2_odd (pbits * rLen) n in
  M.mont_preconditions_d pbits rLen n;

  M.mont_mul_lemma pbits rLen n d mu a b;
  M.mont_mul_lemma pbits rLen n d mu b a;
  lemma_fmul_comm_mont n d a b


let mk_nat_mont_group_ll (pbits:pos) (rLen:nat) (n:pos) (mu:nat{mont_pre pbits rLen n mu}) : LE.exp (nat_mod n) = {
  LE.one = oneM_ll pbits rLen n mu;
  LE.fmul = fmul_mont_ll pbits rLen n mu;
  LE.lemma_one = lemma_one_mont_ll pbits rLen n mu;
  LE.lemma_fmul_assoc = lemma_fmul_assoc_mont_ll pbits rLen n mu;
  LE.lemma_fmul_comm = lemma_fmul_comm_mont_ll pbits rLen n mu;
  }


val pow_nat_mont_ll_is_pow_nat_mont:
    pbits:pos -> rLen:pos
  -> n:pos -> mu:nat
  -> a:nat_mod n -> b:nat -> Lemma
  (requires mont_pre pbits rLen n mu)
  (ensures
   (let r = pow2 (pbits * rLen) in
    let d, k = M.eea_pow2_odd (pbits * rLen) n in
    M.mont_preconditions_d pbits rLen n;

    LE.pow (mk_nat_mont_group n r d) a b ==
    LE.pow (mk_nat_mont_group_ll pbits rLen n mu) a b))

let rec pow_nat_mont_ll_is_pow_nat_mont pbits rLen n mu a b =
  let r = pow2 (pbits * rLen) in
  let d, k = M.eea_pow2_odd (pbits * rLen) n in
  M.mont_preconditions_d pbits rLen n;

  let k0 = mk_nat_mont_group n r d in
  let k1 = mk_nat_mont_group_ll pbits rLen n mu in

  if b = 0 then begin
    LE.lemma_pow0 k0 a;
    LE.lemma_pow0 k1 a;
    M.to_mont_lemma pbits rLen n d mu 1 end
  else begin
    LE.lemma_pow_unfold k0 a b;
    LE.lemma_pow_unfold k1 a b;
    //assert (LE.pow k1 a b == k1.LE.fmul a (LE.pow k1 a (b - 1)));
    M.mont_mul_lemma pbits rLen n d mu a (LE.pow k1 a (b - 1));
    pow_nat_mont_ll_is_pow_nat_mont pbits rLen n mu a (b - 1);
    () end


val mod_exp_mont_ll: pbits:pos -> rLen:pos -> n:pos -> mu:nat{mont_pre pbits rLen n mu}
  -> a:nat_mod n -> b:pos -> nat_mod n

let mod_exp_mont_ll pbits rLen n mu a b =
  let d, k = M.eea_pow2_odd (pbits * rLen) n in
  M.mont_preconditions_d pbits rLen n;

  let aM = M.to_mont pbits rLen n mu a in
  M.to_mont_lemma pbits rLen n d mu a;
  let accM = LE.pow (mk_nat_mont_group_ll pbits rLen n mu) aM b in
  let acc = M.from_mont pbits rLen n mu accM in
  M.from_mont_lemma pbits rLen n d mu accM;
  acc


val mod_exp_mont_ll_lemma: pbits:pos -> rLen:pos -> n:pos -> mu:nat{mont_pre pbits rLen n mu}
  -> a:nat_mod n -> b:pos ->
  Lemma (mod_exp_mont_ll pbits rLen n mu a b == pow a b % n)

let mod_exp_mont_ll_lemma pbits rLen n mu a b =
  let r = pow2 (pbits * rLen) in
  let d, k = M.eea_pow2_odd (pbits * rLen) n in
  M.mont_preconditions_d pbits rLen n;

  let k1 = mk_nat_mont_group_ll pbits rLen n mu in
  let k2 = mk_nat_mont_group n r d in

  let aM = M.to_mont pbits rLen n mu a in
  M.to_mont_lemma pbits rLen n d mu a;
  assert (aM == a * r % n);

  let accM = LE.pow k1 aM b in
  pow_nat_mont_ll_is_pow_nat_mont pbits rLen n mu aM b;
  assert (accM == LE.pow k2 aM b);

  let acc = M.from_mont pbits rLen n mu accM in
  M.from_mont_lemma pbits rLen n d mu accM;
  assert (acc == accM * d % n);
  mod_exp_mont_lemma n r d a b


///  A righ-to-left binary method with Montgomery arithmetic
///  using functions defined in Hacl.Spec.Montgomery.Lemmas

val mod_exp_rl_mont_f:
    pbits:pos -> rLen:nat
  -> n:pos -> mu:nat
  -> bBits:nat -> b:nat{b < pow2 bBits}
  -> i:nat{i < bBits} -> tuple2 nat nat ->
  tuple2 nat nat

let mod_exp_rl_mont_f pbits rLen n mu bBits b i (aM, accM) =
  let accM = if (b / pow2 i % 2 = 1) then M.mont_mul pbits rLen n mu accM aM else accM in
  let aM = M.mont_mul pbits rLen n mu aM aM in
  (aM, accM)


val mod_exp_rl_mont:
    pbits:pos -> rLen:nat
  -> n:pos -> mu:nat
  -> a:nat -> bBits:nat -> b:pos{b < pow2 bBits} ->
  nat

let mod_exp_rl_mont pbits rLen n mu a bBits b =
  let aM = M.to_mont pbits rLen n mu a in
  let accM = M.to_mont pbits rLen n mu 1 in
  let (aM, accM) = Loops.repeati bBits (mod_exp_rl_mont_f pbits rLen n mu bBits b) (aM, accM) in
  M.from_mont pbits rLen n mu accM


val mod_exp_rl_mont_lemma_loop:
    pbits:pos -> rLen:nat
  -> n:pos -> mu:nat
  -> bBits:nat -> b:pos{b < pow2 bBits}
  -> i:nat{i <= bBits}
  -> aM0:nat_mod n -> accM0:nat_mod n -> Lemma
  (requires mont_pre pbits rLen n mu)
  (ensures
   (let k = mk_nat_mont_group_ll pbits rLen n mu in
    let aM1, accM1 = Loops.repeati i (mod_exp_rl_mont_f pbits rLen n mu bBits b) (aM0, accM0) in
    let aM2, accM2 = Loops.repeati i (LE.exp_rl_f k bBits b) (aM0, accM0) in
    aM1 == aM2 /\ accM1 == accM2))

let rec mod_exp_rl_mont_lemma_loop pbits rLen n mu bBits b i aM0 accM0 =
  let k = mk_nat_mont_group_ll pbits rLen n mu in

  if i = 0 then begin
    Loops.eq_repeati0 i (mod_exp_rl_mont_f pbits rLen n mu bBits b) (aM0, accM0);
    Loops.eq_repeati0 i (LE.exp_rl_f k bBits b) (aM0, accM0) end
  else begin
    Loops.unfold_repeati i (mod_exp_rl_mont_f pbits rLen n mu bBits b) (aM0, accM0) (i - 1);
    Loops.unfold_repeati i (LE.exp_rl_f k bBits b) (aM0, accM0) (i - 1);
    mod_exp_rl_mont_lemma_loop pbits rLen n mu bBits b (i - 1) aM0 accM0 end


val mod_exp_rl_mont_lemma:
    pbits:pos -> rLen:nat
  -> n:pos -> mu:nat
  -> a:nat_mod n
  -> bBits:nat -> b:pos{b < pow2 bBits} -> Lemma
  (requires mont_pre pbits rLen n mu)
  (ensures  mod_exp_rl_mont pbits rLen n mu a bBits b == pow_mod #n a b)

let mod_exp_rl_mont_lemma pbits rLen n mu a bBits b =
  let r = pow2 (pbits * rLen) in
  let d, k = M.eea_pow2_odd (pbits * rLen) n in
  M.mont_preconditions_d pbits rLen n;
  let k1 = mk_nat_mont_group_ll pbits rLen n mu in

  let aM0 = M.to_mont pbits rLen n mu a in
  let accM0 = M.to_mont pbits rLen n mu 1 in
  M.to_mont_lemma pbits rLen n d mu a;
  M.to_mont_lemma pbits rLen n d mu 1;
  assert (aM0 == a * r % n);
  assert (accM0 == 1 * r % n);

  let (aM1, accM1) = Loops.repeati bBits (mod_exp_rl_mont_f pbits rLen n mu bBits b) (aM0, accM0) in
  mod_exp_rl_mont_lemma_loop pbits rLen n mu bBits b bBits aM0 accM0;
  LE.exp_rl_lemma k1 aM0 bBits b;
  assert (accM1 == LE.pow k1 aM0 b);
  let res = M.from_mont pbits rLen n mu accM1 in
  M.from_mont_lemma pbits rLen n d mu accM1;
  mod_exp_mont_ll_lemma pbits rLen n mu a b;
  assert (res == pow a b % n);
  lemma_pow_mod #n a b


///  Montgomery ladder for exponentiation with Montgomery arithmetic and
///  conditional swap using functions defined in Hacl.Spec.Montgomery.Lemmas

val mod_exp_mont_ladder_swap_f:
    pbits:pos -> rLen:nat
  -> n:pos -> mu:nat
  -> bBits:nat -> b:nat{b < pow2 bBits}
  -> i:nat{i < bBits} -> tuple3 nat nat nat ->
  tuple3 nat nat nat

let mod_exp_mont_ladder_swap_f pbits rLen n mu bBits b i (rM0, rM1, privbit) =
  let bit = b / pow2 (bBits - i - 1) % 2 in
  let sw = (bit + privbit) % 2 in
  let rM0, rM1 = LE.cswap sw rM0 rM1 in
  let rM0, rM1 = (M.mont_mul pbits rLen n mu rM0 rM0, M.mont_mul pbits rLen n mu rM1 rM0) in
  (rM0, rM1, bit)


val mod_exp_mont_ladder_swap:
    pbits:pos -> rLen:nat
  -> n:pos -> mu:nat
  -> a:nat -> bBits:nat -> b:nat{b < pow2 bBits} ->
  nat

let mod_exp_mont_ladder_swap pbits rLen n mu a bBits b =
  let rM0 = M.to_mont pbits rLen n mu 1 in
  let rM1 = M.to_mont pbits rLen n mu a in
  let sw = 0 in
  let (rM0', rM1', sw') =
    Loops.repeati bBits (mod_exp_mont_ladder_swap_f pbits rLen n mu bBits b) (rM0, rM1, sw) in
  let rM0', rM1' = LE.cswap sw' rM0' rM1' in
  M.from_mont pbits rLen n mu rM0'


val mod_exp_mont_lader_swap_lemma_loop:
    pbits:pos -> rLen:nat
  -> n:pos -> mu:nat
  -> bBits:nat -> b:pos{b < pow2 bBits}
  -> i:nat{i <= bBits}
  -> rM0:nat_mod n -> rM1:nat_mod n -> sw0:nat -> Lemma
  (requires
    mont_pre pbits rLen n mu /\
    sw0 == b / pow2 bBits % 2)
  (ensures
    (let k = mk_nat_mont_group_ll pbits rLen n mu in
     let (rM0', rM1', sw') = Loops.repeati i
       (mod_exp_mont_ladder_swap_f pbits rLen n mu bBits b) (rM0, rM1, sw0) in
     let (rM0'', rM1'', sw'') = Loops.repeati i (LE.exp_mont_ladder_swap_f k bBits b) (rM0, rM1, sw0) in
     rM0' == rM0'' /\ rM1' == rM1'' /\ sw' == sw''))

let rec mod_exp_mont_lader_swap_lemma_loop pbits rLen n mu bBits b i rM0 rM1 sw0 =
  let k = mk_nat_mont_group_ll pbits rLen n mu in

  if i = 0 then begin
    Loops.eq_repeati0 i (mod_exp_mont_ladder_swap_f pbits rLen n mu bBits b) (rM0, rM1, sw0);
    Loops.eq_repeati0 i (LE.exp_mont_ladder_swap_f k bBits b) (rM0, rM1, sw0) end
  else begin
    Loops.unfold_repeati i (mod_exp_mont_ladder_swap_f pbits rLen n mu bBits b) (rM0, rM1, sw0) (i - 1);
    Loops.unfold_repeati i (LE.exp_mont_ladder_swap_f k bBits b) (rM0, rM1, sw0) (i - 1);
    mod_exp_mont_lader_swap_lemma_loop pbits rLen n mu bBits b (i - 1) rM0 rM1 sw0 end


val mod_exp_mont_ladder_swap_lemma:
    pbits:pos -> rLen:nat
  -> n:pos -> mu:nat
  -> a:nat_mod n
  -> bBits:nat -> b:pos{b < pow2 bBits} -> Lemma
  (requires mont_pre pbits rLen n mu)
  (ensures  mod_exp_mont_ladder_swap pbits rLen n mu a bBits b == pow_mod #n a b)

let mod_exp_mont_ladder_swap_lemma pbits rLen n mu a bBits b =
  let r = pow2 (pbits * rLen) in
  let d, k = M.eea_pow2_odd (pbits * rLen) n in
  M.mont_preconditions_d pbits rLen n;
  let k1 = mk_nat_mont_group_ll pbits rLen n mu in

  let rM0 = M.to_mont pbits rLen n mu 1 in
  let rM1 = M.to_mont pbits rLen n mu a in
  M.to_mont_lemma pbits rLen n d mu 1;
  M.to_mont_lemma pbits rLen n d mu a;
  assert (rM0 == oneM n r);
  assert (rM1 == a * r % n);

  let sw0 = 0 in
  Math.Lemmas.small_div b (pow2 bBits);
  assert (sw0 == b / pow2 bBits % 2);

  let (rM0', rM1', sw') = Loops.repeati bBits (mod_exp_mont_ladder_swap_f pbits rLen n mu bBits b) (rM0, rM1, sw0) in
  let (rM0'', rM1'', sw'') = Loops.repeati bBits (LE.exp_mont_ladder_swap_f k1 bBits b) (rM0, rM1, sw0) in
  mod_exp_mont_lader_swap_lemma_loop pbits rLen n mu bBits b bBits rM0 rM1 sw0;
  assert (rM0' == rM0'' /\ rM1' == rM1'' /\ sw' == sw'');

  let rM0', rM1' = LE.cswap sw' rM0' rM1' in
  LE.exp_mont_ladder_swap_lemma k1 rM1 bBits b;
  LE.exp_mont_ladder_lemma k1 rM1 bBits b;
  assert (rM0' == LE.pow k1 rM1 b);

  let res = M.from_mont pbits rLen n mu rM0' in
  M.from_mont_lemma pbits rLen n d mu rM0';
  mod_exp_mont_ll_lemma pbits rLen n mu a b;
  assert (res == pow a b % n);
  lemma_pow_mod #n a b

///  Fixed window exponentiation with a precomputed table and Montgomery arithmetic
///  using functions defined in Hacl.Spec.Montgomery.Lemmas

// res == pow acc (pow2 b)
val mod_exp_pow2_mont: pbits:pos -> rLen:nat -> n:pos -> mu:nat -> a:nat -> b:nat -> nat
let mod_exp_pow2_mont pbits rLen n mu a b =
  Loops.repeat b (M.mont_sqr pbits rLen n mu) a


val mod_precomp_table_mont_f:
    pbits:pos -> rLen:nat
  -> n:pos -> mu:nat
  -> a:nat
  -> table_len:Lib.IntTypes.size_nat{1 < table_len}
  -> i:nat{i < table_len - 2}
  -> table:lseq nat table_len ->
  lseq nat table_len

let mod_precomp_table_mont_f pbits rLen n mu a table_len i table =
  table.[i + 2] <- M.mont_mul pbits rLen n mu table.[i + 1] a

// table_len = pow2 l
// table.[i] == pow a i
val mod_precomp_table_mont:
    pbits:pos -> rLen:nat
  -> n:pos -> mu:nat
  -> table_len:Lib.IntTypes.size_nat{1 < table_len}
  -> a:nat ->
  lseq nat table_len

let mod_precomp_table_mont pbits rLen n mu table_len a =
  let table = create table_len 0 in
  let table = table.[0] <- M.to_mont pbits rLen n mu 1 in
  let table = table.[1] <- a in

  Loops.repeati (table_len - 2) (mod_precomp_table_mont_f pbits rLen n mu a table_len) table


val mod_exp_fw_mont_f:
    pbits:pos -> rLen:nat
  -> n:pos -> mu:nat
  -> bBits:nat -> b:nat{b < pow2 bBits}
  -> l:pos
  -> table_len:Lib.IntTypes.size_nat{1 < table_len /\ table_len == pow2 l}
  -> table:lseq nat table_len
  -> i:nat{l * (i + 1) <= bBits} -> acc:nat ->
  nat

let mod_exp_fw_mont_f pbits rLen n mu bBits b l table_len table i acc =
  let bits_l = b / pow2 (bBits - l * i - l) % table_len in
  let acc_pow2l = mod_exp_pow2_mont pbits rLen n mu acc l in // pow k acc (pow2 l)
  let a_powbits_l = table.[bits_l] in //select_table // pow k a bits_l
  M.mont_mul pbits rLen n mu acc_pow2l a_powbits_l


val mod_exp_fw_mont_rem:
    pbits:pos -> rLen:nat
  -> n:pos -> mu:nat
  -> bBits:nat -> b:nat{b < pow2 bBits}
  -> l:pos
  -> table_len:Lib.IntTypes.size_nat{1 < table_len /\ table_len == pow2 l}
  -> table:lseq nat table_len -> accM:nat ->
  nat

let mod_exp_fw_mont_rem pbits rLen n mu bBits b l table_len table accM =
  let c = bBits % l in
  let bits_c = b % pow2 c in
  let acc_pow2c = mod_exp_pow2_mont pbits rLen n mu accM c in // pow k acc (pow2 c)
  Math.Lemmas.pow2_lt_compat l c;
  let a_powbits_c = table.[bits_c] in //select_table // pow k a bits_c
  M.mont_mul pbits rLen n mu acc_pow2c a_powbits_c


val mod_exp_fw_mont_:
    pbits:pos -> rLen:nat
  -> n:pos -> mu:nat
  -> aM:nat
  -> bBits:nat -> b:nat{b < pow2 bBits}
  -> l:pos{pow2 l <= Lib.IntTypes.max_size_t} ->
  nat

let mod_exp_fw_mont_ pbits rLen n mu aM bBits b l =
  let oneM = M.to_mont pbits rLen n mu 1 in
  let table_len = pow2 l in
  Math.Lemmas.pow2_le_compat l 1;
  let table = mod_precomp_table_mont pbits rLen n mu table_len aM in
  let accM = Loops.repeati (bBits / l) (mod_exp_fw_mont_f pbits rLen n mu bBits b l table_len table) oneM in
  if bBits % l = 0 then accM else mod_exp_fw_mont_rem pbits rLen n mu bBits b l table_len table accM


val mod_exp_fw_mont:
    pbits:pos -> rLen:nat
  -> n:pos -> mu:nat
  -> a:nat -> bBits:nat -> b:nat{b < pow2 bBits}
  -> l:pos{pow2 l <= Lib.IntTypes.max_size_t} ->
  nat

let mod_exp_fw_mont pbits rLen n mu a bBits b l =
  let aM = M.to_mont pbits rLen n mu a in
  let resM = mod_exp_fw_mont_ pbits rLen n mu aM bBits b l in
  M.from_mont pbits rLen n mu resM


val mod_exp_pow2_mont_lemma:
    pbits:pos -> rLen:nat
  -> n:pos -> mu:nat
  -> a:nat_mod n
  -> b:nat -> Lemma
  (requires mont_pre pbits rLen n mu)
  (ensures
   (let k = mk_nat_mont_group_ll pbits rLen n mu in
    let r = mod_exp_pow2_mont pbits rLen n mu a b in
    r == LE.exp_pow2 k a b /\ r < n))

let rec mod_exp_pow2_mont_lemma pbits rLen n mu a b =
  let k = mk_nat_mont_group_ll pbits rLen n mu in

  if b = 0 then begin
    Loops.eq_repeat0 (LE.fsqr k) a;
    Loops.eq_repeat0 (M.mont_sqr pbits rLen n mu) a end
  else begin
    Loops.unfold_repeat b (LE.fsqr k) a (b - 1);
    Loops.unfold_repeat b (M.mont_sqr pbits rLen n mu) a (b - 1);
    mod_exp_pow2_mont_lemma pbits rLen n mu a (b - 1) end


val mod_precomp_table_mont_loop_lemma:
    pbits:pos -> rLen:nat
  -> n:pos -> mu:nat
  -> table_len:Lib.IntTypes.size_nat{1 < table_len}
  -> a:nat_mod n
  -> t01:lseq nat table_len
  -> t02:lseq (nat_mod n) table_len
  -> j:nat{j <= table_len - 2} -> Lemma
  (requires
    mont_pre pbits rLen n mu /\
    index t01 0 == index t02 0 /\
    index t01 1 == index t02 1)
  (ensures (let k = mk_nat_mont_group_ll pbits rLen n mu in
    let t1 : lseq nat table_len = Loops.repeati j (mod_precomp_table_mont_f pbits rLen n mu a table_len) t01 in
    let t2 : lseq (nat_mod n) table_len = Loops.repeati j (LE.precomp_table_f k a table_len) t02 in
    (forall (i:nat{i < j + 2}). index t1 i == index t2 i)))

let rec mod_precomp_table_mont_loop_lemma pbits rLen n mu table_len a t01 t02 j =
  let k = mk_nat_mont_group_ll pbits rLen n mu in
  let t1 : lseq nat table_len = Loops.repeati j (mod_precomp_table_mont_f pbits rLen n mu a table_len) t01 in
  let t2 : lseq (nat_mod n) table_len = Loops.repeati j (LE.precomp_table_f k a table_len) t02 in

  if j = 0 then begin
    Loops.eq_repeati0 j (mod_precomp_table_mont_f pbits rLen n mu a table_len) t01;
    Loops.eq_repeati0 j (LE.precomp_table_f k a table_len) t02 end
  else begin
    let t3 : lseq nat table_len = Loops.repeati (j - 1) (mod_precomp_table_mont_f pbits rLen n mu a table_len) t01 in
    let t4 : lseq (nat_mod n) table_len = Loops.repeati (j - 1) (LE.precomp_table_f k a table_len) t02 in

    Loops.unfold_repeati j (mod_precomp_table_mont_f pbits rLen n mu a table_len) t01 (j - 1);
    Loops.unfold_repeati j (LE.precomp_table_f k a table_len) t02 (j - 1);
    mod_precomp_table_mont_loop_lemma pbits rLen n mu table_len a t01 t02 (j - 1);
    assert (forall (i:nat{i < j + 1}). index t3 i == index t4 i);
    assert (forall (i:nat{i < j + 1}). index t1 i == index t2 i);
    assert (index t1 (j + 1) == M.mont_mul pbits rLen n mu t3.[j] a);
    assert (index t2 (j + 1) == k.LE.fmul t4.[j] a);
    assert (M.mont_mul pbits rLen n mu t3.[j] a == k.LE.fmul t4.[j] a);
    assert (forall (i:nat{i < j + 2}). index t1 i == index t2 i);
    () end


val mod_precomp_table_mont_lemma:
    pbits:pos -> rLen:nat
  -> n:pos -> mu:nat
  -> table_len:Lib.IntTypes.size_nat{1 < table_len}
  -> a:nat_mod n
  -> i:nat{i < table_len} -> Lemma
  (requires mont_pre pbits rLen n mu)
  (ensures
   (let k = mk_nat_mont_group_ll pbits rLen n mu in
    let t1 = mod_precomp_table_mont pbits rLen n mu table_len a in
    let t2 = LE.precomp_table k a table_len in
    index t1 i == index t2 i /\ index t1 i < n))

let mod_precomp_table_mont_lemma pbits rLen n mu table_len a i =
  let k = mk_nat_mont_group_ll pbits rLen n mu in

  let res = create table_len 0 in
  let res = res.[0] <- k.LE.one in
  let res = res.[1] <- a in

  let table = create table_len k.LE.one in
  let table = table.[0] <- k.LE.one in
  let table = table.[1] <- a in

  mod_precomp_table_mont_loop_lemma pbits rLen n mu table_len a res table (table_len - 2)


val mod_exp_fw_mont_f_lemma:
    pbits:pos -> rLen:nat
  -> n:pos -> mu:nat
  -> aM:nat_mod n
  -> bBits:nat -> b:nat{b < pow2 bBits}
  -> l:pos
  -> table_len:Lib.IntTypes.size_nat{1 < table_len /\ table_len == pow2 l}
  -> accM:nat_mod n
  -> i:nat{l * (i + 1) <= bBits} -> Lemma
  (requires mont_pre pbits rLen n mu)
  (ensures
   (let k = mk_nat_mont_group_ll pbits rLen n mu in
    let t1 = mod_precomp_table_mont pbits rLen n mu table_len aM in
    let t2 = LE.precomp_table k aM table_len in
    let r = mod_exp_fw_mont_f pbits rLen n mu bBits b l table_len t1 i accM in
    r == LE.exp_fw_f k bBits b l table_len t2 i accM /\ r < n))

let mod_exp_fw_mont_f_lemma pbits rLen n mu aM bBits b l table_len accM i =
  let k = mk_nat_mont_group_ll pbits rLen n mu in
  let t1 = mod_precomp_table_mont pbits rLen n mu table_len aM in
  let t2 = LE.precomp_table k aM table_len in

  let bits_l = b / pow2 (bBits - l * i - l) % table_len in
  mod_precomp_table_mont_lemma pbits rLen n mu table_len aM bits_l;
  assert (index t1 bits_l == index t2 bits_l);
  mod_exp_pow2_mont_lemma pbits rLen n mu accM l


val mod_exp_fw_mont_rem_lemma:
    pbits:pos -> rLen:nat
  -> n:pos -> mu:nat
  -> aM:nat_mod n
  -> bBits:nat -> b:nat{b < pow2 bBits}
  -> l:pos
  -> table_len:Lib.IntTypes.size_nat{1 < table_len /\ table_len == pow2 l}
  -> accM:nat_mod n -> Lemma
  (requires mont_pre pbits rLen n mu)
  (ensures
   (let k = mk_nat_mont_group_ll pbits rLen n mu in
    let t1 = mod_precomp_table_mont pbits rLen n mu table_len aM in
    let t2 = LE.precomp_table k aM table_len in
    let r = mod_exp_fw_mont_rem pbits rLen n mu bBits b l table_len t1 accM in
    r == LE.exp_fw_rem k bBits b l table_len t2 accM /\ r < n))

let mod_exp_fw_mont_rem_lemma pbits rLen n mu aM bBits b l table_len accM =
  let k = mk_nat_mont_group_ll pbits rLen n mu in
  let t1 = mod_precomp_table_mont pbits rLen n mu table_len aM in
  let t2 = LE.precomp_table k aM table_len in

  let c = bBits % l in
  let bits_c = b % pow2 c in
  Math.Lemmas.pow2_lt_compat l c;

  mod_precomp_table_mont_lemma pbits rLen n mu table_len aM bits_c;
  assert (index t1 bits_c == index t2 bits_c);
  mod_exp_pow2_mont_lemma pbits rLen n mu accM c


val mod_exp_fw_mont_loop_lemma:
    pbits:pos -> rLen:nat
  -> n:pos -> mu:nat
  -> aM:nat_mod n
  -> bBits:nat -> b:nat{b < pow2 bBits}
  -> l:pos
  -> table_len:Lib.IntTypes.size_nat{1 < table_len /\ table_len == pow2 l}
  -> accM0:nat_mod n
  -> j:nat{l * j <= bBits } -> Lemma
  (requires mont_pre pbits rLen n mu)
  (ensures
   (let k = mk_nat_mont_group_ll pbits rLen n mu in
    let t1 = mod_precomp_table_mont pbits rLen n mu table_len aM in
    let t2 = LE.precomp_table k aM table_len in

    let accM1 = Loops.repeati j (mod_exp_fw_mont_f pbits rLen n mu bBits b l table_len t1) accM0 in
    let accM2 : nat_mod n = Loops.repeati j (LE.exp_fw_f k bBits b l table_len t2) accM0 in
    accM1 == accM2 /\ accM1 < n))

let rec mod_exp_fw_mont_loop_lemma pbits rLen n mu aM bBits b l table_len accM0 j =
  let k = mk_nat_mont_group_ll pbits rLen n mu in
  let t1 = mod_precomp_table_mont pbits rLen n mu table_len aM in
  let t2 = LE.precomp_table k aM table_len in

  if j = 0 then begin
    Loops.eq_repeati0 j (mod_exp_fw_mont_f pbits rLen n mu bBits b l table_len t1) accM0;
    Loops.eq_repeati0 j (LE.exp_fw_f k bBits b l table_len t2) accM0 end
  else begin
    Math.Lemmas.lemma_mult_lt_left l (j - 1) j;
    let accM4 = Loops.repeati (j - 1) (LE.exp_fw_f k bBits b l table_len t2) accM0 in
    Loops.unfold_repeati j (LE.exp_fw_f k bBits b l table_len t2) accM0 (j - 1);
    Loops.unfold_repeati j (mod_exp_fw_mont_f pbits rLen n mu bBits b l table_len t1) accM0 (j - 1);
    mod_exp_fw_mont_loop_lemma pbits rLen n mu aM bBits b l table_len accM0 (j - 1);
    mod_exp_fw_mont_f_lemma pbits rLen n mu aM bBits b l table_len accM4 (j - 1);
    () end


val mod_exp_fw_mont_aux_lemma:
    pbits:pos -> rLen:pos
  -> n:pos -> mu:nat
  -> aM:nat_mod n
  -> bBits:nat -> b:nat{b < pow2 bBits}
  -> l:pos{pow2 l <= Lib.IntTypes.max_size_t} -> Lemma
  (requires mont_pre pbits rLen n mu)
  (ensures
   (let k = mk_nat_mont_group_ll pbits rLen n mu in
    let r = mod_exp_fw_mont_ pbits rLen n mu aM bBits b l in
    r == LE.exp_fw k aM bBits b l /\ r < n))

let mod_exp_fw_mont_aux_lemma pbits rLen n mu aM bBits b l =
  let r = pow2 (pbits * rLen) in
  let d, k = M.eea_pow2_odd (pbits * rLen) n in
  M.mont_preconditions_d pbits rLen n;
  let k1 = mk_nat_mont_group_ll pbits rLen n mu in

  let oneM = M.to_mont pbits rLen n mu 1 in
  M.to_mont_lemma pbits rLen n d mu 1;
  assert (oneM == 1 * r % n);

  Math.Lemmas.pow2_le_compat l 1;
  let table_len = pow2 l in
  assert (1 < table_len /\ table_len <= Lib.IntTypes.max_size_t);
  let t1 = mod_precomp_table_mont pbits rLen n mu table_len aM in
  let t2 = LE.precomp_table k1 aM table_len in

  //Math.Lemmas.multiply_fractions bBits l;
  let accM : nat = Loops.repeati (bBits / l) (mod_exp_fw_mont_f pbits rLen n mu bBits b l table_len t1) oneM in
  mod_exp_fw_mont_loop_lemma pbits rLen n mu aM bBits b l table_len oneM (bBits / l);
  assert (accM < n);
  mod_exp_fw_mont_rem_lemma pbits rLen n mu aM bBits b l table_len accM


val mod_exp_fw_mont_lemma:
    pbits:pos -> rLen:nat
  -> n:pos -> mu:nat
  -> a:nat_mod n
  -> bBits:nat -> b:pos{b < pow2 bBits}
  -> l:pos{pow2 l <= Lib.IntTypes.max_size_t} -> Lemma
  (requires mont_pre pbits rLen n mu)
  (ensures  mod_exp_fw_mont pbits rLen n mu a bBits b l == pow_mod #n a b)

let mod_exp_fw_mont_lemma pbits rLen n mu a bBits b l =
  let r = pow2 (pbits * rLen) in
  let d, k = M.eea_pow2_odd (pbits * rLen) n in
  M.mont_preconditions_d pbits rLen n;
  let k1 = mk_nat_mont_group_ll pbits rLen n mu in

  let aM = M.to_mont pbits rLen n mu a in
  M.to_mont_lemma pbits rLen n d mu a;
  assert (aM == a * r % n);

  let resM = mod_exp_fw_mont_ pbits rLen n mu aM bBits b l in
  mod_exp_fw_mont_aux_lemma pbits rLen n mu aM bBits b l;
  assert (resM == LE.exp_fw k1 aM bBits b l);
  LE.exp_fw_lemma k1 aM bBits b l;
  assert (resM == LE.pow k1 aM b);

  let res = M.from_mont pbits rLen n mu resM in
  M.from_mont_lemma pbits rLen n d mu resM;
  assert (res == resM * d % n);

  mod_exp_mont_ll_lemma pbits rLen n mu a b;
  assert (res == pow a b % n);
  lemma_pow_mod #n a b
