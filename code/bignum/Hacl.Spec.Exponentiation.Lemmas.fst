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
  M.mont_one_lemma pbits rLen n d mu;
  M.mont_one pbits rLen n mu

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
  M.mont_one_lemma pbits rLen n d mu;
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
