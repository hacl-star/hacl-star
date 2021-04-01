module Hacl.Spec.Exponentiation.Lemmas

open FStar.Mul
open Lib.NatMod
open Lib.Sequence

module Loops = Lib.LoopCombinators
module LSeq = Lib.Sequence

module LE = Lib.Exponentiation
module SE = Spec.Exponentiation

module M = Hacl.Spec.Montgomery.Lemmas
module AM = Hacl.Spec.AlmostMontgomery.Lemmas

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(* Modular exponentiation with Montgomery arithmetic *)
val mont_one: n:pos -> r:pos -> nat_mod n
let mont_one n r = 1 * r % n

val mont_mul: n:pos -> d:int -> a:nat_mod n -> b:nat_mod n -> nat_mod n
let mont_mul n d a b = a * b * d % n

val lemma_mont_one: n:pos -> r:pos -> d:int{r * d % n = 1} -> a:nat_mod n ->
  Lemma (mont_mul n d a (mont_one n r) == a)
let lemma_mont_one n r d a =
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

val lemma_mont_mul_assoc: n:pos -> d:int -> a:nat_mod n -> b:nat_mod n -> c:nat_mod n ->
  Lemma (mont_mul n d (mont_mul n d a b) c == mont_mul n d a (mont_mul n d b c))
let lemma_mont_mul_assoc n d a b c =
  calc (==) {
    mont_mul n d (mont_mul n d a b) c;
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
    mont_mul n d a (mont_mul n d b c);
    }


val lemma_mont_mul_comm: n:pos -> d:int -> a:nat_mod n -> b:nat_mod n ->
  Lemma (mont_mul n d a b == mont_mul n d a b)
let lemma_mont_mul_comm n d a b = ()

let mk_nat_mont_comm_monoid (n:pos) (r:nat) (d:int{r * d % n = 1}) : LE.comm_monoid (nat_mod n) = {
  LE.one = mont_one n r;
  LE.mul = mont_mul n d;
  LE.lemma_one = lemma_mont_one n r d;
  LE.lemma_mul_assoc = lemma_mont_mul_assoc n d;
  LE.lemma_mul_comm = lemma_mont_mul_comm n d;
  }


val pow_nat_mont_is_pow: n:pos -> r:nat -> d:int{r * d % n = 1} -> aM:nat_mod n -> b:nat ->
  Lemma (pow (aM * d % n) b * r % n == LE.pow (mk_nat_mont_comm_monoid n r d) aM b)

let rec pow_nat_mont_is_pow n r d aM b =
  let k = mk_nat_mont_comm_monoid n r d in
  if b = 0 then begin
    calc (==) {
      pow (aM * d % n) b * r % n;
      (==) { lemma_pow0 (aM * d % n) }
      1 * r % n;
      (==) { LE.lemma_pow0 k aM }
      LE.pow k aM b;
      }; () end
  else begin
    calc (==) {
      pow (aM * d % n) b * r % n;
      (==) { lemma_pow_unfold (aM * d % n) b }
      (aM * d % n) * pow (aM * d % n) (b - 1) * r % n;
      (==) {
        Math.Lemmas.paren_mul_right (aM * d % n) (pow (aM * d % n) (b - 1)) r;
        Math.Lemmas.lemma_mod_mul_distr_r (aM * d % n) (pow (aM * d % n) (b - 1) * r) n }
      (aM * d % n) * (pow (aM * d % n) (b - 1) * r % n) % n;
      (==) { pow_nat_mont_is_pow n r d aM (b - 1) }
      (aM * d % n) * LE.pow k aM (b - 1) % n;
      (==) { Math.Lemmas.lemma_mod_mul_distr_l (aM * d) (LE.pow k aM (b - 1)) n }
      aM * d * LE.pow k aM (b - 1) % n;
      (==) {
        Math.Lemmas.paren_mul_right aM d (LE.pow k aM (b - 1));
        Math.Lemmas.paren_mul_right aM (LE.pow k aM (b - 1)) d }
      aM * LE.pow k aM (b - 1) * d % n;
      (==) { LE.lemma_pow_unfold k aM b }
      LE.pow k aM b;
      }; () end


val mod_exp_mont: n:pos -> r:pos -> d:int{r * d % n == 1} -> a:nat_mod n -> b:nat -> nat_mod n
let mod_exp_mont n r d a b =
  let aM = a * r % n in
  let accM = LE.pow (mk_nat_mont_comm_monoid n r d) aM b in
  let acc = accM * d % n in
  acc


val mod_exp_mont_lemma: n:pos -> r:pos -> d:int{r * d % n == 1} -> a:nat_mod n -> b:nat ->
  Lemma (mod_exp_mont n r d a b == pow_mod #n a b)

let mod_exp_mont_lemma n r d a b =
  let k = mk_nat_mont_comm_monoid n r d in
  let aM = a * r % n in
  //let accM = LE.pow k aM b in
  //let acc = accM * d % n in

  calc (==) { // acc
    LE.pow k aM b * d % n;
    (==) { pow_nat_mont_is_pow n r d aM b }
    (pow (aM * d % n) b * r % n) * d % n;
    (==) { M.lemma_mont_id n r d (pow (aM * d % n) b) }
    pow (aM * d % n) b % n;
    (==) { }
    pow (a * r % n * d % n) b % n;
    (==) { M.lemma_mont_id n r d a }
    pow (a % n) b % n;
    (==) { Math.Lemmas.small_mod a n }
    pow a b % n;
    };
  assert (mod_exp_mont n r d a b == pow a b % n);
  lemma_pow_mod #n a b

(* Modular exponentiation with Montgomery arithmetic
   using functions from Hacl.Spec.Montgomery.Lemmas *)

val mont_one_ll: pbits:pos -> rLen:pos -> n:pos -> mu:nat{M.mont_pre pbits rLen n mu} -> nat_mod n
let mont_one_ll pbits rLen n mu =
  M.mont_one_lemma pbits rLen n mu;
  M.mont_one pbits rLen n mu

val mont_mul_ll: pbits:pos -> rLen:pos -> n:pos -> mu:nat{M.mont_pre pbits rLen n mu}
  -> a:nat_mod n -> b:nat_mod n -> nat_mod n
let mont_mul_ll pbits rLen n mu a b =
  M.mont_mul_lemma pbits rLen n mu a b;
  M.mont_mul pbits rLen n mu a b


val lemma_mont_one_ll: pbits:pos -> rLen:pos -> n:pos -> mu:nat{M.mont_pre pbits rLen n mu} -> a:nat_mod n ->
  Lemma (mont_mul_ll pbits rLen n mu a (mont_one_ll pbits rLen n mu) == a)
let lemma_mont_one_ll pbits rLen n mu a =
  let r = pow2 (pbits * rLen) in
  let d, _ = M.eea_pow2_odd (pbits * rLen) n in
  M.mont_preconditions_d pbits rLen n;

  let mont_one = mont_one_ll pbits rLen n mu in
  M.mont_one_lemma pbits rLen n mu;
  assert (mont_one == 1 * r % n);
  M.mont_mul_lemma pbits rLen n mu a mont_one;
  lemma_mont_one n r d a


val lemma_mont_mul_ll_assoc: pbits:pos -> rLen:pos -> n:pos -> mu:nat{M.mont_pre pbits rLen n mu}
  -> a:nat_mod n -> b:nat_mod n -> c:nat_mod n ->
  Lemma (mont_mul_ll pbits rLen n mu (mont_mul_ll pbits rLen n mu a b) c ==
    mont_mul_ll pbits rLen n mu a (mont_mul_ll pbits rLen n mu b c))

let lemma_mont_mul_ll_assoc pbits rLen n mu a b c =
  let r = pow2 (pbits * rLen) in
  let d, _ = M.eea_pow2_odd (pbits * rLen) n in
  M.mont_preconditions_d pbits rLen n;

  M.mont_mul_lemma pbits rLen n mu a b;
  M.mont_mul_lemma pbits rLen n mu (mont_mul_ll pbits rLen n mu a b) c;
  M.mont_mul_lemma pbits rLen n mu b c;
  M.mont_mul_lemma pbits rLen n mu a (mont_mul_ll pbits rLen n mu b c);
  lemma_mont_mul_assoc n d a b c


val lemma_mont_mul_ll_comm: pbits:pos -> rLen:pos -> n:pos -> mu:nat{M.mont_pre pbits rLen n mu}
  -> a:nat_mod n -> b:nat_mod n ->
  Lemma (mont_mul_ll pbits rLen n mu a b == mont_mul_ll pbits rLen n mu b a)

let lemma_mont_mul_ll_comm pbits rLen n mu a b =
  let r = pow2 (pbits * rLen) in
  let d, _ = M.eea_pow2_odd (pbits * rLen) n in
  M.mont_preconditions_d pbits rLen n;

  M.mont_mul_lemma pbits rLen n mu a b;
  M.mont_mul_lemma pbits rLen n mu b a;
  lemma_mont_mul_comm n d a b


let mk_nat_mont_ll_comm_monoid (pbits:pos) (rLen:pos)
  (n:pos) (mu:nat{M.mont_pre pbits rLen n mu}) : LE.comm_monoid (nat_mod n) = {
  LE.one = mont_one_ll pbits rLen n mu;
  LE.mul = mont_mul_ll pbits rLen n mu;
  LE.lemma_one = lemma_mont_one_ll pbits rLen n mu;
  LE.lemma_mul_assoc = lemma_mont_mul_ll_assoc pbits rLen n mu;
  LE.lemma_mul_comm = lemma_mont_mul_ll_comm pbits rLen n mu;
  }


val pow_nat_mont_ll_is_pow_nat_mont:
    pbits:pos -> rLen:pos
  -> n:pos -> mu:nat
  -> a:nat_mod n -> b:nat -> Lemma
  (requires M.mont_pre pbits rLen n mu)
  (ensures
   (let r = pow2 (pbits * rLen) in
    let d, _ = M.eea_pow2_odd (pbits * rLen) n in
    M.mont_preconditions_d pbits rLen n;

    LE.pow (mk_nat_mont_comm_monoid n r d) a b ==
    LE.pow (mk_nat_mont_ll_comm_monoid pbits rLen n mu) a b))

let rec pow_nat_mont_ll_is_pow_nat_mont pbits rLen n mu a b =
  let r = pow2 (pbits * rLen) in
  let d, _ = M.eea_pow2_odd (pbits * rLen) n in
  M.mont_preconditions_d pbits rLen n;

  let k0 = mk_nat_mont_comm_monoid n r d in
  let k1 = mk_nat_mont_ll_comm_monoid pbits rLen n mu in

  if b = 0 then begin
    LE.lemma_pow0 k0 a;
    LE.lemma_pow0 k1 a;
    M.to_mont_lemma pbits rLen n mu 1 end
  else begin
    LE.lemma_pow_unfold k0 a b;
    LE.lemma_pow_unfold k1 a b;
    //assert (LE.pow k1 a b == k1.LE.fmul a (LE.pow k1 a (b - 1)));
    M.mont_mul_lemma pbits rLen n mu a (LE.pow k1 a (b - 1));
    pow_nat_mont_ll_is_pow_nat_mont pbits rLen n mu a (b - 1);
    () end


val mod_exp_mont_ll: pbits:pos -> rLen:pos -> n:pos -> mu:nat{M.mont_pre pbits rLen n mu}
  -> a:nat_mod n -> b:nat -> nat_mod n

let mod_exp_mont_ll pbits rLen n mu a b =
  let aM = M.to_mont pbits rLen n mu a in
  M.to_mont_lemma pbits rLen n mu a;
  let accM = LE.pow (mk_nat_mont_ll_comm_monoid pbits rLen n mu) aM b in
  let acc = M.from_mont pbits rLen n mu accM in
  M.from_mont_lemma pbits rLen n mu accM;
  acc


val mod_exp_mont_ll_mod_lemma: pbits:pos -> rLen:pos -> n:pos -> mu:nat{M.mont_pre pbits rLen n mu}
  -> a:nat_mod n -> b:nat -> accM:nat -> Lemma
  (requires (let r = pow2 (pbits * rLen) in
    let k = mk_nat_mont_ll_comm_monoid pbits rLen n mu in
    accM < r /\ accM % n == LE.pow k (a * r % n) b))
  (ensures
    (let aM = M.to_mont pbits rLen n mu a in
     let acc = M.from_mont pbits rLen n mu accM in
     acc == pow_mod #n a b))

let mod_exp_mont_ll_mod_lemma pbits rLen n mu a b accM =
  let r = pow2 (pbits * rLen) in
  let d, _ = M.eea_pow2_odd (pbits * rLen) n in
  M.mont_preconditions_d pbits rLen n;

  let k1 = mk_nat_mont_ll_comm_monoid pbits rLen n mu in
  let k2 = mk_nat_mont_comm_monoid n r d in

  let aM = M.to_mont pbits rLen n mu a in
  M.to_mont_lemma pbits rLen n mu a;
  assert (aM == a * r % n);

  pow_nat_mont_ll_is_pow_nat_mont pbits rLen n mu aM b;
  assert (accM % n == LE.pow k2 aM b);

  let acc = M.from_mont pbits rLen n mu accM in
  M.from_mont_lemma pbits rLen n mu accM;
  assert (acc == accM * d % n);
  Math.Lemmas.lemma_mod_mul_distr_l accM d n;
  mod_exp_mont_lemma n r d a b


val mod_exp_mont_ll_lemma: pbits:pos -> rLen:pos -> n:pos -> mu:nat{M.mont_pre pbits rLen n mu}
  -> a:nat_mod n -> b:nat ->
  Lemma (mod_exp_mont_ll pbits rLen n mu a b == pow_mod #n a b)

let mod_exp_mont_ll_lemma pbits rLen n mu a b =
  let k = mk_nat_mont_ll_comm_monoid pbits rLen n mu in
  let aM = M.to_mont pbits rLen n mu a in
  M.to_mont_lemma pbits rLen n mu a;

  let accM = LE.pow k aM b in
  assert (accM == LE.pow k aM b /\ accM < n);
  Math.Lemmas.small_mod accM n;
  mod_exp_mont_ll_mod_lemma pbits rLen n mu a b accM


val from_mont_exp_lemma: pbits:pos -> rLen:pos -> n:pos -> mu:nat -> aM:nat -> b:nat -> Lemma
  (requires
    M.mont_pre pbits rLen n mu /\ aM < n)
  (ensures
   (let k = mk_nat_mont_ll_comm_monoid pbits rLen n mu in
    let cM = LE.pow k aM b in
    let c = M.from_mont pbits rLen n mu cM in
    let a = M.from_mont pbits rLen n mu aM in
    a < n /\ c == pow_mod #n a b))

let from_mont_exp_lemma pbits rLen n mu aM b =
  let r = pow2 (pbits * rLen) in
  let d, _ = M.eea_pow2_odd (pbits * rLen) n in
  M.mont_preconditions_d pbits rLen n;

  let k1 = mk_nat_mont_ll_comm_monoid pbits rLen n mu in
  let k2 = mk_nat_mont_comm_monoid n r d in

  let cM = LE.pow k1 aM b in
  let c = M.from_mont pbits rLen n mu cM in
  let a = M.from_mont pbits rLen n mu aM in

  M.from_mont_lemma pbits rLen n mu cM;
  M.from_mont_lemma pbits rLen n mu aM;
  //assert (c == cM * d % n);
  calc (==) {
    cM * d % n;
    (==) { pow_nat_mont_ll_is_pow_nat_mont pbits rLen n mu aM b }
    LE.pow k2 aM b * d % n;
    (==) { pow_nat_mont_is_pow n r d aM b }
    pow (aM * d % n) b * r % n * d % n;
    (==) { M.lemma_mont_id n r d (pow (aM * d % n) b) }
    pow (aM * d % n) b % n;
    (==) { }
    pow a b % n;
    (==) { Lib.NatMod.lemma_pow_mod #n a b }
    pow_mod #n a b;
    };
  assert (a < n /\ c == pow_mod #n a b)


val pow_nat_mont_ll_mod_base:
    pbits:pos -> rLen:pos
  -> n:pos -> mu:nat
  -> a:nat_mod n -> b:nat -> Lemma
  (requires
    M.mont_pre pbits rLen n mu)
  (ensures
   (let k = mk_nat_mont_ll_comm_monoid pbits rLen n mu in
    LE.pow k a b == LE.pow k (a % n) b))

let pow_nat_mont_ll_mod_base pbits rLen n mu a b =
  let r = pow2 (pbits * rLen) in
  let d, _ = M.eea_pow2_odd (pbits * rLen) n in
  M.mont_preconditions_d pbits rLen n;

  let k1 = mk_nat_mont_comm_monoid n r d in
  let k2 = mk_nat_mont_ll_comm_monoid pbits rLen n mu in

  calc (==) {
    LE.pow k2 a b;
    (==) { pow_nat_mont_ll_is_pow_nat_mont pbits rLen n mu a b }
    LE.pow k1 a b;
    (==) { pow_nat_mont_is_pow n r d a b }
    pow (a * d % n) b * r % n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l a d n }
    pow (a % n * d % n) b * r % n;
    (==) { pow_nat_mont_is_pow n r d (a % n) b }
    LE.pow k1 (a % n) b;
    (==) { pow_nat_mont_ll_is_pow_nat_mont pbits rLen n mu (a % n) b }
    LE.pow k2 (a % n) b;
    }
