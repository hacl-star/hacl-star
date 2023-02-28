module Hacl.Spec.P256.Lemmas

open FStar.Mul
open FStar.Math.Lemmas
open FStar.Math.Lib
open FStar.Tactics
open FStar.Tactics.Canon

open Lib.IntTypes

open Spec.P256

#set-options " --z3rlimit 100 --fuel 2 --ifuel 2"

val modulo_distributivity_mult: a: int -> b: int -> c: pos ->
  Lemma ((a * b) % c = ((a % c) * (b % c)) % c)

let modulo_distributivity_mult a b c =
  lemma_mod_mul_distr_l a b c;
  lemma_mod_mul_distr_r (a % c) b c


val power_one: a: nat -> Lemma (pow 1 a == 1)
let rec power_one a =
  match a with
  | 0 -> assert_norm (pow 1 0 == 1)
  | _ -> power_one (a - 1)


val pow_plus: a: nat -> b: nat -> c: nat ->
  Lemma (ensures (pow a b * pow a c = pow a (b + c)))
  (decreases b)

let rec pow_plus a b c =
  match b with
  | 0 -> assert_norm (pow a 0 = 1)
  | _ -> pow_plus a (b - 1) c


val power_distributivity: a: nat -> b: nat -> c: pos -> Lemma ((pow (a % c) b) % c = (pow a b) % c)
let rec power_distributivity a b c =
   match b with
   | 0 -> ()
   | _ ->
     power_distributivity a (b - 1) c;
     modulo_distributivity_mult (pow a (b -1)) a c;
     lemma_mod_twice a c;
     modulo_distributivity_mult (pow (a % c) (b -1)) (a % c) c


val power_distributivity_2: a: nat -> b: nat -> c: pos -> Lemma (pow (a * b) c == pow a c * pow b c)
let rec power_distributivity_2 a b c =
  match c with
  |0 -> ()
  |1 -> ()
  | _ ->
    power_distributivity_2 a b (c - 1);
    assert_by_tactic (pow a (c - 1) * pow b (c - 1) * a * b == (pow a c * pow b c)) canon



(* Start of Marina RSA PSS code *)
// local
val lemma_fpow_unfold0: a: nat -> b: pos {1 < b /\ b % 2 = 0} -> prime: pos { a < prime} -> Lemma (
  exp #prime a b = exp #prime (mul_n a a) (b / 2))
let lemma_fpow_unfold0 a b prime = ()


// local
val lemma_fpow_unfold1: a: nat -> b: pos {1 < b /\ b % 2 = 1} -> prime: pos { a < prime} -> Lemma (
  exp #prime a b = mul_n (exp #prime (mul_n a a) (b / 2)) a)
let lemma_fpow_unfold1 a b prime = ()


// local
val lemma_pow_unfold: a: nat -> b: pos -> Lemma (a * pow a (b - 1) == pow a b)
let lemma_pow_unfold a b = ()


// local
val lemma_pow_double: a: nat -> b: nat -> Lemma (pow (a * a) b == pow a (b + b))
let rec lemma_pow_double a b =
  if b = 0 then ()
  else begin
    calc (==) {
      pow (a * a) b;
      (==) { lemma_pow_unfold (a * a) b }
      a * a * pow (a * a) (b - 1);
      (==) { lemma_pow_double a (b - 1) }
      a * a * pow a (b + b - 2);
      (==) {power_one  a }
      pow a 1 * pow a 1 * pow a (b + b - 2);
      (==) { pow_plus a 1 1 }
      pow a 2 * pow a (b + b - 2);
      (==) { pow_plus a 2 (b + b - 2) }
      pow a (b + b);
    };
    assert (pow (a * a) b == pow a (b + b))
  end


val lemma_pow_mod_n_is_fpow: n:pos -> a:nat{a < n} -> b:pos -> Lemma
  (ensures (exp #n a b == pow a b % n)) (decreases b)

let rec lemma_pow_mod_n_is_fpow n a b =
  if b = 1 then ()
  else begin
    if b % 2 = 0 then begin
      calc (==) {
	exp #n a b;
	(==) { lemma_fpow_unfold0 a b n}
	exp #n (mul_n #n a a) (b / 2);
	(==) { lemma_pow_mod_n_is_fpow n (mul_n #n a a) (b / 2) }
	pow (mul_n #n a a) (b / 2) % n;
	(==) { power_distributivity (a * a) (b / 2) n }
	pow (a * a) (b / 2) % n;
	(==) { lemma_pow_double a (b / 2) }
	pow a b % n;
      };
      assert (exp #n a b == pow a b % n) end
    else begin
      calc (==) {
	exp #n a b;
	(==) { lemma_fpow_unfold1 a b n }
	mul_n a (exp (mul_n #n a a) (b / 2));
	(==) { lemma_pow_mod_n_is_fpow n (mul_n #n a a) (b / 2) }
	mul_n a (pow (mul_n #n a a) (b / 2) % n);
	(==) { power_distributivity (a * a) (b / 2) n }
	mul_n a (pow (a * a) (b / 2) % n);
	(==) { lemma_pow_double a (b / 2) }
	mul_n a (pow a (b / 2 * 2) % n);
	(==) { Math.Lemmas.lemma_mod_mul_distr_r a (pow a (b / 2 * 2)) n }
	a * pow a (b / 2 * 2) % n;
	(==) { power_one a }
	pow a 1 * pow a (b / 2 * 2) % n;
	(==) { power_distributivity_2 a 1 (b / 2 * 2) }
	pow a (b / 2 * 2 + 1) % n;
	(==) { Math.Lemmas.euclidean_division_definition b 2 }
	pow a b % n;
      };
      assert (exp #n a b == pow a b % n) end
  end

(* End of Marina RSA PSS code *)

val lemma_brackets : a: int -> b: int -> c: int -> Lemma (a * b * c = a * (b * c))
let lemma_brackets a b c = ()


let mul_lemma_ (a: nat) (b: nat) (c: nat) : Lemma (requires (a < c /\ b < c)) (ensures (a * b < c * c)) = ()

(*This code is taken from Curve25519, written by Polubelova M *)
val lemma_cswap2_step:
    bit:uint64{v bit <= 1}
  -> p1:uint64
  -> p2:uint64
  -> Lemma (
      let mask = u64 0 -. bit in
      let dummy = mask &. (p1 ^. p2) in
      let p1' = p1 ^. dummy in
      let p2' = p2 ^. dummy in
      if v bit = 1 then p1' == p2 /\ p2' == p1 else p1' == p1 /\ p2' == p2)

let lemma_cswap2_step bit p1 p2 =
  let mask = u64 0 -. bit in
  assert (v bit == 0 ==> v mask == 0);
  assert (v bit == 1 ==> v mask == pow2 64 - 1);
  let dummy = mask &. (p1 ^. p2) in
  logand_lemma mask (p1 ^. p2);
  assert (v bit == 1 ==> v dummy == v (p1 ^. p2));
  assert (v bit == 0 ==> v dummy == 0);
  let p1' = p1 ^. dummy in
  (* uintv_extensionality dummy (if v bit = 1 then (p1 ^. p2) else u64 0); *)
  logxor_lemma p1 p2;
  let p2' = p2 ^. dummy in
  logxor_lemma p2 p1

(* </> *)
