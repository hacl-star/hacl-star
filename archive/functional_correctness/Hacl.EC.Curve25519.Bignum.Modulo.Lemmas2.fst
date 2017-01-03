module Hacl.EC.Curve25519.Bignum.Modulo.Lemmas2

open FStar.Mul
open FStar.ST
open FStar.HyperStack
open FStar.Ghost
open Hacl.UInt64
open FStar.Buffer
open FStar.Math.Lib
open FStar.Math.Lemmas
open Hacl.EC.Curve25519.Parameters
open Hacl.EC.Curve25519.Bigint

open Hacl.EC.Curve25519.Bignum.Lemmas.Utils


#reset-options "--initial_fuel 0 --max_fuel 0"

(* Module abbreviations *)
module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module U8  = FStar.UInt8
module U32 = FStar.UInt32
module H8  = Hacl.UInt8
module H32  = Hacl.UInt32
module H64  = Hacl.UInt64


#reset-options "--z3rlimit 5 --initial_fuel 0 --max_fuel 0"

val lemma_div_def: a:nat -> b:pos -> Lemma (a = b * (a / b) + a % b)
let lemma_div_def a b = ()

val lemma_mod_a_b: a:pos -> b:nat -> Lemma ((a + b) % a = b % a)
let lemma_mod_a_b a b = lemma_mod_plus b 1 a

val lemma_modulo_mul: a:nat -> b:nat -> p:pos -> Lemma ((a * b) % p = (a%p * b) % p)
let lemma_modulo_mul a b p =
  lemma_mod_mul_distr_l a b p
val lemma_modulo_add: a:nat -> b:nat -> p:pos -> Lemma ((a + b) % p = (a%p + b) % p)
let lemma_modulo_add a b p =
  lemma_mod_plus_distr_l a b p


#reset-options "--z3rlimit 5 --initial_fuel 0 --max_fuel 0"

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

private val lemma_2_255m19_val: n:nat -> Lemma (requires (n = 255))
                                              (ensures (pow2 n - 19 > 0))
                                              [SMTPat (pow2 n - 19)]
let lemma_2_255m19_val n = assert_norm (pow2 255 - 19 > 0)

val lemma_2_255_modulo_prime: unit -> Lemma (pow2 255 - 19 > 0 /\ pow2 255 % (pow2 255 - 19) = 19)
let lemma_2_255_modulo_prime () =
  assert_norm(pow2 255 % (pow2 255 - 19) = 19)


#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

let isCarried (h0:mem) (h1:mem) (b:bigint) : GTot Type0 =
  live h0 b /\ live h1 b /\ length b >= norm_length+1
  /\ ( let open Hacl.UInt64 in
      let b0 = v (get h0 b 0) in
      let b1 = v (get h0 b 1) in
      let b2 = v (get h0 b 2) in
      let b3 = v (get h0 b 3) in
      let b4 = v (get h0 b 4) in
      let r0  = b0 / pow2 51 in
      let r1  = (b1 + r0) / pow2 51 in
      let r2  = (b2 + r1) / pow2 51 in
      let r3  = (b3 + r2) / pow2 51 in
      v (get h1 b 5) = (b4 + r3) / pow2 51
      /\ v (get h1 b 0) = b0 % pow2 51
      /\ v (get h1 b 1) = (b1 + r0)  % pow2 51
      /\ v (get h1 b 2) = (b2 + r1)  % pow2 51
      /\ v (get h1 b 3) = (b3 + r2)  % pow2 51
      /\ v (get h1 b 4) = (b4 + r3)  % pow2 51
    )

#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"


let u63 = x:H64.t{H64.v x < pow2 63}

let bound63 (h:heap) (b:bigint) : GTot Type0 =
  live h b /\ v (get h b 0) < pow2 63 /\ v (get h b 1) < pow2 63 /\ v (get h b 2) < pow2 63
  /\ v (get h b 3) < pow2 63 /\ v (get h b 4) < pow2 63

#reset-options "--z3rlimit 5 --initial_fuel 0 --max_fuel 0"


let isCarried_
  (h1:mem)
  (b0:H64.t) (b1:H64.t) (b2:H64.t) (b3:H64.t) (b4:H64.t)
  (b:bigint) : GTot Type0 =
  live h1 b /\ length b >= norm_length+1
  /\ ( let open Hacl.UInt64 in
      let r0  = v b0 / pow2 51 in
      let r1  = (v b1 + r0) / pow2 51 in
      let r2  = (v b2 + r1) / pow2 51 in
      let r3  = (v b3 + r2) / pow2 51 in
      v (get h1 b 5) = (v b4 + r3) / pow2 51
      /\ v (get h1 b 0) = v b0 % pow2 51
      /\ v (get h1 b 1) = (v b1 + r0)  % pow2 51
      /\ v (get h1 b 2) = (v b2 + r1)  % pow2 51
      /\ v (get h1 b 3) = (v b3 + r2)  % pow2 51
      /\ v (get h1 b 4) = (v b4 + r3)  % pow2 51
    )


let carried_1 (h:mem) (b:bigint) : GTot Type0 =
  live h b /\ length b >= norm_length+1
  /\ (let open Hacl.UInt64 in
  v (get h b 0) < pow2 51
  /\ v (get h b 1) < pow2 51
  /\ v (get h b 2) < pow2 51
  /\ v (get h b 3) < pow2 51
  /\ v (get h b 4) < pow2 51
  /\ v (get h b 5) <= pow2 13)


#reset-options "--z3rlimit 5 --initial_fuel 0 --max_fuel 0"

let lemma_carry_10_0 (x:int) (y:pos) : Lemma (x % y < y) = ()
let lemma_carry_10_1 (x:nat) (y:nat) (z:pos) : Lemma (requires (x < y)) (ensures (x / z <= y / z))
  = lemma_div_mod x z;
    lemma_div_mod y z;
    assert(x = z * (x / z) + x % z);
    assert(y = z * (y / z) + y % z);
    let xz = x/z in let yz = y/z in
    distributivity_sub_right z yz xz;
    assert(z * (yz - xz) + y % z - x % z > 0);
    cut (x % z < z /\ y % z < z);
    assert(z * (yz - xz) > x % z - y % z);
    assert(z * (yz - xz) > - z)
let lemma_carry_10_2 (x:nat) : Lemma (requires (x < pow2 64)) (ensures (x / pow2 51 <= pow2 13))
  = pow2_minus 64 51;
    lemma_carry_10_1 x (pow2 64) (pow2 51)


val lemma_carry_10:
  h0:mem -> h1:mem ->
  b:bigint{length b >= norm_length+1} ->
  Lemma (requires (bound63 h0 b /\ isCarried h0 h1 b))
	(ensures  (carried_1 h1 b))
let lemma_carry_10 h0 h1 b =
  let open Hacl.UInt64 in
  let (p51:pos) = pow2 51 in
  let b0 = v (get h0 b 0) in
  let b1 = v (get h0 b 1) in
  let b2 = v (get h0 b 2) in
  let b3 = v (get h0 b 3) in
  let b4 = v (get h0 b 4) in
  nat_over_pos_is_nat b0 p51;
  let r0  = b0 / p51 in
  nat_over_pos_is_nat (b1+r0) p51;
  let r1  = (b1 + r0) / p51 in
  nat_over_pos_is_nat (b2+r1) p51;
  let r2  = (b2 + r1) / p51 in
  nat_over_pos_is_nat (b3+r2) p51;
  let r3  = (b3 + r2) / p51 in
  nat_over_pos_is_nat (b4+r3) p51;
  lemma_carry_10_0 b0 (p51);
  lemma_carry_10_0 (b1+r0) (p51);
  lemma_carry_10_0 (b2+r1) (p51);
  lemma_carry_10_0 (b3+r2) (p51);
  lemma_carry_10_0 (b4+r3) (p51);
  pow2_double_sum 63;
  pow2_lt_compat 63 51;
  pow2_lt_compat 63 13;
  lemma_carry_10_2 b0;
  lemma_carry_10_2 (b1+r0);
  lemma_carry_10_2 (b2+r1);
  lemma_carry_10_2 (b3+r2);
  lemma_carry_10_2 (b4+r3)


#reset-options "--z3rlimit 5 --initial_fuel 0 --max_fuel 0"

let lemma_carry_110_0 (x:int) (y:int) (z:nat) :
  Lemma (pow2 z * (x + pow2 51 * y) = pow2 z * x + pow2 (z+51) * y)
  = distributivity_add_right (pow2 z) x (pow2 51 * y);
    pow2_plus 51 z


val lemma_carry_1101:
  b0:nat -> b1:nat -> b2:nat -> b3:nat -> b4:nat ->
  c0:nat -> c1:nat -> c2:nat -> c3:nat -> c4:nat -> c5:nat ->
  Lemma (requires (
    let p51 = pow2 51 in
    c0 = (b0 % p51)
    /\ c1 = ((b0 / p51 + b1) % p51)
    /\ (b0 / p51 + b1) >= 0
    /\ c2 = (((b0 / p51 + b1) / p51 + b2) % p51)
    /\ ((b0 / p51 + b1) / p51 + b2) >= 0
    /\ c3 = ((((b0 / p51 + b1) / p51 + b2) / p51 + b3) % p51)
    /\ (((b0 / p51 + b1) / p51 + b2) / p51 + b3) >= 0
    /\ c4 = (((((b0 / p51 + b1) / p51 + b2) / p51 + b3) / p51 + b4) % pow2 51)
    /\ ((((b0 / p51 + b1) / p51 + b2) / p51 + b3) / p51 + b4) >= 0
    /\ c5 = (((((b0 / p51 + b1) / p51 + b2) / p51 + b3) / p51 + b4) / pow2 51) ))
    (ensures  (let p51 = pow2 51 in pow2 204 * c4 + pow2 255 * c5 = pow2 204 * ((((b0 / p51 + b1) / p51 + b2) / p51 + b3) / p51) + pow2 204 * b4))
let lemma_carry_1101 b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 c5 =
  let p51 = pow2 51 in
  nat_over_pos_is_nat b0 p51;
  let r0  = b0 / p51 in
  nat_over_pos_is_nat (b1+r0) p51;
  let r1  = (b1 + r0) / p51 in
  nat_over_pos_is_nat (b2+r1) p51;
  let r2  = (b2 + r1) / p51 in
  nat_over_pos_is_nat (b3+r2) p51;
  let r3  = (b3 + r2) / p51 in
  nat_over_pos_is_nat (b4+r3) p51;
  lemma_div_mod ((((b0 / p51 + b1) / p51 + b2) / p51 + b3) / p51 + b4) (pow2 51);
  cut (c4 + pow2 51 * c5 = (((b0 / p51 + b1) / p51 + b2) / p51 + b3) / p51 + b4);
  lemma_carry_110_0 c4 c5 204;
  cut (pow2 204 * c4 + pow2 255 * c5 = pow2 204 * (c4 + pow2 51 * c5));
  distributivity_add_right (pow2 204) ((((b0 / p51 + b1) / p51 + b2) / p51 + b3) / p51) b4


#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

val lemma_carry_1102:
  b0:nat -> b1:nat -> b2:nat -> b3:nat -> b4:nat ->
  c0:nat -> c1:nat -> c2:nat -> c3:nat -> c4:nat -> c5:nat ->
  Lemma (requires (
    let p51 = pow2 51 in
    c0 = (b0 % p51)
    /\ c1 = ((b0 / p51 + b1) % p51)
    /\ (b0 / p51 + b1) >= 0
    /\ c2 = (((b0 / p51 + b1) / p51 + b2) % p51)
    /\ ((b0 / p51 + b1) / p51 + b2) >= 0
    /\ c3 = ((((b0 / p51 + b1) / p51 + b2) / p51 + b3) % p51)
    /\ (((b0 / p51 + b1) / p51 + b2) / p51 + b3) >= 0
    /\ c4 = (((((b0 / p51 + b1) / p51 + b2) / p51 + b3) / p51 + b4) % pow2 51)
    /\ ((((b0 / p51 + b1) / p51 + b2) / p51 + b3) / p51 + b4) >= 0
    /\ c5 = (((((b0 / p51 + b1) / p51 + b2) / p51 + b3) / p51 + b4) / pow2 51) ))
    (ensures  (let p51 = pow2 51 in pow2 153 * c3 + pow2 204 * ((((b0 / p51 + b1) / p51 + b2) / p51 + b3) / p51) = pow2 153 * (((b0 / p51 + b1) / p51 + b2) / p51) + pow2 153 * b3))
let lemma_carry_1102 b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 c5 =
  let p51 = pow2 51 in
  nat_over_pos_is_nat b0 p51;
  let r0  = b0 / p51 in
  nat_over_pos_is_nat (b1+r0) p51;
  let r1  = (b1 + r0) / p51 in
  nat_over_pos_is_nat (b2+r1) p51;
  let r2  = (b2 + r1) / p51 in
  nat_over_pos_is_nat (b3+r2) p51;
  let r3  = (b3 + r2) / p51 in
  nat_over_pos_is_nat (b4+r3) p51;
  lemma_div_mod ((((b0 / p51 + b1) / p51 + b2) / p51 + b3)) (pow2 51);
  cut (c3 + pow2 51 * ((((b0 / p51 + b1) / p51 + b2) / p51 + b3) / pow2 51) = (((b0 / p51 + b1) / p51 + b2) / p51 + b3));
  lemma_carry_110_0 c3 ((((b0 / p51 + b1) / p51 + b2) / p51 + b3) / pow2 51) 153;
  distributivity_add_right (pow2 153) (((b0 / p51 + b1) / p51 + b2) / pow2 51) b3


#reset-options "--z3rlimit 5 --initial_fuel 0 --max_fuel 0"

val lemma_carry_1103:
  b0:nat -> b1:nat -> b2:nat -> b3:nat -> b4:nat ->
  c0:nat -> c1:nat -> c2:nat -> c3:nat -> c4:nat -> c5:nat ->
  Lemma (requires (
    let p51 = pow2 51 in
    c0 = (b0 % p51)
    /\ c1 = ((b0 / p51 + b1) % p51)
    /\ (b0 / p51 + b1) >= 0
    /\ c2 = (((b0 / p51 + b1) / p51 + b2) % p51)
    /\ ((b0 / p51 + b1) / p51 + b2) >= 0
    /\ c3 = ((((b0 / p51 + b1) / p51 + b2) / p51 + b3) % p51)
    /\ (((b0 / p51 + b1) / p51 + b2) / p51 + b3) >= 0
    /\ c4 = (((((b0 / p51 + b1) / p51 + b2) / p51 + b3) / p51 + b4) % pow2 51)
    /\ ((((b0 / p51 + b1) / p51 + b2) / p51 + b3) / p51 + b4) >= 0
    /\ c5 = (((((b0 / p51 + b1) / p51 + b2) / p51 + b3) / p51 + b4) / pow2 51) ))
    (ensures  (let p51 = pow2 51 in pow2 102 * c2 + pow2 153 * (((b0 / p51 + b1) / p51 + b2) / p51) = pow2 102 * ((b0 / p51 + b1) / p51) + pow2 102 * b2))
let lemma_carry_1103 b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 c5 =
  let p51 = pow2 51 in
  nat_over_pos_is_nat b0 p51;
  let r0  = b0 / p51 in
  nat_over_pos_is_nat (b1+r0) p51;
  let r1  = (b1 + r0) / p51 in
  nat_over_pos_is_nat (b2+r1) p51;
  let r2  = (b2 + r1) / p51 in
  nat_over_pos_is_nat (b3+r2) p51;
  let r3  = (b3 + r2) / p51 in
  nat_over_pos_is_nat (b4+r3) p51;
  lemma_div_mod (((b0 / p51 + b1) / p51 + b2)) (pow2 51);
  cut (c2 + pow2 51 * ((((b0 / p51 + b1) / p51 + b2) / p51)) = (((b0 / p51 + b1) / p51 + b2)));
  lemma_carry_110_0 c2 ((((b0 / p51 + b1) / p51 + b2)) / pow2 51) 102;
  distributivity_add_right (pow2 102) (((b0 / p51 + b1) / p51)) b2


#reset-options "--z3rlimit 5 --initial_fuel 0 --max_fuel 0"

val lemma_carry_1204:
  b0:nat -> b1:nat -> b2:nat -> b3:nat -> b4:nat ->
  c0:nat -> c1:nat -> c2:nat -> c3:nat -> c4:nat -> c5:nat ->
  Lemma (requires (
    let p51 = pow2 51 in
    c0 = (b0 % p51)
    /\ c1 = ((b0 / p51 + b1) % p51)
    /\ (b0 / p51 + b1) >= 0
    /\ c2 = (((b0 / p51 + b1) / p51 + b2) % p51)
    /\ ((b0 / p51 + b1) / p51 + b2) >= 0
    /\ c3 = ((((b0 / p51 + b1) / p51 + b2) / p51 + b3) % p51)
    /\ (((b0 / p51 + b1) / p51 + b2) / p51 + b3) >= 0
    /\ c4 = (((((b0 / p51 + b1) / p51 + b2) / p51 + b3) / p51 + b4) % pow2 51)
    /\ ((((b0 / p51 + b1) / p51 + b2) / p51 + b3) / p51 + b4) >= 0
    /\ c5 = (((((b0 / p51 + b1) / p51 + b2) / p51 + b3) / p51 + b4) / pow2 51) ))
    (ensures  (let p51 = pow2 51 in pow2 51 * c1 + pow2 102 * (((b0 / p51 + b1) / p51)) = pow2 51 * ((b0 / p51)) + pow2 51 * b1))
let lemma_carry_1204 b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 c5 =
  let p51 = pow2 51 in
  nat_over_pos_is_nat b0 p51;
  let r0  = b0 / p51 in
  nat_over_pos_is_nat (b1+r0) p51;
  let r1  = (b1 + r0) / p51 in
  nat_over_pos_is_nat (b2+r1) p51;
  let r2  = (b2 + r1) / p51 in
  nat_over_pos_is_nat (b3+r2) p51;
  let r3  = (b3 + r2) / p51 in
  nat_over_pos_is_nat (b4+r3) p51;
  lemma_div_mod (((b0 / p51 + b1))) (pow2 51);
  cut (c1 + pow2 51 * ((((b0 / p51 + b1) / p51))) = (((b0 / p51 + b1))));
  lemma_carry_110_0 c1 ((((b0 / p51 + b1))) / pow2 51) 51;
  distributivity_add_right (pow2 51) (((b0 / p51))) b1


#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

val lemma_carry_110:
  b0:nat -> b1:nat -> b2:nat -> b3:nat -> b4:nat ->
  c0:nat -> c1:nat -> c2:nat -> c3:nat -> c4:nat -> c5:nat ->
  Lemma (requires (
    let p51 = pow2 51 in
    c0 = (b0 % p51)
    /\ c1 = ((b0 / p51 + b1) % p51)
    /\ (b0 / p51 + b1) >= 0
    /\ c2 = (((b0 / p51 + b1) / p51 + b2) % p51)
    /\ ((b0 / p51 + b1) / p51 + b2) >= 0
    /\ c3 = ((((b0 / p51 + b1) / p51 + b2) / p51 + b3) % p51)
    /\ (((b0 / p51 + b1) / p51 + b2) / p51 + b3) >= 0
    /\ c4 = (((((b0 / p51 + b1) / p51 + b2) / p51 + b3) / p51 + b4) % pow2 51)
    /\ ((((b0 / p51 + b1) / p51 + b2) / p51 + b3) / p51 + b4) >= 0
    /\ c5 = (((((b0 / p51 + b1) / p51 + b2) / p51 + b3) / p51 + b4) / pow2 51) ))
    (ensures  (b0 + pow2 51 * b1 + pow2 102 * b2 + pow2 153 * b3 + pow2 204 * b4
      = c0 + pow2 51 * c1 + pow2 102 * c2 + pow2 153 * c3 + pow2 204 * c4 + pow2 255 * c5))
let lemma_carry_110 b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 c5 =
  let p51 = pow2 51 in
  lemma_carry_1101 b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 c5;
  let z = c0 + pow2 51 * c1 + pow2 102 * c2 + pow2 153 * c3 + pow2 204 * c4 + pow2 255 * c5 in
  cut (z = c0 + pow2 51 * c1 + pow2 102 * c2 + pow2 153 * c3 + pow2 204 * ((((b0 / p51 + b1) / p51 + b2) / p51 + b3) / p51) + pow2 204 * b4);
  lemma_carry_1102 b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 c5;
  cut (c0 + pow2 51 * c1 + pow2 102 * c2 + pow2 153 * c3 + pow2 204 * ((((b0 / p51 + b1) / p51 + b2) / p51 + b3) / p51) + pow2 204 * b4 = c0 + pow2 51 * c1 + pow2 102 * c2 + pow2 153 * (((b0 / p51 + b1) / p51 + b2) / p51) + pow2 153 * b3 + pow2 204 * b4);
  lemma_carry_1103 b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 c5;
  cut (c0 + pow2 51 * c1 + pow2 102 * c2 + pow2 153 * (((b0 / p51 + b1) / p51 + b2) / p51) + pow2 153 * b3 + pow2 204 * b4 = c0 + pow2 51 * c1 + pow2 102 * ((b0 / p51 + b1) / p51) + pow2 102 * b2 + pow2 153 * b3 + pow2 204 * b4);
  lemma_carry_1204 b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 c5;
  cut (c0 + pow2 51 * c1 + pow2 102 * ((b0 / p51 + b1) / p51) + pow2 102 * b2 + pow2 153 * b3 + pow2 204 * b4 = c0 + pow2 51 * ((b0 / p51)) + pow2 51 * b1 + pow2 102 * b2 + pow2 153 * b3 + pow2 204 * b4);
  lemma_div_mod b0 (pow2 51)


#reset-options "--z3rlimit 5 --initial_fuel 0 --max_fuel 0"

val lemma_carry_11:
  h0:mem -> h1:mem ->
  b:bigint{length b >= norm_length+1} ->
  Lemma (requires (isCarried h0 h1 b))
	(ensures  (isCarried h0 h1 b
	  /\ eval h1 b (norm_length+1) = eval h0 b norm_length))
let lemma_carry_11 h0 h1 b =
  let (p51:pos) = pow2 51 in
  lemma_eval_bigint_5 h0 b;
  lemma_eval_bigint_6 h1 b;
  let open Hacl.UInt64 in
  let b0 = v (get h0 b 0) in
  let b1 = v (get h0 b 1) in
  let b2 = v (get h0 b 2) in
  let b3 = v (get h0 b 3) in
  let b4 = v (get h0 b 4) in
  nat_over_pos_is_nat b0 p51;
  let r0  = b0 / p51 in
  nat_over_pos_is_nat (b1+r0) p51;
  let r1  = (b1 + r0) / p51 in
  nat_over_pos_is_nat (b2+r1) p51;
  let r2  = (b2 + r1) / p51 in
  nat_over_pos_is_nat (b3+r2) p51;
  let r3  = (b3 + r2) / p51 in
  nat_over_pos_is_nat (b4+r3) p51;
  cut(eval h1 b 6 = v (get h1 b 0) + pow2 51  * v (get h1 b 1) + pow2 102  * v (get h1 b 2)
	       + pow2 153  * v (get h1 b 3) + pow2 204 * v (get h1 b 4) + pow2 255 * v (get h1 b 5));
  cut (v (get h1 b 0) = b0 % p51);
  cut (v (get h1 b 1) = ((b0 / p51 + b1) % p51));
  cut (v (get h1 b 2) = (((b0 / p51 + b1) / p51 + b2) % p51));
  cut (v (get h1 b 3) = ((((b0 / p51 + b1) / p51 + b2) / p51 + b3) % p51));
  cut (v (get h1 b 4) = (((((b0 / p51 + b1) / p51 + b2) / p51 + b3) / p51 + b4) % pow2 51) );
  cut (v (get h1 b 5) = (((((b0 / p51 + b1) / p51 + b2) / p51 + b3) / p51 + b4) / pow2 51) );
  lemma_carry_110 b0 b1 b2 b3 b4 (v (get h1 b 0)) (v (get h1 b 1)) (v (get h1 b 2)) (v (get h1 b 3)) (v (get h1 b 4)) (v (get h1 b 5))


#reset-options "--z3rlimit 5 --initial_fuel 0 --max_fuel 0"

val lemma_carry_1:
  h0:mem -> h1:mem ->
  b:bigint{length b >= norm_length+1} ->
  Lemma (requires (bound63 h0 b /\ isCarried h0 h1 b))
	(ensures  (bound63 h0 b /\ isCarried h0 h1 b
	  /\ eval h1 b (norm_length+1) = eval h0 b norm_length
	  /\ carried_1 h1 b))
let lemma_carry_1 h0 h1 b =
  lemma_carry_10 h0 h1 b;
  lemma_carry_11 h0 h1 b


#reset-options "--z3rlimit 5 --initial_fuel 0 --max_fuel 0"

let carried_2 (h:mem) (b:bigint) : GTot Type0 =
  let open Hacl.UInt64 in
  live h b /\ length b >= norm_length+1
  /\ v (get h b 0) < pow2 52
  /\ v (get h b 1) < pow2 51
  /\ v (get h b 2) < pow2 51
  /\ v (get h b 3) < pow2 51
  /\ v (get h b 4) < pow2 51


let carried_3 (h:mem) (b:bigint) : GTot Type0 =
  let open Hacl.UInt64 in
  norm h b /\ length b >= norm_length+1
  /\ v (get h b 5) <= 1
  /\ (v (get h b 5) = 1
    ==> (v (get h b 1) < pow2 1 /\ v (get h b 2) < pow2 1  /\ v (get h b 3) < pow2 1
	/\ v (get h b 4) < pow2 1))


val lemma_div_lt: a:nat -> n:nat -> m:nat{m <= n} ->
  Lemma (requires (a < pow2 n))
	(ensures  (a / pow2 m < pow2 (n-m)))
let lemma_div_lt a n m =
  lemma_div_mod a (pow2 m);
  assert(a = pow2 m * (a / pow2 m) + a % pow2 m);
  pow2_plus m (n-m);
  assert(pow2 n = pow2 m * pow2 (n - m))

val lemma_div_rest: a:nat -> m:nat -> n:nat{m < n} ->
  Lemma (requires (a >= pow2 n /\ a < pow2 m + pow2 n))
	(ensures  (a % pow2 n < pow2 m))
let lemma_div_rest a m n =
  pow2_double_sum n;
  lemma_div_mod a (pow2 n)

let lemma_mod_0 (a:nat) (b:pos) : Lemma (a % b < b) = ()


#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

val lemma_carry_20:
  h0:mem -> h1:mem ->
  b:bigint{length b >= norm_length+1} ->
  Lemma (requires (carried_2 h0 b /\ isCarried h0 h1 b))
	(ensures  (carried_2 h0 b /\ isCarried h0 h1 b /\ carried_3 h1 b))
let lemma_carry_20 h0 h1 b =
  let open Hacl.UInt64 in
  let p51 = pow2 51 in
  let b0 = v (get h0 b 0) in
  let b1 = v (get h0 b 1) in
  let b2 = v (get h0 b 2) in
  let b3 = v (get h0 b 3) in
  let b4 = v (get h0 b 4) in
  nat_over_pos_is_nat b0 p51;
  let r0  = b0 / p51 in
  nat_over_pos_is_nat (b1+r0) p51;
  let r1  = (b1 + r0) / p51 in
  nat_over_pos_is_nat (b2+r1) p51;
  let r2  = (b2 + r1) / p51 in
  nat_over_pos_is_nat (b3+r2) p51;
  let r3  = (b3 + r2) / p51 in
  nat_over_pos_is_nat (b4+r3) p51;
  lemma_carry_10_1 b0 (pow2 52) (pow2 51);
  lemma_div_lt b0 52 51;
  assert(r0 < pow2 1);
  pow2_lt_compat 51 1;
  pow2_double_sum 51;
  lemma_div_lt (b1+r0) 52 51;
  pow2_lt_compat 51 1;
  lemma_div_lt (b2+r1) 52 51;
  pow2_lt_compat 51 1;
  lemma_div_lt (b3+r2) 52 51;
  pow2_lt_compat 51 1;
  lemma_div_lt (b4+r3) 52 51;
  pow2_lt_compat 51 1;
  assert_norm(pow2 1 = 2);
  cut (v (get h1 b 5) = 1 ==> b4 + r3 >= pow2 51);
  cut (b4 + r3 >= pow2 51 ==> r3 = 1);
  cut (r3 = 1 ==> b3 + r2 >= pow2 51);
  cut (b3 + r2 >= pow2 51 ==> r1 = 1);
  cut (r1 = 1 ==> b1 + r0 >= pow2 51);
  cut (b1 + r0 >= pow2 51 ==> r0 >= 1);
  lemma_mod_0 b0 (pow2 51);
  lemma_mod_0 (b1+r0) (pow2 51);
  lemma_mod_0 (b2+r1) (pow2 51);
  lemma_mod_0 (b3+r2) (pow2 51);
  lemma_mod_0 (b4+r3) (pow2 51);
  if (v (get h1 b 5) = 1) then (
    lemma_div_rest (b1 + r0) 1 51;
    lemma_div_rest (b2 + r1) 1 51;
    lemma_div_rest (b3 + r2) 1 51;
    lemma_div_rest (b4 + r3) 1 51
  )


#reset-options "--z3rlimit 5 --initial_fuel 0 --max_fuel 0"

val lemma_carry_2:
  h0:mem -> h1:mem ->
  b:bigint{length b >= norm_length+1} ->
  Lemma (requires (carried_2 h0 b /\ isCarried h0 h1 b))
	(ensures  (carried_2 h0 b /\ isCarried h0 h1 b
	  /\ eval h1 b (norm_length+1) = eval h0 b norm_length
	  /\ carried_3 h1 b))
let lemma_carry_2 h0 h1 b =
  lemma_carry_20 h0 h1 b;
  lemma_carry_11 h0 h1 b


#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"


let carriedTopBottom (h0:mem) (h1:mem) (b:bigint) : GTot Type0 =
  let open Hacl.UInt64 in
  live h0 b /\ live h1 b /\ length b >= norm_length+1
  /\ v (get h1 b 0) = v (get h0 b 0) + 19 * v (get h0 b 5)
  /\ v (get h1 b 1) = v (get h0 b 1)
  /\ v (get h1 b 2) = v (get h0 b 2)
  /\ v (get h1 b 3) = v (get h0 b 3)
  /\ v (get h1 b 4) = v (get h0 b 4)


val lemma_carry_top_10:
  h0:mem -> h1:mem ->
  b:bigint ->
  Lemma (requires (carried_1 h0 b /\ carriedTopBottom h0 h1 b))
	(ensures  (carried_1 h0 b /\ carriedTopBottom h0 h1 b /\ carried_2 h1 b))
let lemma_carry_top_10 h0 h1 b =
  assert_norm(pow2 5 = 32);
  pow2_plus 5 13;
  pow2_lt_compat 51 18;
  pow2_double_sum 51


val lemma_mod_6_p:
  b0:nat -> b1:nat -> b2:nat -> b3:nat -> b4:nat -> b5:nat -> p:pos ->
  Lemma	(ensures  (
    (b0 + pow2 51 * b1 + pow2 102 * b2 + pow2 153 * b3 + pow2 204 * b4 + pow2 255 * b5) % p
    = (b0 + pow2 51 * b1 + pow2 102 * b2 + pow2 153 * b3 + pow2 204 * b4 + (pow2 255) % p * b5) % p
  ))
let lemma_mod_6_p b0 b1 b2 b3 b4 b5 p =
  lemma_mod_plus_distr_l (pow2 255 * b5)
			 (b0 + pow2 51 * b1 + pow2 102 * b2 + pow2 153 * b3 + pow2 204 * b4)
			 p;
  lemma_mod_mul_distr_l (pow2 255) b5 p;
  lemma_mod_plus_distr_l ((pow2 255 % p) * b5)
			 (b0 + pow2 51 * b1 + pow2 102 * b2 + pow2 153 * b3 + pow2 204 * b4)
			 p


val lemma_carry_top_11:
  h0:mem -> h1:mem ->
  b:bigint ->
  Lemma (requires (carriedTopBottom h0 h1 b))
	(ensures  (carriedTopBottom h0 h1 b
	  /\ eval h1 b norm_length % reveal prime = eval h0 b (norm_length+1) % reveal prime))
let lemma_carry_top_11 h0 h1 b =
  lemma_eval_bigint_6 h0 b;
  lemma_eval_bigint_5 h1 b;
  let open Hacl.UInt64 in
  let b0 = v (get h0 b 0) in
  let b1 = v (get h0 b 1) in
  let b2 = v (get h0 b 2) in
  let b3 = v (get h0 b 3) in
  let b4 = v (get h0 b 4) in
  let b5 = v (get h0 b 5) in
  lemma_mod_6_p b0 b1 b2 b3 b4 b5 (reveal prime);
  lemma_2_255_modulo_prime ()


val lemma_carry_top_1:
  h0:mem -> h1:mem ->
  b:bigint ->
  Lemma (requires (carried_1 h0 b /\ carriedTopBottom h0 h1 b))
	(ensures  (carried_1 h0 b /\ carriedTopBottom h0 h1 b
	  /\ carried_2 h1 b
	  /\ eval h1 b norm_length % reveal prime = eval h0 b (norm_length+1) % reveal prime))
let lemma_carry_top_1 h0 h1 b =
  lemma_carry_top_10 h0 h1 b;
  lemma_carry_top_11 h0 h1 b


let carried_4 (h:mem) (b:bigint) : GTot Type0 =
  let open Hacl.UInt64 in
  live h b /\ v (get h b 0) < pow2 51 + 19
  /\ v (get h b 1) < pow2 51
  /\ (v (get h b 0) >= pow2 51 ==> v (get h b 1) < pow2 1)
  /\ v (get h b 2) < pow2 51
  /\ v (get h b 3) < pow2 51
  /\ v (get h b 4) < pow2 51


#reset-options "--z3rlimit 5 --initial_fuel 0 --max_fuel 0"

val lemma_carry_top_20:
  h0:mem -> h1:mem ->
  b:bigint ->
  Lemma (requires (carried_3 h0 b /\ carriedTopBottom h0 h1 b))
	(ensures  (carried_3 h0 b /\ carried_4 h1 b))
let lemma_carry_top_20 h0 h1 b = ()


#reset-options "--z3rlimit 5 --initial_fuel 0 --max_fuel 0"

val lemma_carry_top_2:
  h0:mem -> h1:mem ->
  b:bigint ->
  Lemma (requires (carried_3 h0 b /\ carriedTopBottom h0 h1 b))
	(ensures  (carried_3 h0 b /\ carriedTopBottom h0 h1 b
	  /\ eval h1 b norm_length % reveal prime = eval h0 b (norm_length+1) % reveal prime
	  /\ carried_4 h1 b))
let lemma_carry_top_2 h0 h1 b =
  lemma_carry_top_20 h0 h1 b;
  lemma_carry_top_11 h0 h1 b


#reset-options "--z3rlimit 5 --initial_fuel 0 --max_fuel 0"

let isCarried01 (h0:mem) (h1:mem) (b:bigint) =
  let open Hacl.UInt64 in
  live h0 b /\ live h1 b
  /\ v (get h1 b 0) = v (get h0 b 0) % pow2 51
  /\ v (get h1 b 1) = v (get h0 b 1) + (v (get h0 b 0) / pow2 51)
  /\ v (get h1 b 2) = v (get h0 b 2)
  /\ v (get h1 b 3) = v (get h0 b 3)
  /\ v (get h1 b 4) = v (get h0 b 4)

val lemma_div_lt2: a:nat -> b:pos{a < b} -> Lemma (a / b = 0)
let lemma_div_lt2 a b = ()


let lemma_norm_5 h (b:bigint) :
  Lemma (requires (let open Hacl.UInt64 in live h b /\ v (get h b 0) < pow2 51 /\ v (get h b 1) < pow2 51
    /\ v (get h b 2) < pow2 51 /\ v (get h b 3) < pow2 51 /\ v (get h b 4) < pow2 51))
    (ensures (norm h b))
    = ()


#reset-options "--z3rlimit 10 --initial_fuel 0 --max_fuel 0"

val lemma_carry_0_to_10:
  h0:mem -> h1:mem ->
  b:bigint ->
  Lemma (requires (carried_4 h0 b /\ isCarried01 h0 h1 b))
	(ensures  (carried_4 h0 b /\ isCarried01 h0 h1 b /\ norm h1 b))
let lemma_carry_0_to_10 h0 h1 b =
  let open Hacl.UInt64 in
  assert_norm (pow2 5 = 32);
  pow2_lt_compat 51 5;
  pow2_double_sum 51;
  lemma_div_lt (v (get h0 b 0)) 52 51;
  if (v (get h0 b 0) >= pow2 51) then (
    assert(v (get h0 b 1) < pow2 1);
    lemma_div_rest (v (get h0 b 0)) 5 51 )
  else lemma_div_lt2 (v (get h0 b 0)) (pow2 51);
  lemma_eval_bigint_5 h0 b;
  lemma_eval_bigint_5 h1 b;
  pow2_lt_compat 32 1;
  pow2_double_sum 32;
  pow2_lt_compat 51 33;
  lemma_mod_0 (v (get h0 b 0)) (pow2 51);
  cut(v (get h1 b 0) < pow2 51);
  cut(v (get h1 b 1) < pow2 51);
  cut(v (get h1 b 2) < pow2 51);
  cut(v (get h1 b 3) < pow2 51);
  cut(v (get h1 b 4) < pow2 51);
  lemma_norm_5 h1 b


val lemma_carry_0_to_11:
  h0:mem -> h1:mem ->
  b:bigint ->
  Lemma (requires (carried_4 h0 b /\ isCarried01 h0 h1 b))
	(ensures  (carried_4 h0 b /\ isCarried01 h0 h1 b /\ eval h1 b norm_length = eval h0 b norm_length))
let lemma_carry_0_to_11 h0 h1 b =
  let open Hacl.UInt64 in
  lemma_eval_bigint_5 h0 b;
  lemma_eval_bigint_5 h1 b;
  cut (eval h1 b 5 =
    v (get h1 b 0) + pow2 51 * v (get h1 b 1) + pow2 102 * v (get h1 b 2)
		   + pow2 153 * v (get h1 b 3) + pow2 204 * v (get h1 b 4));
  cut (eval h1 b 5 =
    v (get h0 b 0) % pow2 51 + pow2 51 * (v (get h0 b 1) + v (get h0 b 0) / pow2 51)
      + pow2 102 * v (get h0 b 2) + pow2 153 * v (get h0 b 3) + pow2 204 * v (get h0 b 4));
  distributivity_add_right (pow2 51) (v (get h0 b 1)) (v (get h0 b 0) / pow2 51);
  cut (eval h1 b 5 =
    v (get h0 b 0) % pow2 51 + pow2 51 * (v (get h0 b 0) / pow2 51) + pow2 51 * (v (get h0 b 1))
      + pow2 102 * v (get h0 b 2) + pow2 153 * v (get h0 b 3) + pow2 204 * v (get h0 b 4));
  lemma_div_mod (v (get h0 b 0)) (pow2 51)


val lemma_carry_0_to_1:
  h0:mem -> h1:mem ->
  b:bigint ->
  Lemma (requires (carried_4 h0 b /\ isCarried01 h0 h1 b))
	(ensures  (carried_4 h0 b /\ isCarried01 h0 h1 b
	  /\ norm h1 b
	  /\ eval h1 b norm_length = eval h0 b norm_length))
let lemma_carry_0_to_1 h0 h1 b =
  lemma_carry_0_to_10 h0 h1 b;
  lemma_carry_0_to_11 h0 h1 b

