module Hacl.EC.Curve25519.Bignum.Modulo.Lemmas

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


#reset-options "--z3timeout 5 --initial_fuel 0 --max_fuel 0"

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


#reset-options "--z3timeout 5 --initial_fuel 0 --max_fuel 0"

val lemma_modulo_9_0: f:nat -> g:nat -> h:nat -> i:nat -> Lemma
  (let p = reveal prime in
    (pow2 255 * f + pow2 306 * g + pow2 357 * h + pow2 408 * i) % p
	   =  ((pow2 255 * f + pow2 306 * g) % p + (pow2 357 * h + pow2 408 * i) % p) % p)
let lemma_modulo_9_0 f g h i =
  let p = reveal prime in
  lemma_modulo_add (pow2 255 * f + pow2 306 * g)  (pow2 357 * h + pow2 408 * i) p;
  lemma_modulo_add (pow2 357 * h + pow2 408 * i)  ((pow2 255 * f + pow2 306 * g) % p) p


val lemma_modulo_9_1: f:nat -> g:nat -> h:nat -> i:nat -> Lemma
  (let p = reveal prime in
	 ((pow2 255 * f + pow2 306 * g) % p = ((pow2 255 * f) % p + (pow2 306 * g) % p) % p
	 /\  (pow2 357 * h + pow2 408 * i) % p =  ((pow2 357 * h) % p + (pow2 408 * i) % p) % p))
let lemma_modulo_9_1 f g h i =
  let p = reveal prime in
  lemma_modulo_add (pow2 255 * f)  (pow2 306 * g) p;
  lemma_modulo_add (pow2 306 * g)  ((pow2 255 * f)%p) p;
  lemma_modulo_add (pow2 357 * h)  (pow2 408 * i) p;
  lemma_modulo_add (pow2 408 * i)  ((pow2 357 * h)%p) p


#reset-options "--z3timeout 20 --initial_fuel 0 --max_fuel 0"

val lemma_modulo_9_2: f:nat -> g:nat -> h:nat -> i:nat -> Lemma
  (let p = reveal prime in
	 ((pow2 255 * f + pow2 306 * g) % p = ((pow2 255 % p) * f + (pow2 306 % p) * g) % p
	 /\  (pow2 357 * h + pow2 408 * i) % p =  ((pow2 357 % p) * h + (pow2 408 % p) * i) % p))
let lemma_modulo_9_2 f g h i =
  let p = reveal prime in
  lemma_modulo_9_1 f g h i;
  lemma_modulo_mul (pow2 255)  f p;
  lemma_modulo_mul (pow2 306)  g p;
  lemma_modulo_mul (pow2 357)  h p;
  lemma_modulo_mul (pow2 408)  i p;
  lemma_modulo_add ((pow2 255 % p) * f)  ((pow2 306 % p) * g) p;
  lemma_modulo_add ((pow2 306 % p) * g)  (((pow2 255 % p) * f)%p) p;
  lemma_modulo_add ((pow2 357%p) * h)  ((pow2 408%p) * i) p;
  lemma_modulo_add ((pow2 408%p) * i)  (((pow2 357%p) * h)%p) p


#reset-options "--z3timeout 20 --initial_fuel 0 --max_fuel 0"

val lemma_modulo_9_3: f:nat -> g:nat -> h:nat -> i:nat -> Lemma
  (let p = reveal prime in
    (pow2 255 * f + pow2 306 * g + pow2 357 * h + pow2 408 * i) % p
	   =  ((pow2 255 % p) * f + (pow2 306 % p) * g + (pow2 357 % p) * h + (pow2 408 % p) * i) % p)
let lemma_modulo_9_3 f g h i =
  let p = reveal prime in
  lemma_modulo_9_0 f g h i;
  lemma_modulo_9_2 f g h i;
  lemma_modulo_add ((pow2 255 %p) * f + (pow2 306 % p) * g)  ((pow2 357 % p) * h + (pow2 408 % p) * i) p;
  lemma_modulo_add ((pow2 357 % p) * h + (pow2 408 % p) * i)  (((pow2 255 % p) * f + (pow2 306%p) * g) % p) p


#reset-options "--z3timeout 20 --initial_fuel 0 --max_fuel 0"

val lemma_modulo_9: a:nat -> b:nat -> c:nat -> d:nat -> e:nat -> f:nat -> g:nat -> h:nat -> i:nat ->
  Lemma (requires (True))
	(ensures  (let p = reveal prime in
	  (a + pow2 51 * b + pow2 102 * c + pow2 153 * d + pow2 204 * e
	   + pow2 255 * f + pow2 306 * g + pow2 357 * h + pow2 408 * i ) % p
	  = (a + pow2 51 * b + pow2 102 * c + pow2 153 * d + pow2 204 * e
	     + (pow2 255 % p) * f + (pow2 306 % p) * g + (pow2 357 % p) * h + (pow2 408 % p) * i) % p))
let lemma_modulo_9 a b c d e f g h i =
  let p = reveal prime in
  nat_times_nat_is_nat (pow2 51)  b;
  nat_times_nat_is_nat (pow2 102)  c;
  nat_times_nat_is_nat (pow2 153)  d;
  nat_times_nat_is_nat (pow2 204) e;
  nat_times_nat_is_nat (pow2 255) f;
  nat_times_nat_is_nat (pow2 306) g;
  nat_times_nat_is_nat (pow2 357) h;
  nat_times_nat_is_nat (pow2 408) i;
  let m0 = (pow2 255 * f + pow2 306 * g + pow2 357 * h + pow2 408 * i) in
  let m1 = (a + pow2 51 * b + pow2 102 * c + pow2 153 * d + pow2 204 * e) in
  lemma_modulo_add m0 m1 p;
  cut( (m1 +m0) % p = (m1 + (m0%p)) % p);
  lemma_modulo_9_3 f g h i;
  nat_times_nat_is_nat (pow2 255 % p) f;
  nat_times_nat_is_nat (pow2 306 % p) g;
  nat_times_nat_is_nat (pow2 357 % p) h;
  nat_times_nat_is_nat (pow2 204 % p) i;
  let m2 = (pow2 255 % p) * f + (pow2 306 % p) * g + (pow2 357 % p) * h + (pow2 408 % p) * i in
  cut (m0 % p = m2 % p);
  cut (m0 % p = ((pow2 255 % p) * f + (pow2 306 % p) * g + (pow2 357 % p) * h + (pow2 408 % p) * i) % p);
  lemma_modulo_add m2 m1 p


#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 20"

private val lemma_2_255m19_val: n:nat -> Lemma (requires (n = 255))
                                              (ensures (pow2 n - 19 > 0))
                                              [SMTPat (pow2 n - 19)]
let lemma_2_255m19_val n = assert_norm (pow2 255 - 19 > 0)

val lemma_2_255_modulo_prime: unit -> Lemma (pow2 255 - 19 > 0 /\ pow2 255 % (pow2 255 - 19) = 19)
let lemma_2_255_modulo_prime () =
  assert_norm(pow2 255 % (pow2 255 - 19) = 19)


#reset-options "--z3timeout 5 --initial_fuel 0 --max_fuel 0"


let isDegreeReduced (h0:mem) (h1:mem) (b:bigint_wide) =
  live h0 b /\ live h1 b /\ length b >= 2*norm_length-1
  /\ (let open Hacl.UInt128 in
  v (get h1 b 0) = v (get h0 b 0) + 19 * v (get h0 b 5)
  /\ v (get h1 b 1) = v (get h0 b 1) + 19 * v (get h0 b 6)
  /\ v (get h1 b 2) = v (get h0 b 2) + 19 * v (get h0 b 7)
  /\ v (get h1 b 3) = v (get h0 b 3) + 19 * v (get h0 b 8)
  /\ v (get h1 b 4) = v (get h0 b 4))


let satisfiesModuloConstraints (h:heap) (b:bigint_wide) : GTot Type0 =
  live h b /\ length b >= 2*norm_length-1
  /\ maxValue_wide h b (2*norm_length-1) * 20 < pow2 127


val lemma_freduce_degree_0:
  h:mem ->
  b:bigint_wide ->
  Lemma (requires (satisfiesModuloConstraints h b))
	(ensures  (satisfiesModuloConstraints h b
          /\ (let open Hacl.UInt128 in
	  19 * v (get h b 5) < pow2 128 /\ 19 * v (get h b 6) < pow2 128 /\ 19 * v (get h b 7) < pow2 128
	  /\ 19 * v (get h b 7) < pow2 128 /\ 19 * v (get h b 8) < pow2 128
	  /\ v (get h b 0) + 19 * v (get h b 5) < pow2 128 /\ v (get h b 1) + 19 * v (get h b 6) < pow2 128
	  /\ v (get h b 2) + 19 * v (get h b 7) < pow2 128 /\ v (get h b 3) + 19 * v (get h b 8) < pow2 128)))
let lemma_freduce_degree_0 h b =
  pow2_double_sum 127;
  maxValue_wide_lemma_aux h b (2*norm_length-1)


let bound127 (h:heap) (b:bigint_wide) : GTot Type0 =
  let open Hacl.UInt128 in
  live h b /\ v (get h b 0) < pow2 127 /\ v (get h b 1) < pow2 127 /\ v (get h b 2) < pow2 127
  /\ v (get h b 3) < pow2 127 /\ v (get h b 4) < pow2 127


#reset-options "--z3timeout 5 --initial_fuel 0 --max_fuel 0"

val lemma_freduce_degree1:
  h0:mem -> h1:mem ->
  b:bigint_wide ->
  Lemma (requires (satisfiesModuloConstraints h0 b /\ isDegreeReduced h0 h1 b))
	(ensures  (satisfiesModuloConstraints h0 b /\ isDegreeReduced h0 h1 b
	  /\ bound127 h1 b))
let lemma_freduce_degree1 h0 h1 b =
  maxValue_wide_lemma_aux h0 b (2*norm_length-1)


let lemma_modulo_00 (a:nat) (b:pos) : Lemma (requires (a < b)) (ensures ( a % b = a )) = ()
let lemma_mul_nat (a:nat) (b:nat) : Lemma (a * b >= 0) = ()


let lemma_pow2_modulo_prime0 () :
  Lemma (let p = reveal prime in (
    (19 * pow2 51) % p = 19 * pow2 51
    /\ (19 * pow2 102) % p = 19 * pow2 102
    /\ (19 * pow2 153) % p = 19 * pow2 153))
  = assert_norm((19 * pow2 51) % (pow2 255 - 19) = 19 * pow2 51);
    assert_norm((19 * pow2 102) % (pow2 255 - 19) = 19 * pow2 102);
    assert_norm((19 * pow2 153) % (pow2 255 - 19) = 19 * pow2 153)


let lemma_pow2_modulo_prime () : Lemma (let p = reveal prime in
  pow2 255 % p = 19 /\ pow2 306 % p = 19 * pow2 51
  /\ pow2 357 % p = 19 * pow2 102 /\ pow2 408 % p = 19 * pow2 153)
  = assert_norm(pow2 255 % (pow2 255 - 19) = 19);
    assert_norm(pow2 306 % (pow2 255 - 19) = 19 * pow2 51);
    assert_norm(pow2 357 % (pow2 255 - 19) = 19 * pow2 102);
    assert_norm(pow2 408 % (pow2 255 - 19) = 19 * pow2 153)


let lemma_2_51_p (a:nat) : Lemma (requires (a < pow2 51)) (ensures  (a < reveal prime /\ a % reveal prime = a))
  = assert_norm(pow2 51 < pow2 255 - 19);
    modulo_lemma a (pow2 255 - 19)


#reset-options "--z3timeout 100 --initial_fuel 0 --max_fuel 0"


val lemma_freduce_degree2:
  h0:mem -> h1:mem ->
  b:bigint_wide ->
  Lemma (requires (isDegreeReduced h0 h1 b))
	(ensures  (isDegreeReduced h0 h1 b
	  /\ eval_wide h1 b norm_length % reveal prime = eval_wide h0 b (2*norm_length-1) % reveal prime))
let lemma_freduce_degree2 h0 h1 b =
  let open Hacl.UInt128 in
  let b0 = v (get h0 b 0) in
  let b1 = v (get h0 b 1) in
  let b2 = v (get h0 b 2) in
  let b3 = v (get h0 b 3) in
  let b4 = v (get h0 b 4) in
  let b5 = v (get h0 b 5) in
  let b6 = v (get h0 b 6) in
  let b7 = v (get h0 b 7) in
  let b8 = v (get h0 b 8) in
  lemma_eval_bigint_wide_9 h0 b;
  let p = reveal prime in
  cut(eval_wide h0 b (2*norm_length-1) % p =
      (b0 + pow2 51 * b1 + pow2 102 * b2 + pow2 153 * b3 + pow2 204 * b4
      + pow2 255 * b5 + pow2 306 * b6 + pow2 357 * b7 + pow2 408 * b8) % p);
  lemma_eval_bigint_wide_5 h1 b;
  lemma_mul_nat (pow2 51)  b1;
  lemma_mul_nat (pow2 102)  b2;
  lemma_mul_nat (pow2 153)  b3;
  lemma_mul_nat (pow2 204) b4;
  lemma_mul_nat (pow2 255) b5;
  lemma_mul_nat (pow2 306) b6;
  lemma_mul_nat (pow2 357) b7;
  lemma_mul_nat (pow2 408) b8;
  lemma_modulo_9 b0 b1 b2 b3 b4 b5 b6 b7 b8;
  distributivity_add_right (pow2 51) b1 (5*b6);
  distributivity_add_right (pow2 102) b2 (5*b7);
  distributivity_add_right (pow2 153) b3 (5*b8);
  let p = reveal prime in
  lemma_modulo_mul (pow2 255) b5 p;
  lemma_modulo_mul (pow2 306) b6 p;
  lemma_modulo_mul (pow2 357) b7 p;
  lemma_modulo_mul (pow2 408) b8 p;
  lemma_pow2_modulo_prime ()


#reset-options "--z3timeout 20 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

val lemma_freduce_degree:
  h0:mem ->
  h1:mem ->
  b:bigint_wide ->
  Lemma (requires (satisfiesModuloConstraints h0 b /\ isDegreeReduced h0 h1 b))
	(ensures  (satisfiesModuloConstraints h0 b /\ isDegreeReduced h0 h1 b
	  /\ bound127 h1 b
	  /\ eval_wide h1 b norm_length % reveal prime = eval_wide h0 b (2*norm_length-1) % reveal prime))
let lemma_freduce_degree h0 h1 b =
  lemma_freduce_degree1 h0 h1 b;
  lemma_freduce_degree2 h0 h1 b


#reset-options "--z3timeout 20 --initial_fuel 0 --max_fuel 0"

let isCarried (h0:mem) (h1:mem) (b:bigint_wide) : GTot Type0 =
  live h0 b /\ live h1 b /\ length b >= norm_length+1
  /\ ( let open Hacl.UInt128 in
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

#reset-options "--z3timeout 20 --initial_fuel 0 --max_fuel 0"


module H128 = Hacl.UInt128


let u127 = x:H128.t{H128.v x < pow2 127}


#reset-options "--z3timeout 5 --initial_fuel 0 --max_fuel 0"


let isCarried_
  (h1:mem)
  (b0:H128.t) (b1:H128.t) (b2:H128.t) (b3:H128.t) (b4:H128.t)
  (b:bigint_wide) : GTot Type0 =
  live h1 b /\ length b >= norm_length+1
  /\ ( let open Hacl.UInt128 in
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


let carried_1 (h:mem) (b:bigint_wide) : GTot Type0 =
  live h b /\ length b >= norm_length+1
  /\ (let open Hacl.UInt128 in
  v (get h b 0) < pow2 51
  /\ v (get h b 1) < pow2 51
  /\ v (get h b 2) < pow2 51
  /\ v (get h b 3) < pow2 51
  /\ v (get h b 4) < pow2 51
  /\ v (get h b 5) <= pow2 77)


#reset-options "--z3timeout 5 --initial_fuel 0 --max_fuel 0"

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
let lemma_carry_10_2 (x:nat) : Lemma (requires (x < pow2 128)) (ensures (x / pow2 51 <= pow2 77))
  = pow2_minus 128 51;
    lemma_carry_10_1 x (pow2 128) (pow2 51)


val lemma_carry_10:
  h0:mem -> h1:mem ->
  b:bigint_wide{length b >= norm_length+1} ->
  Lemma (requires (bound127 h0 b /\ isCarried h0 h1 b))
	(ensures  (carried_1 h1 b))
let lemma_carry_10 h0 h1 b =
  let open Hacl.UInt128 in
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
  pow2_double_sum 127;
  pow2_lt_compat 127 51;
  pow2_lt_compat 127 77;
  lemma_carry_10_2 b0;
  lemma_carry_10_2 (b1+r0);
  lemma_carry_10_2 (b2+r1);
  lemma_carry_10_2 (b3+r2);
  lemma_carry_10_2 (b4+r3)


#reset-options "--z3timeout 5 --initial_fuel 0 --max_fuel 0"

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


#reset-options "--z3timeout 20 --initial_fuel 0 --max_fuel 0"

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


#reset-options "--z3timeout 5 --initial_fuel 0 --max_fuel 0"

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


#reset-options "--z3timeout 5 --initial_fuel 0 --max_fuel 0"

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


#reset-options "--z3timeout 20 --initial_fuel 0 --max_fuel 0"

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


#reset-options "--z3timeout 5 --initial_fuel 0 --max_fuel 0"

val lemma_carry_11:
  h0:mem -> h1:mem ->
  b:bigint_wide{length b >= norm_length+1} ->
  Lemma (requires (isCarried h0 h1 b))
	(ensures  (isCarried h0 h1 b
	  /\ eval_wide h1 b (norm_length+1) = eval_wide h0 b norm_length))
let lemma_carry_11 h0 h1 b =
  let (p51:pos) = pow2 51 in
  lemma_eval_bigint_wide_5 h0 b;
  lemma_eval_bigint_wide_6 h1 b;
  let open Hacl.UInt128 in
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
  cut(eval_wide h1 b 6 = v (get h1 b 0) + pow2 51  * v (get h1 b 1) + pow2 102  * v (get h1 b 2)
	       + pow2 153  * v (get h1 b 3) + pow2 204 * v (get h1 b 4) + pow2 255 * v (get h1 b 5));
  cut (v (get h1 b 0) = b0 % p51);
  cut (v (get h1 b 1) = ((b0 / p51 + b1) % p51));
  cut (v (get h1 b 2) = (((b0 / p51 + b1) / p51 + b2) % p51));
  cut (v (get h1 b 3) = ((((b0 / p51 + b1) / p51 + b2) / p51 + b3) % p51));
  cut (v (get h1 b 4) = (((((b0 / p51 + b1) / p51 + b2) / p51 + b3) / p51 + b4) % pow2 51) );
  cut (v (get h1 b 5) = (((((b0 / p51 + b1) / p51 + b2) / p51 + b3) / p51 + b4) / pow2 51) );
  lemma_carry_110 b0 b1 b2 b3 b4 (v (get h1 b 0)) (v (get h1 b 1)) (v (get h1 b 2)) (v (get h1 b 3)) (v (get h1 b 4)) (v (get h1 b 5))


#reset-options "--z3timeout 5 --initial_fuel 0 --max_fuel 0"

val lemma_carry_1:
  h0:mem -> h1:mem ->
  b:bigint_wide{length b >= norm_length+1} ->
  Lemma (requires (bound127 h0 b /\ isCarried h0 h1 b))
	(ensures  (bound127 h0 b /\ isCarried h0 h1 b
	  /\ eval_wide h1 b (norm_length+1) = eval_wide h0 b norm_length
	  /\ carried_1 h1 b))
let lemma_carry_1 h0 h1 b =
  lemma_carry_10 h0 h1 b;
  lemma_carry_11 h0 h1 b


#reset-options "--z3timeout 5 --initial_fuel 0 --max_fuel 0"

let carried_2 (h:mem) (b:bigint_wide) : GTot Type0 =
  let open Hacl.UInt128 in
  live h b /\ length b >= norm_length+1
  /\ v (get h b 0) < pow2 83
  /\ v (get h b 1) < pow2 51
  /\ v (get h b 2) < pow2 51
  /\ v (get h b 3) < pow2 51
  /\ v (get h b 4) < pow2 51


let carried_3 (h:mem) (b:bigint_wide) : GTot Type0 =
  let open Hacl.UInt128 in
  norm_wide h b /\ length b >= norm_length+1
  /\ v (get h b 5) <= 1
  /\ (v (get h b 5) = 1
    ==> (v (get h b 1) < pow2 32 /\ v (get h b 2) < pow2 32  /\ v (get h b 3) < pow2 32
	/\ v (get h b 4) < pow2 32))


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


#reset-options "--z3timeout 20 --initial_fuel 0 --max_fuel 0"

val lemma_carry_20:
  h0:mem -> h1:mem ->
  b:bigint_wide{length b >= norm_length+1} ->
  Lemma (requires (carried_2 h0 b /\ isCarried h0 h1 b))
	(ensures  (carried_2 h0 b /\ isCarried h0 h1 b /\ carried_3 h1 b))
let lemma_carry_20 h0 h1 b =
  let open Hacl.UInt128 in
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
  lemma_carry_10_1 b0 (pow2 83) (pow2 51);
  lemma_div_lt b0 83 51;
  assert(r0 < pow2 32);
  pow2_lt_compat 51 32;
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
  pow2_lt_compat 32 1;
  if (v (get h1 b 5) = 1) then (
    lemma_div_rest (b1 + r0) 32 51;
    lemma_div_rest (b2 + r1) 32 51;
    lemma_div_rest (b3 + r2) 32 51;
    lemma_div_rest (b4 + r3) 32 51
  )


#reset-options "--z3timeout 5 --initial_fuel 0 --max_fuel 0"

val lemma_carry_2:
  h0:mem -> h1:mem ->
  b:bigint_wide{length b >= norm_length+1} ->
  Lemma (requires (carried_2 h0 b /\ isCarried h0 h1 b))
	(ensures  (carried_2 h0 b /\ isCarried h0 h1 b
	  /\ eval_wide h1 b (norm_length+1) = eval_wide h0 b norm_length
	  /\ carried_3 h1 b))
let lemma_carry_2 h0 h1 b =
  lemma_carry_20 h0 h1 b;
  lemma_carry_11 h0 h1 b


#reset-options "--z3timeout 20 --initial_fuel 0 --max_fuel 0"


let carriedTopBottom (h0:mem) (h1:mem) (b:bigint_wide) : GTot Type0 =
  let open Hacl.UInt128 in
  live h0 b /\ live h1 b /\ length b >= norm_length+1
  /\ v (get h1 b 0) = v (get h0 b 0) + 19 * v (get h0 b 5)
  /\ v (get h1 b 1) = v (get h0 b 1)
  /\ v (get h1 b 2) = v (get h0 b 2)
  /\ v (get h1 b 3) = v (get h0 b 3)
  /\ v (get h1 b 4) = v (get h0 b 4)


val lemma_carry_top_10:
  h0:mem -> h1:mem ->
  b:bigint_wide ->
  Lemma (requires (carried_1 h0 b /\ carriedTopBottom h0 h1 b))
	(ensures  (carried_1 h0 b /\ carriedTopBottom h0 h1 b /\ carried_2 h1 b))
let lemma_carry_top_10 h0 h1 b =
  assert_norm(pow2 5 = 32);
  pow2_plus 5 77;
  pow2_lt_compat 82 51;
  pow2_double_sum 82


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
  b:bigint_wide ->
  Lemma (requires (carriedTopBottom h0 h1 b))
	(ensures  (carriedTopBottom h0 h1 b
	  /\ eval_wide h1 b norm_length % reveal prime = eval_wide h0 b (norm_length+1) % reveal prime))
let lemma_carry_top_11 h0 h1 b =
  lemma_eval_bigint_wide_6 h0 b;
  lemma_eval_bigint_wide_5 h1 b;
  let open Hacl.UInt128 in
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
  b:bigint_wide ->
  Lemma (requires (carried_1 h0 b /\ carriedTopBottom h0 h1 b))
	(ensures  (carried_1 h0 b /\ carriedTopBottom h0 h1 b
	  /\ carried_2 h1 b
	  /\ eval_wide h1 b norm_length % reveal prime = eval_wide h0 b (norm_length+1) % reveal prime))
let lemma_carry_top_1 h0 h1 b =
  lemma_carry_top_10 h0 h1 b;
  lemma_carry_top_11 h0 h1 b


let carried_4 (h:mem) (b:bigint_wide) : GTot Type0 =
  let open Hacl.UInt128 in
  live h b /\ v (get h b 0) < pow2 51 + 19
  /\ v (get h b 1) < pow2 51
  /\ (v (get h b 0) >= pow2 51 ==> v (get h b 1) < pow2 32)
  /\ v (get h b 2) < pow2 51
  /\ v (get h b 3) < pow2 51
  /\ v (get h b 4) < pow2 51


#reset-options "--z3timeout 5 --initial_fuel 0 --max_fuel 0"

val lemma_carry_top_20:
  h0:mem -> h1:mem ->
  b:bigint_wide ->
  Lemma (requires (carried_3 h0 b /\ carriedTopBottom h0 h1 b))
	(ensures  (carried_3 h0 b /\ carried_4 h1 b))
let lemma_carry_top_20 h0 h1 b = ()


#reset-options "--z3timeout 5 --initial_fuel 0 --max_fuel 0"

val lemma_carry_top_2:
  h0:mem -> h1:mem ->
  b:bigint_wide ->
  Lemma (requires (carried_3 h0 b /\ carriedTopBottom h0 h1 b))
	(ensures  (carried_3 h0 b /\ carriedTopBottom h0 h1 b
	  /\ eval_wide h1 b norm_length % reveal prime = eval_wide h0 b (norm_length+1) % reveal prime
	  /\ carried_4 h1 b))
let lemma_carry_top_2 h0 h1 b =
  lemma_carry_top_20 h0 h1 b;
  lemma_carry_top_11 h0 h1 b


#reset-options "--z3timeout 5 --initial_fuel 0 --max_fuel 0"

let isCarried01 (h0:mem) (h1:mem) (b:bigint_wide) =
  let open Hacl.UInt128 in
  live h0 b /\ live h1 b
  /\ v (get h1 b 0) = v (get h0 b 0) % pow2 51
  /\ v (get h1 b 1) = v (get h0 b 1) + (v (get h0 b 0) / pow2 51)
  /\ v (get h1 b 2) = v (get h0 b 2)
  /\ v (get h1 b 3) = v (get h0 b 3)
  /\ v (get h1 b 4) = v (get h0 b 4)

val lemma_div_lt2: a:nat -> b:pos{a < b} -> Lemma (a / b = 0)
let lemma_div_lt2 a b = ()


let lemma_norm_5 h (b:bigint_wide) :
  Lemma (requires (let open Hacl.UInt128 in live h b /\ v (get h b 0) < pow2 51 /\ v (get h b 1) < pow2 51
    /\ v (get h b 2) < pow2 51 /\ v (get h b 3) < pow2 51 /\ v (get h b 4) < pow2 51))
    (ensures (norm_wide h b))
    = ()


#reset-options "--z3timeout 10 --initial_fuel 0 --max_fuel 0"

val lemma_carry_0_to_10:
  h0:mem -> h1:mem ->
  b:bigint_wide ->
  Lemma (requires (carried_4 h0 b /\ isCarried01 h0 h1 b))
	(ensures  (carried_4 h0 b /\ isCarried01 h0 h1 b /\ norm_wide h1 b))
let lemma_carry_0_to_10 h0 h1 b =
  let open Hacl.UInt128 in
  assert_norm (pow2 5 = 32);
  pow2_lt_compat 51 5;
  pow2_double_sum 51;
  lemma_div_lt (v (get h0 b 0)) 52 51;
  if (v (get h0 b 0) >= pow2 51) then (
    assert(v (get h0 b 1) < pow2 32);
    lemma_div_rest (v (get h0 b 0)) 5 51 )
  else lemma_div_lt2 (v (get h0 b 0)) (pow2 51);
  lemma_eval_bigint_wide_5 h0 b;
  lemma_eval_bigint_wide_5 h1 b;
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
  b:bigint_wide ->
  Lemma (requires (carried_4 h0 b /\ isCarried01 h0 h1 b))
	(ensures  (carried_4 h0 b /\ isCarried01 h0 h1 b /\ eval_wide h1 b norm_length = eval_wide h0 b norm_length))
let lemma_carry_0_to_11 h0 h1 b =
  let open Hacl.UInt128 in
  lemma_eval_bigint_wide_5 h0 b;
  lemma_eval_bigint_wide_5 h1 b;
  cut (eval_wide h1 b 5 =
    v (get h1 b 0) + pow2 51 * v (get h1 b 1) + pow2 102 * v (get h1 b 2)
		   + pow2 153 * v (get h1 b 3) + pow2 204 * v (get h1 b 4));
  cut (eval_wide h1 b 5 =
    v (get h0 b 0) % pow2 51 + pow2 51 * (v (get h0 b 1) + v (get h0 b 0) / pow2 51)
      + pow2 102 * v (get h0 b 2) + pow2 153 * v (get h0 b 3) + pow2 204 * v (get h0 b 4));
  distributivity_add_right (pow2 51) (v (get h0 b 1)) (v (get h0 b 0) / pow2 51);
  cut (eval_wide h1 b 5 =
    v (get h0 b 0) % pow2 51 + pow2 51 * (v (get h0 b 0) / pow2 51) + pow2 51 * (v (get h0 b 1))
      + pow2 102 * v (get h0 b 2) + pow2 153 * v (get h0 b 3) + pow2 204 * v (get h0 b 4));
  lemma_div_mod (v (get h0 b 0)) (pow2 51)


val lemma_carry_0_to_1:
  h0:mem -> h1:mem ->
  b:bigint_wide ->
  Lemma (requires (carried_4 h0 b /\ isCarried01 h0 h1 b))
	(ensures  (carried_4 h0 b /\ isCarried01 h0 h1 b
	  /\ norm_wide h1 b
	  /\ eval_wide h1 b norm_length = eval_wide h0 b norm_length))
let lemma_carry_0_to_1 h0 h1 b =
  lemma_carry_0_to_10 h0 h1 b;
  lemma_carry_0_to_11 h0 h1 b

