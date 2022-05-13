module Spec.ECC.Curves

open FStar.Mul

open Lib.ByteSequence
open Lib.IntTypes
open Lib.Sequence

open FStar.Math.Lemmas
open FStar.Math.Lib

#set-options "--fuel 0 --ifuel 0 --z3rlimit 100"


(** Operations for the computations **) 
type elem (n:pos) = x:nat{x < n}

let fmul (#n:pos) (x:elem n) (y:elem n) : elem n = (x * y) % n

val exp: #n: pos -> a: nat {a < n} -> b: pos -> Tot (r: nat{r < n}) (decreases b)

let rec exp #n a b =
  if b = 1 then a
  else
    if b % 2 = 0 then exp #n (fmul #n a a) (b / 2)
    else fmul #n a (exp #n (fmul #n a a) (b / 2))


noextract
val pow: a: nat -> b: nat -> nat

let rec pow a b =
  if b = 0 then 1
  else a * (pow a (b - 1))


#push-options "--fuel 1"

val power_as_specification_same_as_fermat: a: nat -> b: nat -> Lemma (pow a b == FStar.Math.Fermat.pow a b)

let rec power_as_specification_same_as_fermat a b = 
  match b with 
  |0 -> ()
  |_ -> power_as_specification_same_as_fermat a (b - 1)


noextract
val pow_plus: a: nat -> b: nat -> c: nat -> 
  Lemma (ensures (pow a b * pow a c = pow a (b + c))) 
  (decreases b)

let rec pow_plus a b c = 
  match b with 
  | 0 -> assert_norm (pow a 0 = 1)
  | _ -> pow_plus a (b - 1) c

#pop-options


noextract
let modp_inv_prime (prime: pos {prime > 3}) (x: elem prime) : Tot (elem prime) =
  exp #prime x (prime - 2)

noextract
let modp_inv2_prime (x: int) (p: nat {p > 3}) : Tot (elem p) = modp_inv_prime p (x % p)


(** The main instantiation of curves **) 
(* https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.186-4.pdf *)
type curve = 
  |P256
  |P384


let invert_state_s (a: curve): Lemma
  (requires True)
  (ensures (inversion curve))
  [SMTPat (curve) ]
  = allow_inversion (curve)


(** Curve parameters **)

let prime256: (a: pos {a > 3 && a < pow2 256}) =
  assert_norm (pow2 256 - pow2 224 + pow2 192 + pow2 96 -1 > 3);
  assert_norm (pow2 256 - pow2 224 + pow2 192 + pow2 96 -1 < pow2 256);
  pow2 256 - pow2 224 + pow2 192 + pow2 96 - 1

let prime384: (a: pos {a > 3 && a < pow2 384}) = 
  assert_norm(pow2 384 - pow2 128 - pow2 96 + pow2 32 - 1 > 3);
  assert_norm(pow2 384 - pow2 128 - pow2 96 + pow2 32 - 1 < pow2 384);
  pow2 384 - pow2 128 - pow2 96 + pow2 32 - 1



(*
proof that the values are primes in Sage: 
>> is_prime(2**256 - 2**224 + 2**192 + 2**96 -1)
True

>> is_prime(2**384 - 2**128 - 2**96 + 2**32 - 1) 
True

*)

inline_for_extraction
let getPrime curve : prime: pos {prime > 3 /\ FStar.Math.Euclid.is_prime prime /\ prime > pow2 64} = 
  match curve with 
  |P256 -> assert_norm(prime256 > pow2 64); assume (FStar.Math.Euclid.is_prime prime256); prime256
  |P384 -> assert_norm(prime384 > pow2 64); assume (FStar.Math.Euclid.is_prime prime384);  prime384


(* the length of each coordinate of the point as uint64 *)
inline_for_extraction noextract
val getCoordinateLenU64: c: curve -> Tot (a: size_t {v a * 20 < maxint U32})

let getCoordinateLenU64 curve = 
  match curve with
  |P256 -> 4ul
  |P384 -> 6ul  
  |_ -> 4ul


(* the length of the point as uint64 *)
inline_for_extraction noextract
val getPointLenU64: c: curve -> Tot size_t

let getPointLenU64 curve = 
  getCoordinateLenU64 curve *. 3ul 


(* the length of each coordinate of the point as uint8 *)
inline_for_extraction noextract
let getCoordinateLenU curve = getCoordinateLenU64 curve *! 8ul

let getCoordinateLen curve : pos = v (getCoordinateLenU curve)

(* each point consists of three coordinates *)
let getPointLen curve = getCoordinateLenU curve *! 3ul

(* the expected scalar length *)

inline_for_extraction
let getScalarLenWords curve : (a: FStar.UInt32.t {v a > 0}) = 
  match curve with
  |P256 -> 4ul
  |P384 -> 6ul
  |_ -> 4ul

inline_for_extraction
let getScalarLenBytes curve = 
  getScalarLenWords curve *. 8ul

(* the scalar length in bits *)
inline_for_extraction
let getScalarLen (c: curve) = getScalarLenBytes c *! 8ul


(* the next power in pow2 (k * 64) after the prime *)
inline_for_extraction noextract
let getPowerU curve : (a: UInt32.t {
  getPrime curve < pow2 (v a) /\ 
  pow2 (v a) < 2 * getPrime curve}) = 
  match curve with 
  |P256 ->  assert_norm (pow2 256 < 2 * getPrime P256); 256ul
  |P384 ->  assert_norm (pow2 384 < 2 * getPrime P384); 384ul


let getPower curve : a: nat {
  getPrime curve < pow2 a /\ 
  pow2 a < 2 * getPrime curve /\ 
  pow2 a % getPrime curve <> 0 /\
  a == v (getCoordinateLenU64 curve) * 64} = v (getPowerU curve)


val lemmaGetPowerAsCoordinateLen: #c: curve -> Lemma (pow2 (getPower c) == pow2 (8 * v (getCoordinateLenU c)))

let lemmaGetPowerAsCoordinateLen #c = ()


(* the power for 2 words *)
let getLongPower curve = getPower curve * 2

inline_for_extraction 
let getOrderLen (c: curve) = 
  match c with
  | P256 -> 32ul
  | P384 -> 48ul 
  | _ -> 32ul



(* order of the curves *)

(* proof of primarity in Sage: 
>>is_prime(0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551)
True

>> is_prime(0xffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973)
True
*)


inline_for_extraction
let getOrder (#c: curve) : (a: pos{a > pow2 64 /\ a < pow2 (getPower c) /\ pow2 (getPower c) < 2 * a /\ FStar.Math.Euclid.is_prime a /\ pow2 (getPower c) % a <> 0}) =
  match c with 
  |P256 -> 
    let orderp256 = 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551 in 
    assert_norm(orderp256 > pow2 64);
    assert_norm(orderp256 < pow2 (getPower P256));
    assert_norm(2 * orderp256 > pow2 (getPower P256));
    assume(FStar.Math.Euclid.is_prime orderp256);
    orderp256
  |P384 ->     
    let orderp384 = 0xffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973 in 
    assert_norm(orderp384 > pow2 64);
    assert_norm(orderp384 < pow2 (getPower P384));
    assert_norm(2 * orderp384 > pow2 (getPower P384));
    assume(FStar.Math.Euclid.is_prime orderp384);
    orderp384


type coordSyst = 
  |Affine 
  |Jacobian

(* points that are not bound by a prime *)
let point_jacobian_nat = tuple3 nat nat nat

let point_affine_nat = tuple2 nat nat

let invert_point (a: coordSyst): Lemma
  (requires True)
  (ensures (inversion coordSyst))
  [SMTPat (coordSyst) ]
  = allow_inversion (coordSyst)


let point_nat #coordSyst = 
  match coordSyst with 
  |Affine -> point_affine_nat
  |Jacobian -> point_jacobian_nat


(* points that are bound by a prime *)
let nat_prime #curve = n:nat{n < getPrime curve}

let point_nat_prime #curve = 
  p: point_jacobian_nat{let (a, b, c) = p in a < getPrime curve /\ b < getPrime curve /\ c < getPrime curve}

let point_nat_prime_precomputed #curve = 
  p: point_jacobian_nat{let (a, b, c) = p in a < getPrime curve /\ b < getPrime curve /\ c < getPrime curve}


let point_affine_nat_prime #curve = 
  p: point_affine_nat{let (a, b) = p in a < getPrime curve /\ b < getPrime curve}


noextract
let modp_inv2 #curve (x: nat) : Tot (elem (getPrime curve)) =
  modp_inv2_prime x (getPrime curve)

noextract
let modp_inv2_pow #curve (x: nat) : Tot (elem (getPrime curve)) =
  let prime = getPrime curve in 
  pow x (prime - 2) % prime


noextract
let min_one_prime (prime: pos {prime > 3}) (x: int) : Tot (r: int {r < prime}) =
  let p = x % prime in 
  exp #prime p (prime - 1)


(* a coordinate of the curve *)
inline_for_extraction
let aCoordinate #curve : int = 
  match curve with 
  |P256 -> -3
  |P384 -> -3


(* b coordinate of the curve *)
inline_for_extraction
let bCoordinate #curve : (a: nat {a < (getPrime curve)}) =
  match curve with 
  |P256 -> assert_norm (41058363725152142129326129780047268409114441015993725554835256314039467401291 < getPrime P256);
    41058363725152142129326129780047268409114441015993725554835256314039467401291
  |P384 -> assert_norm (0xb3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef < getPrime P384); 
    0xb3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef


inline_for_extraction
let basePoint #curve : point_nat_prime #curve  =
  match curve with 
  |P256 -> assert_norm (0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296 < getPrime P256);
  (0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296,
  0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5,
  1)
   |P384 -> assert_norm(0xaa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7 < getPrime P384);
  (0xaa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7,0x3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f, 1) 


val isPrimeGroup: c: curve -> Tot bool

let isPrimeGroup c = 
  match c with 
  |P256 -> true
  |P384 -> true
  |_ -> false
