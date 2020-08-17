module Spec.P256

open FStar.Mul

open Lib.ByteSequence
open Lib.IntTypes
open Lib.Sequence

open FStar.Math.Lemmas
open FStar.Math.Lib

#set-options "--fuel 0 --ifuel 0 --z3rlimit 100"

noextract
let prime256: (a: pos {a > 3 && a < pow2 256}) =
  assert_norm (pow2 256 - pow2 224 + pow2 192 + pow2 96 -1 > 3);
  assert_norm (pow2 256 - pow2 224 + pow2 192 + pow2 96 -1 < pow2 256);
  pow2 256 - pow2 224 + pow2 192 + pow2 96 -1

noextract
let prime384: (a: pos {a > 3 && a < pow2 384}) = 
  assert_norm(pow2 384 - pow2 128 - pow2 96 + pow2 32 - 1 > 3);
  assert_norm(pow2 384 - pow2 128 - pow2 96 + pow2 32 - 1 < pow2 384);
  pow2 384 - pow2 128 - pow2 96 + pow2 32 - 1


type curve = 
  |P256
  |P384


let invert_state_s (a: curve): Lemma
  (requires True)
  (ensures (inversion curve))
  [SMTPat (curve) ]
=
  allow_inversion (curve)

inline_for_extraction
let getCoordinateLen curve =
  match curve with 
  |P256 -> 32
  |P384 -> 48

inline_for_extraction
let getCoordinateLenU64 curve = 
  match curve with
  |P256 -> 4ul
  |P384 -> 6ul  

inline_for_extraction
let getPointLen curve = 
  match curve with 
  |P256 -> 64
  |P384 -> 96

(* Actually there is a logical distinction between the length of a coordinate and the length of the order.
 Just by magic they have the same values (:  *)

inline_for_extraction
let getScalarLen curve = 
  match curve with 
  |P256 -> 32ul
  |P384 -> 48ul

inline_for_extraction
let getScalarLenNat curve = uint_v (getScalarLen curve)

inline_for_extraction
let getPower curve = 
  match curve with 
  |P256 -> 256
  |P384 -> 384

inline_for_extraction 
let getLongPower curve = getPower curve * 2

inline_for_extraction
let getPowerU curve = 
  match curve with 
  |P256 -> 256ul
  |P384 -> 384ul

inline_for_extraction
let getPower2 curve = pow2 (getPower curve)

inline_for_extraction
let getLongPower2 curve = pow2 (getLongPower curve)

inline_for_extraction
let getPrime curve = 
  match curve with 
  |P256 -> prime256
  |P384 -> prime384

inline_for_extraction
let getPrimeOrder (#c: curve) : (a: pos{a < pow2 (getPower c)}) =
  match c with 
  |P256 -> assert_norm (115792089210356248762697446949407573529996955224135760342422259061068512044369 < pow2 (getPower P256));
  115792089210356248762697446949407573529996955224135760342422259061068512044369
  |P384 -> 
    assert_norm (39402006196394479212279040100143613805079739270465446667946905279627659399113263569398956308152294913554433653942643 < pow2 (getPower P384));
39402006196394479212279040100143613805079739270465446667946905279627659399113263569398956308152294913554433653942643


(* for p256 and 384 are the same *)
inline_for_extraction
let aCoordinate (#c: curve) = -3 

inline_for_extraction
let bCoordinate #curve : (a: nat {a < (getPrime curve)}) =
  match curve with 
  |P256 -> assert_norm (41058363725152142129326129780047268409114441015993725554835256314039467401291 < getPrime P256);
    41058363725152142129326129780047268409114441015993725554835256314039467401291
  |P384 -> assert_norm (27580193559959705877849011840389048093056905856361568521428707301988689241309860865136260764883745107765439761230575 < getPrime P384); 27580193559959705877849011840389048093056905856361568521428707301988689241309860865136260764883745107765439761230575


let nat_prime #curve = n:nat{n < getPrime curve}

let point_nat = tuple3 nat nat nat

let point_nat_prime #curve = (p: point_nat 
  {
    let prime = getPrime curve in 
    let (a, b, c) = p in a < prime /\ b < prime /\ c < prime})


inline_for_extraction
let basePoint #curve : point_nat_prime #curve  =
  match curve with 
  |P256 -> assert_norm (0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296 < getPrime P256);
  (0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296,
  0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5,
  1)
   |P384 -> assert_norm(0xaa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7 < getPrime P384);
  (0xaa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7,0x3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f, 1) 



type elem (n:pos) = x:nat{x < n}

let fmul (#n:pos) (x:elem n) (y:elem n) : elem n = (x * y) % n

noextract
val pow: a:nat -> b:nat -> nat

let rec pow a b =
  if b = 0 then 1
  else a * (pow a (b - 1))


#push-options "--fuel 1"

noextract
val pow_plus: a: nat -> b: nat -> c: nat -> 
  Lemma (ensures (pow a b * pow a c = pow a (b + c))) 
  (decreases b)

let rec pow_plus a b c = 
  match b with 
  | 0 -> assert_norm (pow a 0 = 1)
  | _ -> pow_plus a (b - 1) c

#pop-options

val exp: #n: pos -> a: elem n -> b: pos -> Tot (elem n) (decreases b)

let rec exp #n a b =
  if b = 1 then a
  else
    if b % 2 = 0 then exp (fmul a a) (b / 2)
    else fmul a (exp (fmul a a) (b / 2))


noextract
let modp_inv_prime (prime: pos {prime > 3}) (x: elem prime) : Tot (elem prime) =
  (exp #prime x (prime - 2)) % prime

noextract
let modp_inv2_prime (x: int) (p: nat {p > 3}) : Tot (elem p) = modp_inv_prime p (x % p)

noextract
let modp_inv2 #curve (x: nat) : Tot (elem (getPrime curve)) =
  modp_inv2_prime x (getPrime curve)

noextract
let modp_inv2_pow #curve (x: nat) : Tot (elem (getPrime curve)) =
  let prime = getPrime curve in 
  pow x (prime - 2) % prime


noextract
let min_one_prime (prime: pos {prime > 3}) (x: int) : Tot (elem prime) =
  let p = x % prime in 
  exp #prime p (prime - 1)
  

noextract
let _point_double #curve (p:point_nat_prime #curve) : point_nat_prime #curve =
  let prime = getPrime curve in 
  let x, y, z = p in
  let delta = z * z in 
  let gamma = y * y in 
  let beta = x * gamma in 
  let alpha = 3 * (x - delta) * (x + delta) in 
  let x3 = (alpha * alpha - 8 * beta) % prime in 
  let y3 = (alpha *  (4 * beta - x3) - 8 * gamma * gamma) % prime in 
  let z3 = ((y + z) * (y + z) - delta - gamma) % prime in 
  (x3, y3, z3)


noextract
let _point_add #curve (p:point_nat_prime #curve) (q:point_nat_prime #curve) : point_nat_prime #curve =
  let prime = getPrime curve in 
  let (x1, y1, z1) = p in
  let (x2, y2, z2) = q in

  let z2z2 = z2 * z2 in
  let z1z1 = z1 * z1 in

  let u1 = x1 * z2z2 % prime in
  let u2 = x2 * z1z1 % prime in

  let s1 = y1 * z2 * z2z2 % prime in
  let s2 = y2 * z1 * z1z1 % prime in

  let h = (u2 - u1) % prime in
  let r = (s2 - s1) % prime in

  let rr = r * r in
  let hh = h * h in
  let hhh = h * h * h in

  let x3 = (rr - hhh - 2 * u1 * hh) % prime in
  let y3 = (r * (u1 * hh - x3) - s1 * hhh) % prime in
  let z3 = (h * z1 * z2) % prime in
  if z2 = 0 then
    (x1, y1, z1)
  else
    if z1 = 0 then
      (x2, y2, z2)
    else
      (x3, y3, z3)


let isPointAtInfinity (p:point_nat) =
  let (_, _, z) = p in z = 0

#push-options "--fuel 1"

let _norm #curve (p:point_nat_prime #curve) : point_nat_prime #curve =
  let prime = getPrime curve in 
  let (x, y, z) = p in
  let z2 = z * z in
  let z2i = modp_inv2_pow #curve z2 in
  let z3 = z * z * z in
  let z3i = modp_inv2_pow #curve z3 in
  let x3 = (z2i * x) % prime in
  let y3 = (z3i * y) % prime in
  let z3 = if isPointAtInfinity p then 0 else 1 in
  (x3, y3, z3)


let scalar_bytes (#c: curve) = lbytes (getCoordinateLen c)


let ith_bit (#c: curve) (k:lbytes (getCoordinateLen c)) (i:nat{i < getPower c}) : uint64 =
  let q = (getCoordinateLen c - 1) - i / 8 in 
  let r = size (i % 8) in
  to_u64 ((index k q >>. r) &. u8 1)

val _ml_step0: #c: curve -> p:point_nat_prime #c -> q:point_nat_prime #c -> tuple2 (point_nat_prime #c) (point_nat_prime #c)

let _ml_step0 r0 r1 =
  let r0 = _point_add r1 r0 in
  let r1 = _point_double r1 in
  (r0, r1)


val _ml_step1: #c: curve -> p: point_nat_prime #c -> q: point_nat_prime #c -> tuple2 (point_nat_prime #c) (point_nat_prime #c)

let _ml_step1 r0 r1 =
  let r1 = _point_add r0 r1 in
  let r0 = _point_double r0 in
  (r0, r1)


val _ml_step: #c: curve -> k:scalar_bytes #c -> i:nat{i < getPower c} -> tuple2 (point_nat_prime #c) (point_nat_prime #c) -> tuple2 (point_nat_prime #c) (point_nat_prime #c)

let _ml_step #c k i (p, q) =
  let bit = (getPower c - 1) - i in
  let bit = ith_bit k bit in
  let open Lib.RawIntTypes in
  if uint_to_nat bit = 0 then
    _ml_step1 p q
  else
    _ml_step0 p q


val montgomery_ladder_spec: #c: curve -> scalar_bytes #c -> tuple2 (point_nat_prime #c) (point_nat_prime #c)-> tuple2 (point_nat_prime #c) (point_nat_prime #c)

let montgomery_ladder_spec k pq =
  Lib.LoopCombinators.repeati 256 (_ml_step k) pq


val scalar_multiplication: #c: curve -> scalar_bytes #c -> point_nat_prime #c -> point_nat_prime #c

let scalar_multiplication k p =
  let pai = (0, 0, 0) in
  let q, f = montgomery_ladder_spec k (pai, p) in
  _norm q


val secret_to_public: #c: curve -> scalar_bytes #c -> point_nat_prime #c

let secret_to_public k =
  let pai = (0, 0, 0) in
  let q, f = montgomery_ladder_spec k (pai, basePoint) in
  _norm q


let isPointOnCurve (#c: curve) (p: point_nat_prime #c) : bool = 
  let (x, y, z) = p in
  (y * y) % (getPrime c) =
  (x * x * x + aCoordinate #c  * x + bCoordinate #c) % prime256


val toJacobianCoordinates: tuple2 nat nat -> tuple3 nat nat nat

let toJacobianCoordinates (r0, r1) = (r0, r1, 1)
