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

let point_nat = tuple3 nat nat nat

noextract
val pow: a:nat -> b:nat -> nat

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
  (exp #prime x (prime - 2)) % prime

noextract
let modp_inv2_prime (x: int) (p: nat {p > 3}) : Tot (elem p) = modp_inv_prime p (x % p)


(** The main instantiation of curves **) 
(* https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.186-4.pdf *)
type curve = 
  |P256
  |P384
  |Default


let invert_state_s (a: curve): Lemma
  (requires True)
  (ensures (inversion curve))
  [SMTPat (curve) ]
  = allow_inversion (curve)



(** Curve parameters **)

let prime256: (a: pos {a > 3 && a < pow2 256}) =
  assert_norm (pow2 256 - pow2 224 + pow2 192 + pow2 96 -1 > 3);
  assert_norm (pow2 256 - pow2 224 + pow2 192 + pow2 96 -1 < pow2 256);
  pow2 256 - pow2 224 + pow2 192 + pow2 96 -1

let prime384: (a: pos {a > 3 && a < pow2 384}) = 
  assert_norm(pow2 384 - pow2 128 - pow2 96 + pow2 32 - 1 > 3);
  assert_norm(pow2 384 - pow2 128 - pow2 96 + pow2 32 - 1 < pow2 384);
  pow2 384 - pow2 128 - pow2 96 + pow2 32 - 1

(* the length of each coordinate of the point as uint64 *)
let getCoordinateLenU64 curve = 
  match curve with
  |P256 -> 4ul
  |P384 -> 6ul  
  |_ -> 4ul


(* the length of each coordinate of the point as uint8 *)
let getCoordinateLenU curve = getCoordinateLenU64 curve *. 8ul

let getCoordinateLen curve = v (getCoordinateLenU curve)

(* each point consists of three coordinates *)
let getPointLen curve = getCoordinateLen curve * 3

(* the expected scalar length *)
let getScalarLenBytes curve = 
  match curve with 
  |P256 -> 32ul
  |P384 -> 48ul
  | _ -> 0ul

(* the scalar length in bits *)
let getScalarLen (c: curve) = v (getScalarLenBytes c) * 8


(* the next power in pow2 (k * 64) after the prime *)
let getPowerU curve = 
  match curve with 
  |P256 -> 256ul
  |P384 -> 384ul
  |_ -> 256ul

let getPower curve : a: nat {a = v (getCoordinateLenU64 curve) * 64} = v (getPowerU curve)

(* the power for 2 words *)
let getLongPower curve = getPower curve * 2


inline_for_extraction
let getPrime curve : prime: nat {prime > 3} = 
  match curve with 
  |P256 -> prime256
  |P384 -> prime384
  |_ -> 4



let nat_prime #curve = n:nat{n < getPrime curve}

let point_nat_prime #curve = 
  p: point_nat{let (a, b, c) = p in a < getPrime curve /\ b < getPrime curve /\ c < getPrime curve}


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


(*
inline_for_extraction
let getKo (c: curve) : (r: uint64 {v r = min_one_prime (pow2 64) (- getPrime c)}) = 
  match c with 
  |P256 -> 
    assert_norm (min_one_prime (pow2 64) (- getPrime P256) == 1);
    (u64 1)
  |P384 -> 
    assert_norm (min_one_prime (pow2 64) (- getPrime P384) == 4294967297);
    (u64 4294967297)
  (* |Default ->  *)
    (*  *)
*)

(* order of the curves *)
inline_for_extraction
let getOrder (#c: curve) : (a: pos{a < pow2 (getPower c)}) =
  match c with 
  |P256 -> assert_norm (115792089210356248762697446949407573529996955224135760342422259061068512044369 < pow2 (getPower P256));
  115792089210356248762697446949407573529996955224135760342422259061068512044369
  |P384 -> 
    assert_norm (39402006196394479212279040100143613805079739270465446667946905279627659399113263569398956308152294913554433653942643 < pow2 (getPower P384));
39402006196394479212279040100143613805079739270465446667946905279627659399113263569398956308152294913554433653942643


(* a coordinate of the curve *)
inline_for_extraction
let aCoordinate (#c: curve) = -3 

(* b coordinate of the curve *)
inline_for_extraction
let bCoordinate #curve : (a: nat {a < (getPrime curve)}) =
  match curve with 
  |P256 -> assert_norm (41058363725152142129326129780047268409114441015993725554835256314039467401291 < getPrime P256);
    41058363725152142129326129780047268409114441015993725554835256314039467401291
  |P384 -> assert_norm (27580193559959705877849011840389048093056905856361568521428707301988689241309860865136260764883745107765439761230575 < getPrime P384); 27580193559959705877849011840389048093056905856361568521428707301988689241309860865136260764883745107765439761230575


inline_for_extraction
let basePoint #curve : point_nat_prime #curve  =
  match curve with 
  |P256 -> assert_norm (0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296 < getPrime P256);
  (0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296,
  0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5,
  1)
   |P384 -> assert_norm(0xaa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7 < getPrime P384);
  (0xaa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7,0x3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f, 1) 

