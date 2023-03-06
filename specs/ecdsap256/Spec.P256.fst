module Spec.P256

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open Spec.Hash.Definitions
module M = Lib.NatMod

include Spec.P256.PointOps

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(** https://eprint.iacr.org/2013/816.pdf *)

///  Elliptic curve scalar multiplication
// TODO: use Lib.Exponentiation

let scalar = lbytes 32

let ith_bit (k:scalar) (i:nat{i < 256}) : uint64 =
  let q = 31 - i / 8 in let r = size (i % 8) in
  to_u64 ((index k q >>. r) &. u8 1)


val _ml_step0: p:jacob_point -> q:jacob_point -> tuple2 jacob_point jacob_point
let _ml_step0 r0 r1 =
  let r0 = point_add r1 r0 in
  let r1 = point_double r1 in
  (r0, r1)


val _ml_step1: p: jacob_point -> q:jacob_point -> tuple2 jacob_point jacob_point
let _ml_step1 r0 r1 =
  let r1 = point_add r0 r1 in
  let r0 = point_double r0 in
  (r0, r1)


val _ml_step: k:scalar -> i:nat{i < 256} -> tuple2 jacob_point jacob_point -> tuple2 jacob_point jacob_point
let _ml_step k i (p, q) =
  let bit = 255 - i in
  let bit = ith_bit k bit in
  let open Lib.RawIntTypes in
  if uint_to_nat bit = 0 then
    _ml_step1 p q
  else
    _ml_step0 p q


val montgomery_ladder_spec: k:scalar -> tuple2 jacob_point jacob_point -> tuple2 jacob_point jacob_point
let montgomery_ladder_spec k pq =
  Lib.LoopCombinators.repeati 256 (_ml_step k) pq


val scalar_multiplication: scalar -> jacob_point -> jacob_point
let scalar_multiplication k p =
  let pai = (0, 0, 0) in
  let q, f = montgomery_ladder_spec k (pai, p) in
  norm_jacob_point q


val secret_to_public: scalar -> jacob_point
let secret_to_public k =
  let pai = (0, 0, 0) in
  let q, f = montgomery_ladder_spec k (pai, base_point) in
  norm_jacob_point q

// from Spec.ECDSA.fst

let validate_pubkey_point (pk:lbytes 64) : bool =
  Some? (load_point pk)


val checkCoordinates: r:nat -> s:nat -> bool
let checkCoordinates r s =
  if 0 < r && r < order && 0 < s && s < order then true else false


type hash_alg_ecdsa =
  | NoHash
  | Hash of (a:hash_alg{a == SHA2_256 \/ a == SHA2_384 \/ a == SHA2_512})


let invert_state_s (a:hash_alg_ecdsa): Lemma
  (requires True)
  (ensures (inversion hash_alg_ecdsa))
  [ SMTPat (hash_alg_ecdsa) ]
=
  allow_inversion (hash_alg_ecdsa)


val min_input_length: hash_alg_ecdsa -> Tot int
let min_input_length a = match a with | NoHash -> 32 | Hash a -> 0

(* let hash_length (a:hash_alg_ecdsa) = match a with | NoHash -> 32 | Hash a -> hash_length a *)


val hashSpec:
    a:hash_alg_ecdsa
  -> mLen:size_nat{mLen >= min_input_length a}
  -> m:lseq uint8 mLen ->
  Tot (r:Lib.ByteSequence.lbytes
    (if Hash? a then hash_length (match a with Hash a -> a) else mLen){length r >= 32})

let hashSpec a mLen m =
  assert_norm (pow2 32 < pow2 61);
  assert_norm (pow2 32 < pow2 125);
  allow_inversion hash_alg_ecdsa;
  match a with
  | NoHash -> m
  | Hash a -> Spec.Agile.Hash.hash a m


// TODO: rm, once we use complete point addition and doubling
(**
  Important changed was done comparing to the previous version:
  The point addition routine used in the code doesnot work correctly in case the points are equal to each other. In this case the produced result is equal to 0. To solve it, before the execution we check that points are equal and then call either point double, if the points are identical, or point add.

  Sage script:

  prime = 2** 256 - 2**224 + 2**192 + 2**96 -1

  def pointAdd(x1, y1, z1, x2, y2, z2):
    z2z2 = z2 * z2
    z1z1 = z1 * z1
    u1 = x1 * z2 * z2
    u2 = x2 * z1 * z1
    s1 = y1 * z2 * z2 * z2
    s2 = y2 * z1 * z1 * z1
    h = u2 - u1
    r = s2 - s1
    rr = r * r
    hh = h * h
    hhh = h * h * h
    x3 = (rr - hhh - 2 * u1 * hh) % prime
    y3 = (r * (u1 * hh - x3) - s1 * hhh) % prime
    z3 = (h * z1 * z2) % prime
    return x3, y3, z3

    pointAdd(94616602910890750895476491097843493117917747793373442062816991926475923005642,
    36020885031736900871498807428940761284168967909318796815085487081314546588335, 1,
    94616602910890750895476491097843493117917747793373442062816991926475923005642,
    36020885031736900871498807428940761284168967909318796815085487081314546588335, 1)

    The result is (0, 0, 0)

    The correct result:

    prime = 2** 256 - 2**224 + 2**192 + 2**96 -1
    p = Zmod(prime)
    a = -3
    b = 41058363725152142129326129780047268409114441015993725554835256314039467401291

    c = EllipticCurve(p, [a, b])

    point = c(94616602910890750895476491097843493117917747793373442062816991926475923005642, 36020885031736900871498807428940761284168967909318796815085487081314546588335)
    doublePoint = point + point

    (50269061329272915414642095420870671498020143477290467295126614723791645001065, 13163180605447792593340701861458269296763094398473012191314473475747756843689)

**)


val ecdsa_verification_agile:
    alg:hash_alg_ecdsa
  -> public_key:lbytes 64
  -> r:nat
  -> s:nat
  -> msg_len:size_nat{msg_len >= min_input_length alg}
  -> msg:lbytes msg_len ->
  bool

let ecdsa_verification_agile alg public_key r s msg_len msg =
  allow_inversion hash_alg_ecdsa;
  let pk = load_point public_key in
  if not (Some? pk) then false
  else begin
    if not (checkCoordinates r s) then false
    else begin
      let hashM = hashSpec alg msg_len msg in
      let cutHashM = sub hashM 0 32 in
      let hashNat = nat_from_bytes_be cutHashM % order in

      let sinv = qinv s in
      let u1 = nat_to_bytes_be 32 (sinv *^ hashNat) in
      let u2 = nat_to_bytes_be 32 (sinv *^ r) in

      let pointAtInfinity = (0, 0, 0) in
      let u1D, _ = montgomery_ladder_spec u1 (pointAtInfinity, base_point) in
      let u2D, _ = montgomery_ladder_spec u2 (pointAtInfinity, Some?.v pk) in
      let sumD = if norm_jacob_point u1D = norm_jacob_point u2D then
        point_double u1D
      else
        point_add u1D u2D in
      let pointNorm = norm_jacob_point sumD in

      let x, y, z = pointNorm in
      let x = x % order in
      if is_point_at_inf pointNorm then false else x = r
    end
  end


val ecdsa_signature_agile:
    alg:hash_alg_ecdsa
  -> mLen:size_nat{mLen >= min_input_length alg}
  -> m:lseq uint8 mLen
  -> privateKey:lseq uint8 32
  -> k:lseq uint8 32
  -> tuple3 nat nat bool

let ecdsa_signature_agile alg mLen m privateKey k =
  assert_norm (pow2 32 < pow2 61);
  assert_norm (pow2 32 < pow2 125);
  let r, _ = montgomery_ladder_spec k ((0,0,0), base_point) in
  let (xN, _, _) = norm_jacob_point r in

  let hashM = hashSpec alg mLen m in
  let cutHashM = sub hashM 0 32 in
  let z = nat_from_bytes_be cutHashM % order in

  let kFelem = nat_from_bytes_be k in
  let privateKeyFelem = nat_from_bytes_be privateKey in
  let resultR = xN % order in
  let resultS = (z + resultR * privateKeyFelem) * pow kFelem (order - 2) % order in
  if resultR = 0 || resultS = 0 then
    resultR, resultS, false
  else
    resultR, resultS, true

// from Spec.DH

(* Initiator *)
val ecp256_dh_i: s:lbytes 32 -> tuple2 (lbytes 64) bool
let ecp256_dh_i s =
  let xN, yN, zN = secret_to_public s in
  aff_store_point (xN, yN), not (is_point_at_inf (xN, yN, zN))


(* Responder *)
val ecp256_dh_r: pk:lbytes 64 -> s:lbytes 32 -> tuple2 (lbytes 64) bool
let ecp256_dh_r public_key s =
  let pk = load_point public_key in
  if Some? pk then
    let xN, yN, zN = scalar_multiplication s (Some?.v pk) in
    aff_store_point (xN, yN), not (is_point_at_inf (xN, yN, zN))
  else
    aff_store_point (0, 0), false
