module Spec.ECDSA

open FStar.Mul

open Lib.ByteSequence
open Lib.IntTypes
open Lib.Sequence

open Spec.P256
open Spec.Hash.Definitions

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

//-------------------------------
// TODO: remove
val lemma_scalar_ith: sc:lbytes 32 -> k:nat{k < 32} -> Lemma
  (v sc.[k] == nat_from_intseq_le sc / pow2 (8 * k) % pow2 8)

let lemma_scalar_ith sc k =
  index_nat_to_intseq_le #U8 #SEC 32 (nat_from_intseq_le sc) k;
  nat_from_intseq_le_inj sc (nat_to_intseq_le 32 (nat_from_intseq_le sc))


val lemma_euclidian_for_ithbit: k: nat -> i: nat
  -> Lemma (k / (pow2 (8 * (i / 8)) * pow2 (i % 8)) == k / pow2 i)

let lemma_euclidian_for_ithbit k i =
  Math.Lib.lemma_div_def i 8;
  Math.Lemmas.pow2_plus (8 * (i / 8)) (i % 8)


val ith_bit: k:lbytes 32 -> i:nat{i < 256}
  -> t:uint64 {(v t == 0 \/ v t == 1) /\ v t == nat_from_intseq_le k / pow2 i % 2}

let ith_bit k i =
  let q = i / 8 in
  let r = i % 8 in
  let tmp1 = k.[q] >>. (size r) in
  let tmp2 = tmp1 &. u8 1 in
  let res = to_u64 tmp2 in
  logand_le tmp1 (u8 1);
  logand_mask tmp1 (u8 1) 1;
  lemma_scalar_ith k q;
  let k = nat_from_intseq_le k in
  Math.Lemmas.pow2_modulo_division_lemma_1 (k / pow2 (8 * (i / 8))) (i % 8) 8;
  Math.Lemmas.division_multiplication_lemma k (pow2 (8 * (i / 8))) (pow2 (i % 8));
  lemma_euclidian_for_ithbit k i;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (k / pow2 i) 1 (8 - (i % 8));
  res

//---------------------------------
// TODO: remove
let felem_seq = lseq uint64 4

val changeEndian: felem_seq -> felem_seq
let changeEndian i =
  let zero =  Lib.Sequence.index i 0 in
  let one =   Lib.Sequence.index i 1 in
  let two =   Lib.Sequence.index i 2 in
  let three = Lib.Sequence.index i 3 in

  let o = Lib.Sequence.upd i 0 three in
  let o = Lib.Sequence.upd o 1 two in
  let o = Lib.Sequence.upd o 2 one in
          Lib.Sequence.upd o 3 zero


val changeEndianLemma: k: lseq uint64 4 ->
  Lemma (nat_from_intseq_le (changeEndian k) == nat_from_intseq_be k)

let changeEndianLemma k =
  let k0 = changeEndian k in

  nat_from_intseq_be_slice_lemma (slice k 2 4) 1;
  nat_from_intseq_be_slice_lemma (slice k 1 4) 1;
  nat_from_intseq_be_slice_lemma k 1;

  nat_from_intseq_be_lemma0 (slice k 0 1);
  nat_from_intseq_be_lemma0 (slice k 1 2);
  nat_from_intseq_be_lemma0 (slice k 2 3);
  nat_from_intseq_be_lemma0 (slice k 3 4);

  nat_from_intseq_le_slice_lemma (slice k0 2 4) 1;
  nat_from_intseq_le_slice_lemma (slice k0 1 4) 1;
  nat_from_intseq_le_slice_lemma k0 1;

  nat_from_intseq_le_lemma0 (slice k0 0 1);
  nat_from_intseq_le_lemma0 (slice k0 1 2);
  nat_from_intseq_le_lemma0 (slice k0 2 3);
  nat_from_intseq_le_lemma0 (slice k0 3 4);

  assert_norm (pow2 (2 * 64) * pow2 64 == pow2 (3 * 64))

val changeEndianLemmaI: a: nat {a < pow2 256} ->
  Lemma (changeEndian (nat_to_intseq_le 4 a) == nat_to_intseq_be 4 a)

let changeEndianLemmaI a =
  let a0 = nat_to_intseq_le #U64 #SEC 4 a in
  index_nat_to_intseq_le #U64 #SEC  4 a 0;
  index_nat_to_intseq_le #U64 #SEC  4 a 1;
  index_nat_to_intseq_le #U64 #SEC  4 a 2;
  index_nat_to_intseq_le #U64 #SEC  4 a 3;

  index_nat_to_intseq_be #U64 #SEC 4 a 0;
  index_nat_to_intseq_be #U64 #SEC 4 a 2;
  index_nat_to_intseq_be #U64 #SEC 4 a 3;
  index_nat_to_intseq_be #U64 #SEC 4 a 1;


  assert(Lib.Sequence.index #_ #4 (changeEndian (nat_to_intseq_le #U64 #SEC 4 a)) 3 == Lib.Sequence.index #_ #4 (nat_to_intseq_be #U64 #SEC 4 a) 3);

  assert(Lib.Sequence.index #_ #4 (changeEndian (nat_to_intseq_le #U64 #SEC 4 a)) 2 == Lib.Sequence.index #_ #4 (nat_to_intseq_be #U64 #SEC 4 a) 2);

  assert(Lib.Sequence.index #_ #4 (changeEndian (nat_to_intseq_le #U64 #SEC 4 a)) 1 == Lib.Sequence.index #_ #4 (nat_to_intseq_be #U64 #SEC 4 a) 1);

  assert(Lib.Sequence.index #_ #4 (changeEndian (nat_to_intseq_le #U64 #SEC 4 a)) 0 == Lib.Sequence.index #_ #4 (nat_to_intseq_be #U64 #SEC 4 a) 0);
  eq_intro (changeEndian (nat_to_intseq_le #U64 #SEC 4 a)) (nat_to_intseq_be 4 a)


val changeEndian_le_be: a:nat{a < pow2 256} ->
  Lemma (uints_to_bytes_be (changeEndian (nat_to_intseq_le 4 a)) == nat_to_bytes_be 32 a)

let changeEndian_le_be a =
  changeEndianLemmaI a;
  uints_to_bytes_be_nat_lemma #U64 #SEC 4 a

//----------------------------------

val verifyQValidCurvePointSpec: publicKey:tuple3 nat nat nat{~(isPointAtInfinity publicKey)} -> bool
let verifyQValidCurvePointSpec publicKey =
  let x, y, z = publicKey in
  x < prime && y < prime && z < prime &&
  is_point_on_curve (x, y, z)


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
  -> publicKey:tuple2 nat nat
  -> r:nat
  -> s:nat
  -> mLen:size_nat{mLen >= min_input_length alg}
  -> m:lseq uint8 mLen
  -> bool

let ecdsa_verification_agile alg publicKey r s mLen m =
  allow_inversion hash_alg_ecdsa;
  let publicJacobian = toJacobianCoordinates publicKey in
  if not (verifyQValidCurvePointSpec publicJacobian) then false
  else begin
    if not (checkCoordinates r s) then false
    else begin
      let hashM = hashSpec alg mLen m in
      let cutHashM = sub hashM 0 32 in
      let hashNat = nat_from_bytes_be cutHashM % order in

      let sinv = qinv s in
      let u1 = nat_to_bytes_be 32 (sinv *^ hashNat) in
      let u2 = nat_to_bytes_be 32 (sinv *^ r) in

      let pointAtInfinity = (0, 0, 0) in
      let u1D, _ = montgomery_ladder_spec u1 (pointAtInfinity, base_point) in
      let u2D, _ = montgomery_ladder_spec u2 (pointAtInfinity, publicJacobian) in
      let sumD = if norm_jacob_point u1D = norm_jacob_point u2D then
        point_double u1D
      else
        point_add u1D u2D in
      let pointNorm = norm_jacob_point sumD in

      let x, y, z = pointNorm in
      let x = x % order in
      if Spec.P256.isPointAtInfinity pointNorm then false else x = r
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
