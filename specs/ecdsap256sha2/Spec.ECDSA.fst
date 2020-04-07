module Spec.ECDSA

open FStar.Mul
open Spec.ECDSAP256.Definition
open Spec.P256.Lemmas

open Lib.ByteSequence
open Lib.IntTypes
open Lib.Sequence

open Spec.Hash
open Spec.P256

module Def = Spec.Hash.Definitions

open FStar.Math.Lemmas
open FStar.Math.Lib

(*
// Sage scratchpad

def toB(x):
    for i in range(4):
        print(((x >> i * 64) % (2 ** 64)))

qx = 0xe424dc61d4bb3cb7ef4344a7f8957a0c5134e16f7a67c074f82e6e12f49abf3c
qy = 0x970eed7aa2bc48651545949de1dddaf0127e5965ac85d1243d6f60e7dfaee927

primeOrder = 115792089210356248762697446949407573529996955224135760342422259061068512044369

R = 0xbf96b99aa49c705c910be33142017c642ff540c76349b9dab72f981fd9347f4f
S = 0x17c55095819089c2e03b9cd415abdf12444e323075d98f31920b9e0f57ec871c
z = 18096356966075357844 + 13937533974375268201 * 2**64 + 2811996616035378163 * 2**128 + 15112091478601597678 * 2**192

u1 = (inverse_mod(S, primeOrder) * z) % primeOrder
u2 = (inverse_mod(S, primeOrder) * R) % primeOrder

prime = Zmod(Integer(115792089210356248762697446949407573530086143415290314195533631308867097853951))
p2 = 41058363725152142129326129780047268409114441015993725554835256314039467401291

c = EllipticCurve(prime, [-3, p2])
basePoint = c(0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296, 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5)
pk = c(qx, qy)

u1g = basePoint * u1
u2Q = pk * u2
x1 = (u1g + u2Q).xy()[0]
print(x1 == R)
print(Integer(x1) % primeOrder)
print(Integer(R) % primeOrder)

#############

z = 1330795747694424120 + 14316922599628991228 * 2**64 + 308854472678183009 * 2**128 + 16765196972424757399 * 2 **192
z = 0x44acf6b7e36c1342c2c5897204fe09504e1e2efb1a900377dbc4e7a6a133ec56
d = 0x519b423d715f8b581f4fa8ee59f4771a5b44c8130b4e3eacca54a56dda72b464
k = 0x94a1bbb14b906a61a280f245f9e93c7f3b4a6247824f5d33b9670787642a68de
r = 0xf3ac8061b514795b8843e3d6629527ed2afd6b1f6a555a7acabb5e6f79c8c2ac

order = 115792089210356248762697446949407573529996955224135760342422259061068512044369
km = inverse_mod(k, order)
s = (km * (z + r * d)) % order
s_ = 0x8bf77819ca05a6b2786c76262bf7371cef97b218e96f175a3ccdda2acc058903

print(hex(s))
print(s_)

qx = 0x1ccbe91c075fc7f4f033bfa248db8fccd3565de94bbfb12f3c59ff46c271bf83
qy = 0xce4014c68811f9a21a1fdb2c0e6113e06db7ca93b7404e78dc7ccd5ca89a4ca9

primeOrder = 115792089210356248762697446949407573529996955224135760342422259061068512044369

u1 = (inverse_mod(s, primeOrder) * z) % primeOrder
u2 = (inverse_mod(s, primeOrder) * r) % primeOrder

prime = Zmod(Integer(115792089210356248762697446949407573530086143415290314195533631308867097853951))
p2 = 41058363725152142129326129780047268409114441015993725554835256314039467401291

c = EllipticCurve(prime, [-3, p2])
basePoint = c(0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296, 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5)
pk = c(qx, qy)

u1g = basePoint * u1
u2Q = pk * u2
x1 = (u1g + u2Q).xy()[0]
print(int(x1) % primeOrder == r)
*)

#set-options "--fuel 0 --ifuel 0 --z3rlimit 100"

let prime = prime_p256_order

let nat_prime = n:nat{n < prime}


val lemma_scalar_ith: sc:lbytes 32 -> k:nat{k < 32} -> Lemma
  (v sc.[k] == nat_from_intseq_le sc / pow2 (8 * k) % pow2 8)

let lemma_scalar_ith sc k =
  index_nat_to_intseq_le #U8 #SEC 32 (nat_from_intseq_le sc) k;
  //assert (Seq.index (nat_to_intseq_le #U8 #SEC 32 (nat_from_intseq_le sc)) k ==
  //        uint #U8 #SEC (nat_from_intseq_le sc / pow2 (8 * k) % pow2 8));
  //assert (
  //  nat_from_intseq_le sc ==
  //  nat_from_intseq_le (nat_to_intseq_le #U8 #SEC 32 (nat_from_intseq_le sc)));
  nat_from_intseq_le_inj sc (nat_to_intseq_le 32 (nat_from_intseq_le sc))


val lemma_euclidian_for_ithbit: k: nat -> i: nat
  -> Lemma (k / (pow2 (8 * (i / 8)) * pow2 (i % 8)) == k / pow2 i)

let lemma_euclidian_for_ithbit k i =
  lemma_div_def i 8;
  pow2_plus (8 * (i / 8)) (i % 8)


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
  pow2_modulo_division_lemma_1 (k / pow2 (8 * (i / 8))) (i % 8) 8;
  division_multiplication_lemma k (pow2 (8 * (i / 8))) (pow2 (i % 8));
  lemma_euclidian_for_ithbit k i;
  pow2_modulo_modulo_lemma_1 (k / pow2 i) 1 (8 - (i % 8));
  res


let ( *% ) a b = (a * b) % prime


val _exp_step0: p:nat_prime -> q:nat_prime -> tuple2 nat_prime nat_prime

let _exp_step0 r0 r1 =
  let r1 = r0 *% r1 in
  let r0 = r0 *% r0 in
  r0, r1


val _exp_step1: p:nat_prime -> q:nat_prime -> tuple2 nat_prime nat_prime

let _exp_step1 r0 r1 =
  let r0 = r0 *% r1 in
  let r1 = r1 *% r1 in
  (r0, r1)


let swap p q = q, p


val conditional_swap: i:uint64 -> p:nat_prime -> q:nat_prime -> tuple2 nat_prime nat_prime

let conditional_swap i p q =
  if v i = 0 then (p, q) else (q, p)


val lemma_swaped_steps: p: nat_prime -> q: nat_prime ->
  Lemma (
    let afterSwapP, afterSwapQ = swap p q in
    let p1, q1 = _exp_step0 afterSwapP afterSwapQ in
    let p2, q2 = swap p1 q1 in
    let r0, r1 = _exp_step1 p q in
    p2 == r0 /\ q2 == r1)

let lemma_swaped_steps p q = ()


val _exp_step: k:lseq uint8 32 -> i:nat{i < 256} -> before:tuple2 nat_prime nat_prime
  -> tuple2 nat_prime nat_prime

let _exp_step k i (p, q) =
  let bit = 255 - i in
  let bit = ith_bit k bit in
  let open Lib.RawIntTypes in
  if uint_to_nat bit = 0 then _exp_step0 p q else _exp_step1 p q


val _exponent_spec: k:lseq uint8 32  -> tuple2 nat_prime nat_prime
  -> tuple2 nat_prime nat_prime

let _exponent_spec k (p, q) =
  let open Lib.LoopCombinators in
  Lib.LoopCombinators.repeati 256 (_exp_step k) (p, q)


val lemma_even: index:pos{index <= 256} -> k:lseq uint8 32 {v (ith_bit k (256 - index)) == 0} ->
  Lemma (
    let number = nat_from_bytes_le k in
    let newIndex = 256 - index in
    2 * arithmetic_shift_right number (newIndex + 1) ==
    arithmetic_shift_right number newIndex)

let lemma_even index k =
  let number = nat_from_bytes_le k in
  let n = 256 - index in
  FStar.Math.Lemmas.pow2_double_mult n;
  lemma_div_def (number / pow2 n) 2;
  FStar.Math.Lemmas.division_multiplication_lemma number (pow2 n) 2


val lemma_odd: index:pos{index <= 256} -> k:lseq uint8 32 {uint_v (ith_bit k (256 - index)) == 1} ->
  Lemma(
    let number = nat_from_intseq_le k in
    let n = 256 - index  in
    2 * arithmetic_shift_right number (n + 1) + 1 ==
    arithmetic_shift_right number n)

let lemma_odd index k =
  let number = nat_from_bytes_le k in
  let n = 256 - index in
  let a0 = 2 * arithmetic_shift_right number (n + 1) + 1 in
  lemma_div_def (number / pow2 n) 2;
  division_multiplication_lemma number (pow2 n) 2;
  pow2_double_mult n;
  assert (arithmetic_shift_right number (n + 1) == number / pow2 (n + 1));
  assert (arithmetic_shift_right number n ==
          2 * arithmetic_shift_right number (n + 1) + 1)


val lemma_exponen_spec: k:lseq uint8 32
  -> start:tuple2 nat_prime nat_prime {let st0, st1 = start in st0 == 1}
  -> index:nat{index <= 256} ->
  Lemma (
    let start0, start1 = start in
    let number = nat_from_bytes_le k in
    let newIndex = 256 - index in
    let f0, f1 = Lib.LoopCombinators.repeati index (_exp_step k) start in
    f0 == pow start1 (arithmetic_shift_right number newIndex) % prime_p256_order /\
    f1 == pow start1 (arithmetic_shift_right number newIndex + 1) % prime_p256_order
  )

#push-options "--fuel 1"

val lemma_exponen_spec_0: k:lseq uint8 32
  -> start:tuple2 nat_prime nat_prime {let st0, st1 = start in st0 == 1} ->
  Lemma (
    let start0, start1 = start in
    let number = nat_from_bytes_le k in
    let newIndex = 256 in
    let f0, f1 = Lib.LoopCombinators.repeati 0 (_exp_step k) start in
    f0 == pow start1 (arithmetic_shift_right number newIndex) % prime_p256_order /\
    f1 == pow start1 (arithmetic_shift_right number newIndex + 1) % prime_p256_order
  )

let lemma_exponen_spec_0 k start =
  let st0, st1 = start in
  let number = nat_from_bytes_le k in
  assert (arithmetic_shift_right number 256 == number / pow2 256);
  FStar.Math.Lemmas.lemma_div_lt_nat number 256 256;
  assert (arithmetic_shift_right number 256 == 0);
  Lib.LoopCombinators.eq_repeati0 256 (_exp_step k) start

#pop-options

let rec lemma_exponen_spec k start index =
  let f = _exp_step k in
  let st0, st1 = start in
  let number = nat_from_bytes_le k in
  let newIndex = 256 - index in
  let open Lib.LoopCombinators in
  match index with
  | 0 -> lemma_exponen_spec_0 k start
  | _ ->
    begin
    unfold_repeati 256 f start (index - 1);
    lemma_exponen_spec k start (index - 1);
    let bitMask = uint_v (ith_bit k (256 - index)) in
    match bitMask with
      | 0 ->
        let a0 = pow st1 (arithmetic_shift_right number (256 - index + 1)) in
        let a1 = pow st1 (arithmetic_shift_right number (256 - index + 1) + 1) in
        calc (==) {
          (a0 % prime_p256_order) * (a0 % prime_p256_order) % prime_p256_order;
          == {modulo_distributivity_mult a0 a0 prime_p256_order}
          (a0 * a0) % prime_p256_order;
          == { }
          (pow st1 (arithmetic_shift_right number (256 - index + 1)) * pow st1 (arithmetic_shift_right number (256 - index + 1))) % prime_p256_order;
          == {pow_plus st1 (arithmetic_shift_right number (256 - index + 1)) (arithmetic_shift_right number (256 - index + 1))}
          (pow st1 (arithmetic_shift_right number (256 - index + 1) + arithmetic_shift_right number (256 - index + 1))) % prime_p256_order;
          == {}
          (pow st1 (2 * arithmetic_shift_right number (256 - index + 1))) % prime_p256_order;
          == {lemma_even index k}
          pow st1 (arithmetic_shift_right number newIndex) % prime_p256_order;
        };
        calc (==) {
          (a0 % prime_p256_order) * (a1 % prime_p256_order) % prime_p256_order;
          == {modulo_distributivity_mult a0 a1 prime_p256_order}
          (a0 * a1) % prime_p256_order;
          == { }
          (pow st1 (arithmetic_shift_right number (256 - index + 1)) * pow st1 (arithmetic_shift_right number (256 - index + 1) + 1)) % prime_p256_order;
          == {pow_plus st1 (arithmetic_shift_right number (256 - index + 1)) (arithmetic_shift_right number (256 - index + 1) + 1)}
          (pow st1 (arithmetic_shift_right number (256 - index + 1) + arithmetic_shift_right number (256 - index + 1) + 1)) % prime_p256_order;
          == {}
          (pow st1 (2* arithmetic_shift_right number (256 - index + 1) + 1)) % prime_p256_order;
          == {lemma_even index k}
          (pow st1 (arithmetic_shift_right number (256 - index) + 1)) % prime_p256_order;
        }
      | 1 ->
        let a0 = pow st1 (arithmetic_shift_right number (256 - index + 1)) in
        let a1 = pow st1 (arithmetic_shift_right number (256 - index + 1) + 1) in
        calc (==) {
          (a1 % prime_p256_order) * (a1 % prime_p256_order) % prime_p256_order;
          == {modulo_distributivity_mult a1 a1 prime_p256_order}
          (a1 * a1) % prime_p256_order;
          == { }
          (pow st1 (arithmetic_shift_right number (256 - index + 1) + 1) * pow st1 (arithmetic_shift_right number (256 - index + 1) + 1)) % prime_p256_order;
          == {pow_plus st1 (arithmetic_shift_right number (256 - index + 1) + 1) (arithmetic_shift_right number (256 - index + 1) + 1)}
          (pow st1 (arithmetic_shift_right number (256 - index + 1) + 1 + arithmetic_shift_right number (256 - index + 1) + 1)) % prime_p256_order;
          == {}
          (pow st1 (2 * arithmetic_shift_right number (256 - index + 1) + 2)) % prime_p256_order;
          == {lemma_odd index k}
          pow st1 (arithmetic_shift_right number newIndex + 1) % prime_p256_order;
        };
        calc (==) {
          (a0 % prime_p256_order) * (a1 % prime_p256_order) % prime_p256_order;
          == {modulo_distributivity_mult a0 a1 prime_p256_order}
          (a0 * a1) % prime_p256_order;
          == { }
          (pow st1 (arithmetic_shift_right number (256 - index + 1)) * pow st1 (arithmetic_shift_right number (256 - index + 1) + 1)) % prime_p256_order;
          == {pow_plus st1 (arithmetic_shift_right number (256 - index + 1)) (arithmetic_shift_right number (256 - index + 1) + 1)}
          (pow st1 (arithmetic_shift_right number (256 - index + 1) + arithmetic_shift_right number (256 - index + 1) + 1)) % prime_p256_order;
          == {}
          (pow st1 (2* arithmetic_shift_right number (256 - index + 1) + 1)) % prime_p256_order;
          == {lemma_odd index k}
          (pow st1 (arithmetic_shift_right (nat_from_bytes_le k) (256 - index)) % prime_p256_order);
        }
    end


unfold let prime_p256_order_inverse_list: list uint8 =
 [
   u8 79;  u8 37;  u8 99;  u8 252; u8 194; u8 202; u8 185; u8 243;
   u8 132; u8 158; u8 23;  u8 167; u8 173; u8 250; u8 230; u8 188;
   u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255;
   u8 0;   u8 0;   u8 0;   u8 0;   u8 255; u8 255; u8 255; u8 255
 ]


let prime_p256_order_inverse_seq: s:lseq uint8 32{nat_from_intseq_le s == prime_p256_order - 2} =
  assert_norm (List.Tot.length prime_p256_order_inverse_list == 32);
  nat_from_intlist_seq_le 32 prime_p256_order_inverse_list;
  assert_norm (nat_from_intlist_le prime_p256_order_inverse_list == prime_p256_order - 2);
  of_list prime_p256_order_inverse_list


unfold let prime_p256_order_list: list uint8 =
 [
  u8 255; u8 255; u8 255; u8 255; u8 0;  u8 0;   u8 0;   u8 0;
  u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255;
  u8 188; u8 230; u8 250; u8 173; u8 167; u8 23; u8 158; u8 132;
  u8 243; u8 185; u8 202; u8 194; u8 252; u8 99; u8 37; u8 81
 ]


let prime_p256_order_seq: s:lseq uint8 32{nat_from_intseq_be s == prime_p256_order} =
  assert_norm (List.Tot.length prime_p256_order_list == 32);
  nat_from_intlist_seq_be 32 prime_p256_order_list;
  assert_norm (nat_from_intlist_be prime_p256_order_list == prime_p256_order);
  of_list prime_p256_order_list


val exponent_spec: a:nat_prime -> r:nat_prime{r = pow a (prime_p256_order - 2) % prime_p256_order}

let exponent_spec a =
  let a0, _ = _exponent_spec prime_p256_order_inverse_seq (1, a) in
  lemma_exponen_spec prime_p256_order_inverse_seq (1, a) 256;
  a0


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


val changeEndianLemma: k: lseq uint64 4 -> Lemma
  (nat_from_intseq_le (changeEndian k) == nat_from_intseq_be k)

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

val changeEndianLemmaI: a: nat {a < pow2 256} -> Lemma
  (changeEndian (nat_to_intseq_le 4 a) == nat_to_intseq_be 4 a)

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


val changeEndian_le_be: a:nat{a < pow2 256} -> Lemma
  (uints_to_bytes_be (changeEndian (nat_to_intseq_le 4 a)) == nat_to_bytes_be 32 a)

let changeEndian_le_be a =
  changeEndianLemmaI a;
  uints_to_bytes_be_nat_lemma #U64 #SEC 4 a


val verifyQValidCurvePointSpec:
  publicKey:tuple3 nat nat nat{~(isPointAtInfinity publicKey)} -> bool

let verifyQValidCurvePointSpec publicKey =
  let (x: nat), (y:nat), (z:nat) = publicKey in
  x < Spec.P256.Definitions.prime256 &&
  y < Spec.P256.Definitions.prime256 &&
  z < Spec.P256.Definitions.prime256 &&
  isPointOnCurve (x, y, z) &&
  isPointAtInfinity (scalar_multiplication prime_p256_order_seq publicKey)


val checkCoordinates: r:nat -> s:nat -> bool

let checkCoordinates r s =
  if r > 0 && r < prime_p256_order && s > 0 && s < prime_p256_order
  then true
  else false

open Spec.Hash.Definitions

val hashSpec: a: hash_alg {SHA2_256? a \/ SHA2_384? a \/ SHA2_512? a} -> 
  Tot (m: bytes {Seq.length m <= max_input_length a}  -> r: Lib.ByteSequence.lbytes (hash_length a))


let hashSpec a = 
  match a with 
  |SHA2_256 -> Spec.Agile.Hash.hash Def.SHA2_256
  |SHA2_384 -> Spec.Agile.Hash.hash Def.SHA2_384
  |SHA2_512 -> Spec.Agile.Hash.hash Def.SHA2_512
    

open Lib.ByteSequence 

val ecdsa_verification_agile:
  alg: hash_alg {SHA2_256? alg \/ SHA2_384? alg \/ SHA2_512? alg} 
  -> publicKey:tuple2 nat nat -> r:nat -> s:nat
  -> mLen:size_nat
  -> m:lseq uint8 mLen
  -> bool

let ecdsa_verification_agile alg publicKey r s mLen m =
  assert_norm (pow2 32 < pow2 61);
  assert_norm (pow2 32 < pow2 125);
  let publicJacobian = toJacobianCoordinates publicKey in
  if not (verifyQValidCurvePointSpec publicJacobian) then false
  else
    begin
    if not (checkCoordinates r s) then false
    else
      begin
      let hashM = (hashSpec alg) m in
      let cutHashM = sub hashM 0 32 in 
      let hashNat = nat_from_bytes_be cutHashM % prime_p256_order in

      let u1 = nat_to_bytes_be 32 (pow s (prime_p256_order - 2) * hashNat % prime_p256_order) in
      let u2 = nat_to_bytes_be 32 (pow s (prime_p256_order - 2) * r % prime_p256_order) in

      let pointAtInfinity = (0, 0, 0) in
      let u1D, _ = montgomery_ladder_spec u1 (pointAtInfinity, basePoint) in
      let u2D, _ = montgomery_ladder_spec u2 (pointAtInfinity, publicJacobian) in

      let sumPoints = _point_add u1D u2D in
      let pointNorm = _norm sumPoints in
      let x, y, z = pointNorm in
      if Spec.P256.isPointAtInfinity pointNorm then false else x = r
    end
  end


val ecdsa_verification_blake2:
  publicKey:tuple2 nat nat -> r:nat -> s:nat
  -> mLen:size_nat
  -> m:lseq uint8 mLen
  -> bool

let ecdsa_verification_blake2 publicKey r s mLen m =
  let publicJacobian = toJacobianCoordinates publicKey in
  if not (verifyQValidCurvePointSpec publicJacobian) then false
  else
    begin
    if not (checkCoordinates r s) then false
    else
      begin
      
      let hashM = Spec.Blake2.blake2b m 0 Seq.Base.empty 32 in
      let hashNat = nat_from_bytes_be hashM % prime_p256_order in

      let u1 = nat_to_bytes_be 32 (pow s (prime_p256_order - 2) * hashNat % prime_p256_order) in
      let u2 = nat_to_bytes_be 32 (pow s (prime_p256_order - 2) * r % prime_p256_order) in

      let pointAtInfinity = (0, 0, 0) in
      let u1D, _ = montgomery_ladder_spec u1 (pointAtInfinity, basePoint) in
      let u2D, _ = montgomery_ladder_spec u2 (pointAtInfinity, publicJacobian) in

      let sumPoints = _point_add u1D u2D in
      let pointNorm = _norm sumPoints in
      let x, y, z = pointNorm in
      if Spec.P256.isPointAtInfinity pointNorm then false else x = r
    end
  end


val ecdsa_verification_without_hash:
  publicKey:tuple2 nat nat -> r:nat -> s:nat
  -> m:lseq uint8 32
  -> bool

let ecdsa_verification_without_hash publicKey r s m =
  let publicJacobian = toJacobianCoordinates publicKey in
  if not (verifyQValidCurvePointSpec publicJacobian) then false
  else
    begin
    if not (checkCoordinates r s) then false
    else
      begin
      
      let hashNat = nat_from_bytes_be m % prime_p256_order in

      let u1 = nat_to_bytes_be 32 (pow s (prime_p256_order - 2) * hashNat % prime_p256_order) in
      let u2 = nat_to_bytes_be 32 (pow s (prime_p256_order - 2) * r % prime_p256_order) in

      let pointAtInfinity = (0, 0, 0) in
      let u1D, _ = montgomery_ladder_spec u1 (pointAtInfinity, basePoint) in
      let u2D, _ = montgomery_ladder_spec u2 (pointAtInfinity, publicJacobian) in

      let sumPoints = _point_add u1D u2D in
      let pointNorm = _norm sumPoints in
      let x, y, z = pointNorm in
      if Spec.P256.isPointAtInfinity pointNorm then false else x = r
    end
  end



val ecdsa_signature_agile:
  alg: hash_alg {SHA2_256? alg \/ SHA2_384? alg \/ SHA2_512? alg}
  -> mLen:size_nat
  -> m:lseq uint8 mLen
  -> privateKey:lseq uint8 32
  -> k:lseq uint8 32
  -> tuple3 nat nat uint64

let ecdsa_signature_agile alg mLen m privateKey k =
  assert_norm (pow2 32 < pow2 61);
  assert_norm (pow2 32 < pow2 125);
  let r, _ = montgomery_ladder_spec k ((0,0,0), basePoint) in
  let (xN, _, _) = _norm r in
  let hashM = (hashSpec alg) m in
  let cutHashM = sub hashM 0 32 in 
  let z = nat_from_bytes_be cutHashM % prime_p256_order in
  let kFelem = nat_from_bytes_be k in
  let privateKeyFelem = nat_from_bytes_be privateKey in
  let resultR = xN % prime_p256_order in
  let resultS = (z + resultR * privateKeyFelem) * pow kFelem (prime_p256_order - 2) % prime_p256_order in
    if resultR = 0 || resultS = 0 then
      resultR, resultS, u64 (pow2 64 - 1)
    else
      resultR, resultS, u64 0


val ecdsa_signature_blake2:
    mLen:size_nat
  -> m:lseq uint8 mLen
  -> privateKey:lseq uint8 32
  -> k:lseq uint8 32
  -> tuple3 nat nat uint64

let ecdsa_signature_blake2 mLen m privateKey k =
  assert_norm (pow2 32 < pow2 61);
  assert_norm (pow2 32 < pow2 125);
  let r, _ = montgomery_ladder_spec k ((0,0,0), basePoint) in
  let (xN, _, _) = _norm r in
  let hashM = Spec.Blake2.blake2b m 0 Seq.Base.empty 32 in
  let z = nat_from_bytes_be hashM % prime_p256_order in
  let kFelem = nat_from_bytes_be k in
  let privateKeyFelem = nat_from_bytes_be privateKey in
  let resultR = xN % prime_p256_order in
  let resultS = (z + resultR * privateKeyFelem) * pow kFelem (prime_p256_order - 2) % prime_p256_order in
    if resultR = 0 || resultS = 0 then
      resultR, resultS, u64 (pow2 64 - 1)
    else
      resultR, resultS, u64 0


val ecdsa_signature_without_hash:
    m:lseq uint8 32
  -> privateKey:lseq uint8 32
  -> k:lseq uint8 32
  -> tuple3 nat nat uint64

let ecdsa_signature_without_hash m privateKey k =
  let r, _ = montgomery_ladder_spec k ((0,0,0), basePoint) in
  let (xN, _, _) = _norm r in
  let z = nat_from_bytes_be m % prime_p256_order in 
  let kFelem = nat_from_bytes_be k in
  let privateKeyFelem = nat_from_bytes_be privateKey in
  let resultR = xN % prime_p256_order in
  let resultS = (z + resultR * privateKeyFelem) * pow kFelem (prime_p256_order - 2) % prime_p256_order in
    if resultR = 0 || resultS = 0 then
      resultR, resultS, u64 (pow2 64 - 1)
    else
      resultR, resultS, u64 0
