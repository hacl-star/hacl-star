module Hacl.Spec.ECDSA.Definition

open Lib.IntTypes
open Lib.ByteSequence

open FStar.Math.Lemmas
open FStar.Math.Lib

open FStar.HyperStack
open FStar.HyperStack.All
open Lib.Sequence
open Lib.Buffer
open FStar.Mul

open Spec.P256

noextract
let prime_p256_order: (a: pos{a < pow2 256}) =
  assert_norm (115792089210356248762697446949407573529996955224135760342422259061068512044369 < pow2 256);
  115792089210356248762697446949407573529996955224135760342422259061068512044369


inline_for_extraction noextract
let p256_order_prime_list : x:list uint64{List.Tot.length x == 4 /\ 
  (
    let open FStar.Mul in 
    let l0 = uint_v (List.Tot.index x 0) in 
    let l1 = uint_v (List.Tot.index x 1) in 
    let l2 = uint_v (List.Tot.index x 2) in 
    let l3 = uint_v (List.Tot.index x 3) in 
    l0 + l1 * pow2 64 + l2 * pow2 128 + l3 * pow2 192 == prime_p256_order)
  } =
  let open FStar.Mul in 
  [@inline_let]
  let x =
    [ (u64 17562291160714782033);  (u64 13611842547513532036); (u64 18446744073709551615);  (u64 18446744069414584320);] in
    assert_norm(17562291160714782033 + 13611842547513532036 * pow2 64 + 18446744073709551615* pow2 128 + 18446744069414584320 * pow2 192 == prime_p256_order);
  x  


unfold let prime_order_inverse_list (#c: curve) : list uint8 = 
  match c with 
  |P256 -> 
    [
      u8 79;  u8 37;  u8 99;  u8 252; u8 194; u8 202; u8 185; u8 243;
      u8 132; u8 158; u8 23;  u8 167; u8 173; u8 250; u8 230; u8 188;
      u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255;
      u8 0;   u8 0;   u8 0;   u8 0;   u8 255; u8 255; u8 255; u8 255
    ]
  |P384 -> 
    [ 
      u8 113; u8 41;  u8 197; u8 204; u8 106; u8 25;  u8 236; u8 236;
      u8 122; u8 167; u8 176; u8 72;  u8 178; u8 13;  u8 26;  u8 88;
      u8 223; u8 45;  u8 55;  u8 244; u8 129; u8 77;  u8 99;  u8 199;
      u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255;
      u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255;
      u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255
   ]

   

inline_for_extraction
let felem (c: curve) = lbuffer uint64 (getCoordinateLenU64 c)

inline_for_extraction 
let widefelem (c: curve) = lbuffer uint64 (getCoordinateLenU64 c *. 2ul)


inline_for_extraction noextract
let felem_coordinate (c: curve) =
  match c with 
  |P256 -> tuple4 uint64 uint64 uint64 uint64
  |P384 -> tuple6 uint64 uint64 uint64 uint64 uint64 uint64


inline_for_extraction noextract
let felem8 = tuple8 uint64 uint64 uint64 uint64 uint64 uint64 uint64 uint64

noextract
val as_nat_coordinate: #c: curve -> f:felem_coordinate c -> GTot nat

let as_nat_coordinate #c f =
  match c with 
  |P256 -> 
    let (s0, s1, s2, s3) : tuple4 uint64 uint64 uint64 uint64 = f in
    v s0 + v s1 * pow2 64 + v s2 * pow2 64 * pow2 64 +
    v s3 * pow2 64 * pow2 64 * pow2 64
  |P384 -> 
    let (s0, s1, s2, s3, s4, s5) : tuple6 uint64 uint64 uint64 uint64 uint64 uint64 = f in
    v s0 + 
    v s1 * pow2 64 + 
    v s2 * pow2 64 * pow2 64 +
    v s3 * pow2 64 * pow2 64 * pow2 64 + 
    v s4 * pow2 64 * pow2 64 * pow2 64 * pow2 64 + 
    v s5 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64
    

noextract
val wide_as_nat4: f:felem8 -> GTot nat
let wide_as_nat4 f =
  let (s0, s1, s2, s3, s4, s5, s6, s7) = f in
  v s0 + v s1 * pow2 64 + v s2 * pow2 64 * pow2 64 +
  v s3 * pow2 64 * pow2 64 * pow2 64 +
  v s4 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
  v s5 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
  v s6 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
  v s7 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64


noextract
let as_nat (c: curve) (h:mem) (e:felem c) : GTot nat =
  match c with 
  |P256 -> 
    let s = as_seq h e in
    let s0 = s.[0] in
    let s1 = s.[1] in
    let s2 = s.[2] in
    let s3 = s.[3] in
    as_nat_coordinate (s0, s1, s2, s3)
  |P384 ->     
    let s = as_seq h e in
    let s0 = s.[0] in
    let s1 = s.[1] in
    let s2 = s.[2] in
    let s3 = s.[3] in
    let s4 = s.[4] in 
    let s5 = s.[5] in 
    as_nat_coordinate (s0, s1, s2, s3, s4, s5)
    
  

noextract
let wide_as_nat (c: curve) (h:mem) (e: widefelem c) : GTot nat =
  let s = as_seq h e in
  let s0 = s.[0] in
  let s1 = s.[1] in
  let s2 = s.[2] in
  let s3 = s.[3] in
  let s4 = s.[4] in
  let s5 = s.[5] in
  let s6 = s.[6] in
  let s7 = s.[7] in
  wide_as_nat4 (s0, s1, s2, s3, s4, s5, s6, s7)




noextract
let felem_seq_as_nat_8 (a: lseq uint64 8) : Tot nat = 
  let open FStar.Mul in 
  let a0 = Lib.Sequence.index a 0 in 
  let a1 = Lib.Sequence.index a 1 in 
  let a2 = Lib.Sequence.index a 2 in 
  let a3 = Lib.Sequence.index a 3 in 
  let a4 = Lib.Sequence.index a 4 in 
  let a5 = Lib.Sequence.index a 5 in 
  let a6 = Lib.Sequence.index a 6 in 
  let a7 = Lib.Sequence.index a 7 in
  uint_v a0 + 
  uint_v a1 * pow2 64 + 
  uint_v a2 * pow2 64 * pow2 64 + 
  uint_v a3 * pow2 64 * pow2 64 * pow2 64 + 
  uint_v a4 * pow2 64 * pow2 64 * pow2 64 * pow2 64 + 
  uint_v a5 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 + 
  uint_v a6 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 + 
  uint_v a7 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64

noextract
let felem_seq = lseq uint64 4

noextract
let felem_seq_as_nat (a: felem_seq) : Tot (n: nat {n < pow2 256})  = 
  let open FStar.Mul in 
  let a0 = Lib.Sequence.index a 0 in 
  let a1 =  Lib.Sequence.index a 1 in 
  let a2 =  Lib.Sequence.index  a 2 in 
  let a3 =  Lib.Sequence.index a 3 in 
  assert_norm( uint_v a0 + uint_v a1 * pow2 64 + uint_v a2 * pow2 64 * pow2 64 + uint_v a3 * pow2 64 * pow2 64 * pow2 64 < pow2 256);
  uint_v a0 + uint_v a1 * pow2 64 + uint_v a2 * pow2 64 * pow2 64 + uint_v a3 * pow2 64 * pow2 64 * pow2 64



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
