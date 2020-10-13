module Hacl.Spec.P256.Definition

open Lib.IntTypes
open FStar.Math.Lemmas
open FStar.Math.Lib

open FStar.HyperStack
open FStar.HyperStack.All
open Lib.ByteSequence
open Lib.Sequence
open Lib.Buffer
open FStar.Mul

open Spec.P256

inline_for_extraction noextract
let p256_prime_list : x:list uint64{List.Tot.length x == 4 /\ 
  (
    let open FStar.Mul in 
    let l0 = uint_v (List.Tot.index x 0) in 
    let l1 = uint_v (List.Tot.index x 1) in 
    let l2 = uint_v (List.Tot.index x 2) in 
    let l3 = uint_v (List.Tot.index x 3) in 
    l0 + l1 * pow2 64 + l2 * pow2 128 + l3 * pow2 192 == prime256)
  } =
  let open FStar.Mul in 
  [@inline_let]
  let x =
    [ (u64 0xffffffffffffffff);  (u64 0xffffffff); (u64 0);  (u64 0xffffffff00000001);] in
    assert_norm(0xffffffffffffffff + 0xffffffff * pow2 64 + 0xffffffff00000001 * pow2 192 == prime256);
  x



inline_for_extraction noextract
let p384_prime_list : x:list uint64{List.Tot.length x == 6 /\ 
  (
    let open FStar.Mul in 
    let l0 = uint_v (List.Tot.index x 0) in 
    let l1 = uint_v (List.Tot.index x 1) in 
    let l2 = uint_v (List.Tot.index x 2) in 
    let l3 = uint_v (List.Tot.index x 3) in 
    let l4 = uint_v (List.Tot.index x 4) in 
    let l5 = uint_v (List.Tot.index x 5) in 
    l0 + l1 * pow2 64 + l2 * pow2 128 + l3 * pow2 192 + l4 * pow2 256 + l5 * pow2 320 == prime384)
  } =
  let open FStar.Mul in 
  [@inline_let]
  let x =
    [ (u64 0xffffffff);  (u64 0xffffffff00000000); (u64 0xfffffffffffffffe);  (u64 0xffffffffffffffff); (u64 0xffffffffffffffff); (u64 0xffffffffffffffff);] in
    assert_norm(0xffffffff + 0xffffffff00000000 * pow2 64 + 0xfffffffffffffffe * pow2 128 + 
    0xffffffffffffffff * pow2 192 +  0xffffffffffffffff * pow2 256 +  0xffffffffffffffff * pow2 320 == prime384);
  x


inline_for_extraction noextract
let prime_list (c: curve) :  (x: list uint64 {List.Tot.length x == uint_v (getCoordinateLenU64 c) /\ (
  match c with
  |P256 -> 
    let open FStar.Mul in 
    let l0 = uint_v (List.Tot.index x 0) in 
    let l1 = uint_v (List.Tot.index x 1) in 
    let l2 = uint_v (List.Tot.index x 2) in 
    let l3 = uint_v (List.Tot.index x 3) in 
    l0 + l1 * pow2 64 + l2 * pow2 128 + l3 * pow2 192 == prime256
  |P384 -> 
    let open FStar.Mul in 
    let l0 = uint_v (List.Tot.index x 0) in 
    let l1 = uint_v (List.Tot.index x 1) in 
    let l2 = uint_v (List.Tot.index x 2) in 
    let l3 = uint_v (List.Tot.index x 3) in 
    let l4 = uint_v (List.Tot.index x 4) in 
    let l5 = uint_v (List.Tot.index x 5) in 
    l0 + l1 * pow2 64 + l2 * pow2 128 + l3 * pow2 192 + l4 * pow2 256 + l5 * pow2 320 == prime384
)}) = 
  let open FStar.Mul in 
  match c with 
  |P256 -> 
    p256_prime_list
  |P384 -> 
    p384_prime_list


inline_for_extraction noextract
let p256_order_list : x:list uint64 {List.Tot.length x == 4 /\ 
  (
    let open FStar.Mul in 
    let l0 = uint_v (List.Tot.index x 0) in 
    let l1 = uint_v (List.Tot.index x 1) in 
    let l2 = uint_v (List.Tot.index x 2) in 
    let l3 = uint_v (List.Tot.index x 3) in 
    l0 + l1 * pow2 64 + l2 * pow2 128 + l3 * pow2 192 == getOrder #P256)
  } =
  let open FStar.Mul in 
  [@inline_let]
  let x =
    [ (u64 17562291160714782033);  (u64 13611842547513532036); (u64 18446744073709551615);  (u64 18446744069414584320);] in
    assert_norm(17562291160714782033 + 13611842547513532036 * pow2 64 + 18446744073709551615* pow2 128 + 18446744069414584320 * pow2 192 == getOrder #P256);
  x  


inline_for_extraction noextract
let p384_order_list : x:list uint64 {List.Tot.length x == 6 /\ 
  (
    let open FStar.Mul in 
    let l0 = uint_v (List.Tot.index x 0) in 
    let l1 = uint_v (List.Tot.index x 1) in 
    let l2 = uint_v (List.Tot.index x 2) in 
    let l3 = uint_v (List.Tot.index x 3) in 
    let l4 = uint_v (List.Tot.index x 4) in 
    let l5 = uint_v (List.Tot.index x 5) in 
    l0 + l1 * pow2 64 + l2 * pow2 128 + l3 * pow2 192 + l4 * pow2 256 + l5 * pow2 320 ==  getOrder #P384)
  } =
  let open FStar.Mul in 
  [@inline_let]
  let x =
    [ (u64 17072048233947408755);  (u64 6348401684107011962); (u64 14367412456785391071);  
      (u64 18446744073709551615); (u64 18446744073709551615); (u64 18446744073709551615)
    ] in
    assert_norm(17072048233947408755 + 6348401684107011962 * pow2 64 + 14367412456785391071 * pow2 128 + 18446744073709551615 * pow2 192 + 18446744073709551615 * pow2 256 + 18446744073709551615 * pow2 320 
    == getOrder #P384);
  x  


inline_for_extraction noextract
let order_list (c: curve) :  
  (x: list uint64 {List.Tot.length x == uint_v (getCoordinateLenU64 c) /\ (
  match c with
  |P256 -> 
    let open FStar.Mul in 
    let l0 = uint_v (List.Tot.index x 0) in 
    let l1 = uint_v (List.Tot.index x 1) in 
    let l2 = uint_v (List.Tot.index x 2) in 
    let l3 = uint_v (List.Tot.index x 3) in 
    l0 + l1 * pow2 64 + l2 * pow2 128 + l3 * pow2 192 == prime256
  |P384 -> 
    let open FStar.Mul in 
    let l0 = uint_v (List.Tot.index x 0) in 
    let l1 = uint_v (List.Tot.index x 1) in 
    let l2 = uint_v (List.Tot.index x 2) in 
    let l3 = uint_v (List.Tot.index x 3) in 
    let l4 = uint_v (List.Tot.index x 4) in 
    let l5 = uint_v (List.Tot.index x 5) in 
    l0 + l1 * pow2 64 + l2 * pow2 128 + l3 * pow2 192 + l4 * pow2 256 + l5 * pow2 320 == prime384
)}) = 
  let open FStar.Mul in 
  match c with 
  |P256 -> 
    p256_order_list
  |P384 -> 
    p384_order_list


inline_for_extraction noextract
let p256_inverse_list: x: list uint8 = 
  [
      u8 253; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255;
      u8 255; u8 255; u8 255; u8 255; u8 0;   u8 0;   u8 0;   u8 0;
      u8 0;   u8 0;   u8 0;   u8 0;   u8 0;   u8 0;   u8 0;   u8 0;
      u8 1;   u8 0;   u8 0;   u8 0;   u8 255; u8 255; u8 255;  u8 255
  ]


inline_for_extraction noextract
let p384_inverse_list: x: list uint8 = 
  [ 
    u8 253; u8 255; u8 255; u8 255; u8 0;   u8 0;   u8 0;   u8 0;
    u8 0;   u8 0  ; u8 0  ; u8 0  ; u8 255; u8 255; u8 255; u8 255;
    u8 254; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255;
    u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255;
    u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255;
    u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255
  ]


inline_for_extraction noextract
let prime_inverse_list (c: curve) : x: list uint8 = 
  match c with 
  |P256 -> 
    p256_inverse_list
  |P384 -> 
    p384_inverse_list

(* 

let prime_inverse_seq (#c: curve) : (s:lseq uint8 (getCoordinateLen c) {nat_from_intseq_le s == getPrime c - 2}) =  
  assert_norm (List.Tot.length (prime_order_inverse_list #P256) == getCoordinateLen P256);
  assert_norm (List.Tot.length (prime_order_inverse_list #P384) == getCoordinateLen P384);
  nat_from_intlist_seq_le (getCoordinateLen c) (prime_order_inverse_list #c); 
  assert_norm (nat_from_intlist_le (prime_order_inverse_list #P256) == getPrimeOrder #P256 - 2);
  assert_norm (nat_from_intlist_le (prime_order_inverse_list #P384) == getPrimeOrder #P384 - 2);
  of_list (prime_inverse_list #c)
 *)


inline_for_extraction noextract
let felem_coordinate (c: curve) =
  match c with 
  |P256 -> tuple4 uint64 uint64 uint64 uint64
  |P384 -> tuple6 uint64 uint64 uint64 uint64 uint64 uint64


inline_for_extraction noextract
let widefelem_t (c: curve) = 
  match c with 
  |P256 -> 
    tuple8 uint64 uint64 uint64 uint64 uint64 uint64 uint64 uint64 
  |P384 -> 
    tuple12 uint64 uint64 uint64 uint64 uint64 uint64 uint64 uint64 uint64 uint64 uint64 uint64


inline_for_extraction noextract
let felem8_32 = tuple8 uint32 uint32 uint32 uint32 uint32 uint32 uint32 uint32
inline_for_extraction noextract
let felem9 = tuple9 uint64 uint64 uint64  uint64 uint64 uint64 uint64 uint64 uint64


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


#set-options " --z3rlimit 200"

noextract
val wide_as_nat4: #c: curve -> f: widefelem_t c -> GTot nat

let wide_as_nat4 #c f =
  match c with 
  |P256 -> 
    let (s0, s1, s2, s3, s4, s5, s6, s7) : widefelem_t P256 = f in
    v s0 + v s1 * pow2 64 + v s2 * pow2 64 * pow2 64 +
    v s3 * pow2 64 * pow2 64 * pow2 64 +
    v s4 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
    v s5 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
    v s6 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
    v s7 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64
  |P384 -> 
    let (s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11) : widefelem_t P384 = f in
     v s0 + 
     v s1 * pow2 64 + 
     v s2 * pow2 64 * pow2 64 +
     v s3 * pow2 64 * pow2 64 * pow2 64 +
     v s4 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
     v s5 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
     v s6 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
     v s7 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64  +
     v s8 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 + 
     v s9 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
    v s10 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 + 
    v s11 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 


noextract
let point_seq (c: curve) = Lib.Sequence.lseq uint64 (uint_v (getCoordinateLenU64 c) * 3)

noextract
let felem_seq (c: curve) = lseq uint64 (uint_v (getCoordinateLenU64 c))

inline_for_extraction
let felem (c: curve) = lbuffer uint64 (getCoordinateLenU64 c)

inline_for_extraction 
let widefelem (c: curve) = lbuffer uint64 (getCoordinateLenU64 c *. 2ul)


noextract
let felem_seq_as_nat (c: curve) (a: felem_seq c) : Tot nat  = 
  let open FStar.Mul in 
  match c with 
  |P256 -> 
    let a0 = Lib.Sequence.index a 0 in 
    let a1 = Lib.Sequence.index a 1 in 
    let a2 = Lib.Sequence.index a 2 in 
    let a3 = Lib.Sequence.index a 3 in 
    uint_v a0 + uint_v a1 * pow2 64 + uint_v a2 * pow2 64 * pow2 64 + uint_v a3 * pow2 64 * pow2 64 * pow2 64
  |P384 -> 
    let a0 = Lib.Sequence.index a 0 in 
    let a1 = Lib.Sequence.index a 1 in 
    let a2 = Lib.Sequence.index a 2 in 
    let a3 = Lib.Sequence.index a 3 in 
    let a4 = Lib.Sequence.index a 4 in 
    let a5 = Lib.Sequence.index a 5 in 
    uint_v a0 + 
    uint_v a1 * pow2 64 + 
    uint_v a2 * pow2 64 * pow2 64 + 
    uint_v a3 * pow2 64 * pow2 64 * pow2 64 +
    uint_v a4 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
    uint_v a5 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64



let point_prime_to_coordinates (c: curve) (p:point_seq c) =
  let len = uint_v (getCoordinateLenU64 c) in 
  felem_seq_as_nat c (Lib.Sequence.sub p 0 len),
  felem_seq_as_nat c (Lib.Sequence.sub p len len),
  felem_seq_as_nat c (Lib.Sequence.sub p (len * 2) len)
  

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
let as_nat_il (c: curve) (h:mem) (e:glbuffer uint64 (getCoordinateLenU64 c)) : GTot nat =
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
  match c with 
  |P256 -> 
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
  |P384 ->
    let s = as_seq h e in
    let s0 = s.[0] in
    let s1 = s.[1] in
    let s2 = s.[2] in
    let s3 = s.[3] in
    let s4 = s.[4] in
    let s5 = s.[5] in
    let s6 = s.[6] in
    let s7 = s.[7] in
    let s8 = s.[8] in 
    let s9 = s.[9] in 
    let s10 = s.[10] in 
    let s11 = s.[11] in 
    wide_as_nat4 (s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11)


noextract
let felem_seq_as_nat_8 (a: lseq uint64 8) : GTot nat = 
  let open FStar.Mul in 
  let s0 = Lib.Sequence.index a 0 in 
  let s1 = Lib.Sequence.index a 1 in 
  let s2 = Lib.Sequence.index a 2 in 
  let s3 = Lib.Sequence.index a 3 in 
  let s4 = Lib.Sequence.index a 4 in 
  let s5 = Lib.Sequence.index a 5 in 
  let s6 = Lib.Sequence.index a 6 in 
  let s7 = Lib.Sequence.index a 7 in
  wide_as_nat4 (s0, s1, s2, s3, s4, s5, s6, s7)

noextract
let felem_seq_as_nat_12 (a: lseq uint64 12) : GTot nat = 
  let open FStar.Mul in 
  let s0 = Lib.Sequence.index a 0 in 
  let s1 = Lib.Sequence.index a 1 in 
  let s2 = Lib.Sequence.index a 2 in 
  let s3 = Lib.Sequence.index a 3 in 
  let s4 = Lib.Sequence.index a 4 in 
  let s5 = Lib.Sequence.index a 5 in

  let s6 = Lib.Sequence.index a 6 in 
  let s7 = Lib.Sequence.index a 7 in
  let s8 = Lib.Sequence.index a 8 in 
  let s9 = Lib.Sequence.index a 9 in 
  let s10 = Lib.Sequence.index a 10 in 
  let s11 = Lib.Sequence.index a 11 in 

  wide_as_nat4 #P384 (s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11)


open FStar.Mul

noextract
let felem_seq_prime (c: curve) = a: felem_seq c {felem_seq_as_nat c a < getPrime c}

noextract
let point_primeF (c: curve) =  
  p: point_seq c {
    let len = uint_v (getCoordinateLenU64 c) in 
    let prime = getPrime c in 

    let x = Lib.Sequence.sub p 0 len in 
    let y = Lib.Sequence.sub p len len in 
    let z = Lib.Sequence.sub p (2 * len) len in 
    
    felem_seq_as_nat c x < prime /\ 
    felem_seq_as_nat c y < prime /\ 
    felem_seq_as_nat c z < prime} 


inline_for_extraction
type point (c: curve) = lbuffer uint64 (getCoordinateLenU64 c *. 3ul)

type scalar (c: curve) = lbuffer uint8 (getScalarLen c)



noextract 
let point_x_as_nat (c: curve) (h: mem) (e: point c) : GTot nat = 
  as_nat c h (gsub e (size 0) (getCoordinateLenU64 c))


noextract 
let point_y_as_nat (c: curve) (h: mem) (e: point c) : GTot nat = 
  as_nat c h (gsub e (getCoordinateLenU64 c) (getCoordinateLenU64 c))

noextract 
let point_z_as_nat (c: curve) (h: mem) (e: point c) : GTot nat = 
  as_nat c h (gsub e (size 2 *! getCoordinateLenU64 c) (getCoordinateLenU64 c))


val felem_eval: c: curve -> h: mem -> f: felem c -> Type0

let felem_eval c h f = live h f /\ as_nat c h f < getPrime c



val changeEndianStep: #c: curve 
  -> i: nat {i <= v (shift_right (getCoordinateLenU64 c) 1ul)}  -> felem_seq c -> felem_seq c 

let changeEndianStep #c i b =
  let len = v (getCoordinateLenU64 c) in 
  let lenRight = len - 1 - i in 
  let left = Lib.Sequence.index b i in 
  let right = Lib.Sequence.index b lenRight in 
  let b = Lib.Sequence.upd b i right in 
  Lib.Sequence.upd b lenRight left


(* If you have imagination, it's indeed like this *)
val changeEndian: #c: curve -> felem_seq c -> felem_seq c

let changeEndian #c b =
  let len = getCoordinateLenU64 c in 
  let lenByTwo = shift_right len 1ul in 
  Lib.LoopCombinators.repeati (v lenByTwo) (changeEndianStep) b


val changeEndianLemma: #c: curve -> k: lseq uint64 (getCoordinateLen c) -> Lemma
  (nat_from_intseq_le (changeEndian #c k) == nat_from_intseq_be k)

let changeEndianLemma #c k =
  let k0 = changeEndian #c k in

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


val changeEndianLemmaI: #c: curve -> a: nat {a < getPower2 c} -> Lemma
  (changeEndian #c (nat_to_intseq_le (uint_v (getCoordinateLenU64 c)) a) == nat_to_intseq_be (uint_v (getCoordinateLenU64 c)) a)

let changeEndianLemmaI #c a =
  let len = getCoordinateLenU64 c in
  let a0 = nat_to_intseq_le #U64 #SEC 4 a in
  index_nat_to_intseq_le #U64 #SEC  4 a 0;
  index_nat_to_intseq_le #U64 #SEC  4 a 1;
  index_nat_to_intseq_le #U64 #SEC  4 a 2;
  index_nat_to_intseq_le #U64 #SEC  4 a 3;

  index_nat_to_intseq_be #U64 #SEC 4 a 0;
  index_nat_to_intseq_be #U64 #SEC 4 a 2;
  index_nat_to_intseq_be #U64 #SEC 4 a 3;
  index_nat_to_intseq_be #U64 #SEC 4 a 1;


  assert(Lib.Sequence.index #_ #4 (changeEndian #c (nat_to_intseq_le #U64 #SEC 4 a)) 3 == Lib.Sequence.index #_ #4 (nat_to_intseq_be #U64 #SEC 4 a) 3);

  assert(Lib.Sequence.index #_ #4 (changeEndian #c (nat_to_intseq_le #U64 #SEC 4 a)) 2 == Lib.Sequence.index #_ #4 (nat_to_intseq_be #U64 #SEC 4 a) 2);

  assert(Lib.Sequence.index #_ #4 (changeEndian #c (nat_to_intseq_le #U64 #SEC 4 a)) 1 == Lib.Sequence.index #_ #4 (nat_to_intseq_be #U64 #SEC 4 a) 1);

  assert(Lib.Sequence.index #_ #4 (changeEndian #c (nat_to_intseq_le #U64 #SEC 4 a)) 0 == Lib.Sequence.index #_ #4 (nat_to_intseq_be #U64 #SEC 4 a) 0);
  eq_intro (changeEndian #c (nat_to_intseq_le #U64 #SEC 4 a)) (nat_to_intseq_be 4 a)


val changeEndian_le_be: #c: curve -> a:nat{a < getPower2 c} -> Lemma
  (uints_to_bytes_be (changeEndian #c (nat_to_intseq_le (uint_v (getCoordinateLenU64 c)) a)) == nat_to_bytes_be (getCoordinateLen c) a)

let changeEndian_le_be #c a =
  changeEndianLemmaI #c a;
  uints_to_bytes_be_nat_lemma #U64 #SEC (uint_v (getCoordinateLenU64 c)) a


val lemmaPowerMoreThanU64: #c: curve -> Lemma (getPower2 c > pow2 64)

let lemmaPowerMoreThanU64 #c = 
  assert_norm (getPower2 P256 > pow2 64);
  assert_norm (getPower2 P384 > pow2 64)


val lemmaPrimeLowerBound: #c: curve -> Lemma (getPrime c > pow2 (getPower c - 1))

let lemmaPrimeLowerBound #c = 
  assert_norm (getPrime P256 > pow2 (getPower P256 - 1));  
  assert_norm (getPrime P384 > pow2 (getPower P384 - 1))
