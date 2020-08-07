module Hacl.Spec.P256.Definition

open Lib.IntTypes
open FStar.Math.Lemmas
open FStar.Math.Lib

open FStar.HyperStack
open FStar.HyperStack.All
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
    [ (u64 0xffffffffffffffff);  (u64 0xffffffff); (u64 0);  (u64 0xffffffff00000001);] in
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
let felem_coordinate (c: curve) =
  match c with 
  |P256 -> tuple4 uint64 uint64 uint64 uint64
  |P384 -> tuple6 uint64 uint64 uint64 uint64 uint64 uint64

inline_for_extraction noextract
let felem8 = tuple8 uint64 uint64 uint64 uint64 uint64 uint64 uint64 uint64
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



open FStar.Mul

noextract
let felem_seq_prime (c: curve) = a: felem_seq c {felem_seq_as_nat c a < getPrime c}
noextract
let point_prime (c: curve) =  p: point_seq c {let x = Lib.Sequence.sub p 0 4 in let y = Lib.Sequence.sub p 4 4 in let z = Lib.Sequence.sub p 8 4 in 
  felem_seq_as_nat c x < prime256 /\ felem_seq_as_nat c y < prime256 /\ felem_seq_as_nat c z < prime256} 


inline_for_extraction
type point (c: curve) = lbuffer uint64 (getCoordinateLenU64 c *. 3ul)

type scalar (c: curve) = lbuffer uint8 (getScalarLen c)

