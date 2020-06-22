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
let felem4 = tuple4 uint64 uint64 uint64 uint64
inline_for_extraction noextract
let felem8 = tuple8 uint64 uint64 uint64 uint64 uint64 uint64 uint64 uint64
inline_for_extraction noextract
let felem8_32 = tuple8 uint32 uint32 uint32 uint32 uint32 uint32 uint32 uint32
inline_for_extraction noextract
let felem9 = tuple9 uint64 uint64 uint64  uint64 uint64 uint64 uint64 uint64 uint64



noextract
val as_nat4: f:felem4 -> GTot nat
let as_nat4 f =
  let (s0, s1, s2, s3) = f in
  v s0 + v s1 * pow2 64 + v s2 * pow2 64 * pow2 64 +
  v s3 * pow2 64 * pow2 64 * pow2 64


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
let point_seq = Lib.Sequence.lseq uint64 12 

noextract
let felem_seq = lseq uint64 4

inline_for_extraction
let felem = lbuffer uint64 (size 4)
inline_for_extraction 
let widefelem = lbuffer uint64 (size 8)


noextract
let felem_seq_as_nat (a: felem_seq) : Tot nat  = 
  let open FStar.Mul in 
  let a0 = Lib.Sequence.index a 0 in 
  let a1 =  Lib.Sequence.index a 1 in 
  let a2 =  Lib.Sequence.index  a 2 in 
  let a3 =  Lib.Sequence.index a 3 in 
  uint_v a0 + uint_v a1 * pow2 64 + uint_v a2 * pow2 64 * pow2 64 + uint_v a3 * pow2 64 * pow2 64 * pow2 64

let point_prime_to_coordinates (p:point_seq) =
  felem_seq_as_nat (Lib.Sequence.sub p 0 4),
  felem_seq_as_nat (Lib.Sequence.sub p 4 4),
  felem_seq_as_nat (Lib.Sequence.sub p 8 4)
  


noextract
let as_nat (h:mem) (e:felem) : GTot nat =
  let s = as_seq h e in
  let s0 = s.[0] in
  let s1 = s.[1] in
  let s2 = s.[2] in
  let s3 = s.[3] in
  as_nat4 (s0, s1, s2, s3)

noextract
let as_nat_il (h:mem) (e:glbuffer uint64 (size 4)) : GTot nat =
  let s = as_seq h e in
  let s0 = s.[0] in
  let s1 = s.[1] in
  let s2 = s.[2] in
  let s3 = s.[3] in
  as_nat4 (s0, s1, s2, s3)


noextract
let wide_as_nat (h:mem) (e:widefelem) : GTot nat =
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
let felem_seq_prime = a: felem_seq {felem_seq_as_nat a < prime256}
noextract
let point_prime =  p: point_seq{let x = Lib.Sequence.sub p 0 4 in let y = Lib.Sequence.sub p 4 4 in let z = Lib.Sequence.sub p 8 4 in 
  felem_seq_as_nat x < prime256 /\ felem_seq_as_nat y < prime256 /\ felem_seq_as_nat z < prime256} 


inline_for_extraction
type point = lbuffer uint64 (size 12)

type scalar = lbuffer uint8 (size 32)

