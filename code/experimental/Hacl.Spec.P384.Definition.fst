module Hacl.Spec.P384.Definition

open Lib.IntTypes
open FStar.Math.Lemmas
open FStar.Math.Lib

open FStar.HyperStack
open FStar.HyperStack.All
open Lib.Sequence
open Lib.Buffer
open FStar.Mul


noextract 
let prime384: (a: pos {a > 3 && a < pow2 384}) = 
  assert_norm (pow2 384 - pow2 128 - pow2 96 + pow2 32 - 1 < pow2 384);
  assert_norm (pow2 384 - pow2 128 - pow2 96 + pow2 32 - 1 > 3);
  pow2 384 - pow2 128 - pow2 96 + pow2 32 - 1


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
    l0 + l1 * pow2 64 + l2 * pow2 (2 * 64) + l3 * pow2 (3 * 64) + l4 * pow2 (4 * 64) + l5 * pow2 (5 * 64) == prime384)
  } =
  let open FStar.Mul in 
  [@inline_let]
  let x =
    [ (u64 0x00000000ffffffff);  
      (u64 0xffffffff00000000);
      (u64 0xfffffffffffffffe);  
      (u64 0xffffffffffffffff);
      (u64 0xffffffffffffffff);
      (u64 0xffffffffffffffff)
    ] in
    assert_norm(
      0x00000000ffffffff + 
      0xffffffff00000000 * pow2 64 + 
      0xfffffffffffffffe * pow2 (2 * 64) +
      0xffffffffffffffff * pow2 (3 * 64) +
      0xffffffffffffffff * pow2 (4 * 64) +
      0xffffffffffffffff * pow2 (5 * 64) == prime384);
  x


noextract
let felem6_tuple = tuple6 uint64 uint64 uint64 uint64 uint64 uint64
noextract
let felem12_tuple = tuple12 uint64 uint64 uint64 uint64 uint64 uint64 uint64 uint64 uint64 uint64 uint64 uint64


noextract
val as_nat_t_6: f:felem6_tuple -> GTot nat
let as_nat_t_6 f =
  let (s0, s1, s2, s3, s4, s5) = f in
  v s0 + 
  v s1 * pow2 64 + 
  v s2 * pow2 (2 * 64) +
  v s3 * pow2 (3 * 64) + 
  v s4 * pow2 (4 * 64) + 
  v s5 * pow2 (5 * 64)


#reset-options "--fuel 0 --ifuel 0 --z3rlimit 50"

noextract
val as_nat_t_12: f:felem12_tuple -> GTot nat

let as_nat_t_12 f =
  let (s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11) = f in
  v s0 + 
  v s1 * pow2 64 + 
  v s2 * pow2 (2 * 64) +
  v s3 * pow2 (3 * 64) +  
  v s4 * pow2 (4 * 64) +
  v s5 * pow2 (5 * 64) +
  v s6 * pow2 (6 * 64) +
  v s7 * pow2 (7 * 64) +
  v s8 * pow2 (8 * 64) +
  v s9 * pow2 (9 * 64) +
  v s10* pow2 (10 * 64) +
  v s11 * pow2 (11 * 64)



inline_for_extraction
let felem4 = lbuffer uint64 (size 4)
inline_for_extraction
let felem6_buffer = lbuffer uint64 (size 6)
inline_for_extraction 
let felem12_buffer = lbuffer uint64 (size 12)


noextract
let as_nat6 (h:mem) (e:felem6_buffer) : GTot nat =
  let s = as_seq h e in
  let s0 = s.[0] in
  let s1 = s.[1] in
  let s2 = s.[2] in
  let s3 = s.[3] in
  let s4 = s.[4] in 
  let s5 = s.[5] in 
  as_nat_t_6 (s0, s1, s2, s3, s4, s5)


noextract
let as_nat6_il (h:mem) (e:ilbuffer uint64 (size 6)) : GTot nat =
  let s = as_seq h e in
  let s0 = s.[0] in
  let s1 = s.[1] in
  let s2 = s.[2] in
  let s3 = s.[3] in
  let s4 = s.[4] in 
  let s5 = s.[5] in 
  as_nat_t_6 (s0, s1, s2, s3, s4, s5)


noextract 
let as_nat12 (h: mem) (e: felem12_buffer) : GTot nat = 
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
  as_nat_t_12 (s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11)


noextract 
let seq_as_nat6 (s: lseq uint64 6) : GTot nat = 
  let s0 = s.[0] in
  let s1 = s.[1] in
  let s2 = s.[2] in
  let s3 = s.[3] in
  let s4 = s.[4] in 
  let s5 = s.[5] in  
  as_nat_t_6 (s0, s1, s2, s3, s4, s5)


noextract 
let seq_as_nat12 (s: lseq uint64 12) : GTot nat = 
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
  as_nat_t_12 (s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11)
