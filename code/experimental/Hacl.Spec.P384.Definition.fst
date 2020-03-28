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
let prime384: (a: pos { a < pow2 384}) = 
  pow2 384 - pow2 128 - pow2 96 + pow2 32 - 1


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
  v s2 * pow2 64 * pow2 64 +
  v s3 * pow2 64 * pow2 64 * pow2 64 + 
  v s4 * pow2 64 * pow2 64 * pow2 64 * pow2 64 + 
  v s5 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
  v s6 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
  v s7 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
  v s8 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 + 
  v s9 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
  v s10* pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
  v s11 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64



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
