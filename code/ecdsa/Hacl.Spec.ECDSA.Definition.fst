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

open Spec.ECC
open Spec.ECC.Curves

open Hacl.Spec.EC.Definition

open Hacl.Impl.EC.Setup


#set-options "--z3rlimit 100"

inline_for_extraction
let p256_order_inverse_list: x: list uint8 {List.Tot.length x == v (getScalarLenBytes P256) /\ 
  lst_as_nat x == getOrder #P256 - 2} = 
  [@inline_let]
  let x = [
      u8 79;  u8 37;  u8 99;  u8 252; u8 194; u8 202; u8 185; u8 243;
      u8 132; u8 158; u8 23;  u8 167; u8 173; u8 250; u8 230; u8 188;
      u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255;
      u8 0;   u8 0;   u8 0;   u8 0;   u8 255; u8 255; u8 255; u8 255] in 
    assert_norm (List.Tot.length x == v (getScalarLenBytes P256));
    admit();
    x


inline_for_extraction
let p384_order_inverse_list: x: list uint8 {List.Tot.length x == v (getScalarLenBytes P384) /\ 
  lst_as_nat x == getOrder #P384 - 2} = 
  [@inline_let]
  let x = [ 
    u8 113; u8 41;  u8 197; u8 204; u8 106; u8 25;  u8 236; u8 236;
    u8 122; u8 167; u8 176; u8 72;  u8 178; u8 13;  u8 26;  u8 88;
    u8 223; u8 45;  u8 55;  u8 244; u8 129; u8 77;  u8 99;  u8 199;
    u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255;
    u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255;
    u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255] in 
  assert_norm (List.Tot.length x == v (getScalarLenBytes P384));
  admit(); 
  x


inline_for_extraction
let order_inverse_list (c: curve): x: list uint8 {List.Tot.length x == v (getScalarLenBytes c) /\
  lst_as_nat x == getOrder #c - 2} = 
  match c with 
  |P256 -> p256_order_inverse_list
  |P384 -> p384_order_inverse_list
  |_ -> admit(); []


inline_for_extraction
let prime256order_buffer: x: glbuffer uint8 32ul {witnessed #uint8 #(size 32) x (Lib.Sequence.of_list (order_inverse_list P256)) /\ recallable x} = 
  createL_global (p256_order_inverse_list)

inline_for_extraction
let prime384order_buffer: x: glbuffer uint8 48ul {witnessed #uint8 #(size 48) x (Lib.Sequence.of_list (order_inverse_list P384)) /\ recallable x} = 
  createL_global (p384_order_inverse_list)


inline_for_extraction
let order_inverse_buffer (#c: curve): x: glbuffer uint8 (getCoordinateLenU c) {
  witnessed #uint8 #(getCoordinateLenU c) x (Lib.Sequence.of_list (order_inverse_list c)) /\ recallable x} = 
  match c with 
  |P256 -> prime256order_buffer
  |P384 -> prime384order_buffer
  |_ -> admit(); prime256order_buffer


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


