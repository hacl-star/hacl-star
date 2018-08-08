module Views

open LowStar.BufferView
open Words_s
open Types_s
open Opaque_s

//module U8 = FStar.UInt8
module U8 = SecretByte

let get8_def (s:Seq.lseq U8.t 1) = Seq.index s 0
let put8_def (x:U8.t) : GTot (Seq.lseq U8.t 1) =
  let contents (i:nat{i<1}) = x in
  Seq.init 1 contents

let get8 = make_opaque get8_def
let put8 = make_opaque put8_def

val inverses8 (u:unit) : Lemma (inverses get8 put8)

let view8 = inverses8 (); View 1 get8 put8

let get16_def (s:Seq.lseq U8.t 2) = UInt16.uint_to_t (
  U8.v (Seq.index s 0) +
  U8.v (Seq.index s 1) `op_Multiply` 0x100
  )
let put16_def (x:UInt16.t) : GTot (Seq.lseq U8.t 2) =
  let s = Seq.create 2 (U8.uint_to_t 0) in
  let x = UInt16.v x in
  let s = Seq.upd s 0 (U8.uint_to_t (x % 0x100)) in
  let x = x `op_Division` 0x100 in
  let s = Seq.upd s 1 (U8.uint_to_t (x % 0x100)) in
  s

let get16 = make_opaque get16_def
let put16 = make_opaque put16_def

val inverses16 (u:unit) : Lemma (inverses get16 put16)

let view16 = inverses16 (); View 2 get16 put16

let get32_def (s:Seq.lseq U8.t 4) = UInt32.uint_to_t (
  U8.v (Seq.index s 0) +
  U8.v (Seq.index s 1) `op_Multiply` 0x100 +
  U8.v (Seq.index s 2) `op_Multiply` 0x10000 +
  U8.v (Seq.index s 3) `op_Multiply` 0x1000000
  )
let put32_def (x:UInt32.t) : GTot (Seq.lseq U8.t 4) =
  let s = Seq.create 4 (U8.uint_to_t 0) in
  let x = UInt32.v x in
  let s = Seq.upd s 0 (U8.uint_to_t (x % 0x100)) in
  let x = x `op_Division` 0x100 in
  let s = Seq.upd s 1 (U8.uint_to_t (x % 0x100)) in
  let x = x `op_Division` 0x100 in
  let s = Seq.upd s 2 (U8.uint_to_t (x % 0x100)) in
  let x = x `op_Division` 0x100 in
  let s = Seq.upd s 3 (U8.uint_to_t (x % 0x100)) in
  s

let get32 = make_opaque get32_def
let put32 = make_opaque put32_def

val inverses32 (u:unit) : Lemma (inverses get32 put32)

let view32 = inverses32(); View 4 get32 put32

let nat8s_to_nat64 (v1 v2 v3 v4 v5 v6 v7 v8:nat8) : nat64 =
    v1 +
    v2 `op_Multiply` 0x100 +
    v3 `op_Multiply` 0x10000 +
    v4 `op_Multiply` 0x1000000 +
    v5 `op_Multiply` 0x100000000 +
    v6 `op_Multiply` 0x10000000000 +
    v7 `op_Multiply` 0x1000000000000 +
    v8 `op_Multiply` 0x100000000000000

let get64_def (s:Seq.lseq U8.t 8) =
  UInt64.uint_to_t (
  nat8s_to_nat64
    (U8.v (Seq.index s 0))
    (U8.v (Seq.index s 1))
    (U8.v (Seq.index s 2))
    (U8.v (Seq.index s 3))
    (U8.v (Seq.index s 4))
    (U8.v (Seq.index s 5))
    (U8.v (Seq.index s 6))
    (U8.v (Seq.index s 7))
  )

let put64_def (a:UInt64.t) : GTot (Seq.lseq U8.t 8) =
  let u0 = UInt32.uint_to_t (UInt64.v a % 0x100000000) in
  let u1 = UInt32.uint_to_t ((UInt64.v a / 0x100000000) % 0x100000000) in
  let s0 = put32_def u0 in
  let s1 = put32_def u1 in
  Seq.append s0 s1


let get64 = make_opaque get64_def
let put64 = make_opaque put64_def

val inverses64 (u:unit) : Lemma (inverses get64 put64)

let view64 = inverses64 (); View 8 get64 put64

let nat8s_to_nat32 (v1 v2 v3 v4:nat8) : nat32 =
    v1 +
    v2 `op_Multiply` 0x100 +
    v3 `op_Multiply` 0x10000 +
    v4 `op_Multiply` 0x1000000

let get128_def (s:Seq.lseq U8.t 16) =
  Mkfour
  (nat8s_to_nat32
    (U8.v (Seq.index s 0))
    (U8.v (Seq.index s 1))
    (U8.v (Seq.index s 2))
    (U8.v (Seq.index s 3)))
 (nat8s_to_nat32
    (U8.v (Seq.index s 4))
    (U8.v (Seq.index s 5))
    (U8.v (Seq.index s 6))
    (U8.v (Seq.index s 7)))
 (nat8s_to_nat32
    (U8.v (Seq.index s 8))
    (U8.v (Seq.index s 9))
    (U8.v (Seq.index s 10))
    (U8.v (Seq.index s 11)))
 (nat8s_to_nat32
    (U8.v (Seq.index s 12))
    (U8.v (Seq.index s 13))
    (U8.v (Seq.index s 14))
    (U8.v (Seq.index s 15)))

let put128_def (a:quad32) : GTot (Seq.lseq U8.t 16) =
  let s0 = put32 (UInt32.uint_to_t a.lo0) in
  let s1 = put32 (UInt32.uint_to_t a.lo1) in
  let s2 = put32 (UInt32.uint_to_t a.hi2) in
  let s3 = put32 (UInt32.uint_to_t a.hi3) in
  Seq.append (Seq.append s0 s1) (Seq.append s2 s3)

let get128 = make_opaque get128_def
let put128 = make_opaque put128_def

val inverses128 (u:unit) : Lemma (inverses get128 put128)

let view128 = inverses128 (); View 16 get128 put128

