module Views

open LowStar.BufferView
open Words_s
open Types_s
open Opaque_s
open Collections.Seqs_s
open Words.Seq_s
open Words.Seq

module U8 = FStar.UInt8

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

let get64_def (s:Seq.lseq U8.t 8) =
  UInt64.uint_to_t (le_bytes_to_nat64 (seq_uint8_to_seq_nat8 s))

let put64_def (a:UInt64.t) : GTot (Seq.lseq U8.t 8) =
  seq_nat8_to_seq_uint8 (le_nat64_to_bytes (UInt64.v a))

let get64 = make_opaque get64_def
let put64 = make_opaque put64_def

val inverses64 (u:unit) : Lemma (inverses get64 put64)

let view64 = inverses64 (); View 8 get64 put64

let get128_def (s:Seq.lseq U8.t 16) =
  le_bytes_to_quad32 (seq_uint8_to_seq_nat8 s)

let put128_def (a:quad32) : GTot (Seq.lseq U8.t 16) =
  seq_nat8_to_seq_uint8 (le_quad32_to_bytes a)

let get128 = make_opaque get128_def
let put128 = make_opaque put128_def

val inverses128 (u:unit) : Lemma (inverses get128 put128)

let view128 = inverses128 (); View 16 get128 put128

open FStar.Mul

let nat32s_to_nat128 (v1 v2 v3 v4: nat32): nat128 =
  v1 + v2 * 0x100000000 + v3 * 0x1000000000000 + v4 * 0x1000000000000000000000000

module U32 = FStar.UInt32

let get32_128_def (s: Seq.lseq U32.t 4) : quad32 =
  seq_to_four_LE (seq_map UInt32.v s)

let put32_128_def (a:quad32) : GTot (Seq.lseq U32.t 4) =
  seq_map UInt32.uint_to_t (four_to_seq_LE a)

let get32_128 = make_opaque get32_128_def
let put32_128 = make_opaque put32_128_def

val inverses32_128 (u: unit): Lemma (inverses get32_128 put32_128)

let view32_128 = inverses32_128 (); View 4 get32_128 put32_128
