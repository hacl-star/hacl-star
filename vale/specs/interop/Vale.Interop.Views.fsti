module Vale.Interop.Views

module DV = LowStar.BufferView.Down
module BV = LowStar.BufferView.Up
open FStar.Mul
open Vale.Def.Words_s
open Vale.Def.Types_s
open Vale.Def.Opaque_s
open Vale.Lib.Seqs_s
open Vale.Def.Words.Seq_s
open Vale.Def.Words.Seq
open Vale.Def.Words.Four_s

module U8 = FStar.UInt8

[@"opaque_to_smt"]
let get8 (s:Seq.lseq U8.t 1) = Seq.index s 0

[@"opaque_to_smt"]
let put8 (x:U8.t) : GTot (Seq.lseq U8.t 1) =
  let contents (i:nat{i<1}) = x in
  Seq.init 1 contents

val inverses8 (u:unit) : Lemma (DV.inverses get8 put8)

let up_view8 = inverses8 (); BV.View 1 get8 put8
let down_view8 = inverses8 (); DV.View 1 put8 get8

[@"opaque_to_smt"]
let get16 (s:Seq.lseq U8.t 2) = UInt16.uint_to_t (
  U8.v (Seq.index s 0) +
  U8.v (Seq.index s 1) * 0x100
  )

[@"opaque_to_smt"]
let put16 (x:UInt16.t) : GTot (Seq.lseq U8.t 2) =
  let s = Seq.create 2 (U8.uint_to_t 0) in
  let x = UInt16.v x in
  let s = Seq.upd s 0 (U8.uint_to_t (x % 0x100)) in
  let x = x `op_Division` 0x100 in
  let s = Seq.upd s 1 (U8.uint_to_t (x % 0x100)) in
  s

val inverses16 (u:unit) : Lemma (DV.inverses get16 put16)

let up_view16 = inverses16 (); BV.View 2 get16 put16
let down_view16 = inverses16 (); DV.View 2 put16 get16

[@"opaque_to_smt"]
let get32 (s:Seq.lseq U8.t 4) =
  UInt32.uint_to_t (four_to_nat 8 (seq_to_four_LE  (seq_uint8_to_seq_nat8 s)))

[@"opaque_to_smt"]
let put32 (x:UInt32.t) : GTot (Seq.lseq U8.t 4) =
  seq_nat8_to_seq_uint8 (four_to_seq_LE (nat_to_four 8 (UInt32.v x)))

val inverses32 (u:unit) : Lemma (DV.inverses get32 put32)

let up_view32 = inverses32(); BV.View 4 get32 put32
let down_view32 = inverses32(); DV.View 4 put32 get32

[@"opaque_to_smt"]
let get64 (s:Seq.lseq U8.t 8) =
  UInt64.uint_to_t (le_bytes_to_nat64 (seq_uint8_to_seq_nat8 s))

[@"opaque_to_smt"]
let put64 (a:UInt64.t) : GTot (Seq.lseq U8.t 8) =
  seq_nat8_to_seq_uint8 (le_nat64_to_bytes (UInt64.v a))

val inverses64 (u:unit) : Lemma (DV.inverses get64 put64)

let up_view64 = inverses64 (); BV.View 8 get64 put64
let down_view64 = inverses64 (); DV.View 8 put64 get64

[@"opaque_to_smt"]
let get128 (s:Seq.lseq U8.t 16) =
  le_bytes_to_quad32 (seq_uint8_to_seq_nat8 s)

[@"opaque_to_smt"]
let put128 (a:quad32) : GTot (Seq.lseq U8.t 16) =
  seq_nat8_to_seq_uint8 (le_quad32_to_bytes a)

val inverses128 (u:unit) : Lemma (DV.inverses get128 put128)

let up_view128 = inverses128 (); BV.View 16 get128 put128
let down_view128 = inverses128 (); DV.View 16 put128 get128

let nat32s_to_nat128 (v1 v2 v3 v4: nat32): nat128 =
  v1 + v2 * 0x100000000 + v3 * 0x1000000000000 + v4 * 0x1000000000000000000000000

module U32 = FStar.UInt32

[@"opaque_to_smt"]
let get32_128 (s: Seq.lseq U32.t 4) : quad32 =
  seq_to_four_LE (seq_map UInt32.v s)

[@"opaque_to_smt"]
let put32_128 (a:quad32) : GTot (Seq.lseq U32.t 4) =
  seq_map UInt32.uint_to_t (four_to_seq_LE a)

val inverses32_128 (u: unit): Lemma (DV.inverses get32_128 put32_128)

let view32_128 = inverses32_128 (); BV.View 4 get32_128 put32_128
