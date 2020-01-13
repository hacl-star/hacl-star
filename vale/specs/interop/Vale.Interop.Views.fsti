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

let get8_def (s:Seq.lseq U8.t 1) = Seq.index s 0
[@"opaque_to_smt"] let get8 = opaque_make get8_def
irreducible let get8_reveal = opaque_revealer (`%get8) get8 get8_def

let put8_def (x:U8.t) : GTot (Seq.lseq U8.t 1) =
  let contents (i:nat{i<1}) = x in
  Seq.init 1 contents
[@"opaque_to_smt"] let put8 = opaque_make put8_def
irreducible let put8_reveal = opaque_revealer (`%put8) put8 put8_def

val inverses8 (u:unit) : Lemma (DV.inverses get8 put8)

let up_view8 = inverses8 (); BV.View 1 get8 put8
let down_view8 = inverses8 (); DV.View 1 put8 get8

let get16_def (s:Seq.lseq U8.t 2) = UInt16.uint_to_t (
  U8.v (Seq.index s 0) +
  U8.v (Seq.index s 1) * 0x100
  )
[@"opaque_to_smt"] let get16 = opaque_make get16_def
irreducible let get16_reveal = opaque_revealer (`%get16) get16 get16_def

let put16_def (x:UInt16.t) : GTot (Seq.lseq U8.t 2) =
  let s = Seq.create 2 (U8.uint_to_t 0) in
  let x = UInt16.v x in
  let s = Seq.upd s 0 (U8.uint_to_t (x % 0x100)) in
  let x = x `op_Division` 0x100 in
  let s = Seq.upd s 1 (U8.uint_to_t (x % 0x100)) in
  s
[@"opaque_to_smt"] let put16 = opaque_make put16_def
irreducible let put16_reveal = opaque_revealer (`%put16) put16 put16_def

val inverses16 (u:unit) : Lemma (DV.inverses get16 put16)

let up_view16 = inverses16 (); BV.View 2 get16 put16
let down_view16 = inverses16 (); DV.View 2 put16 get16

let get32_def (s:Seq.lseq U8.t 4) =
  UInt32.uint_to_t (four_to_nat 8 (seq_to_four_LE  (seq_uint8_to_seq_nat8 s)))
[@"opaque_to_smt"] let get32 = opaque_make get32_def
irreducible let get32_reveal = opaque_revealer (`%get32) get32 get32_def

let put32_def (x:UInt32.t) : GTot (Seq.lseq U8.t 4) =
  seq_nat8_to_seq_uint8 (four_to_seq_LE (nat_to_four 8 (UInt32.v x)))
[@"opaque_to_smt"] let put32 = opaque_make put32_def
irreducible let put32_reveal = opaque_revealer (`%put32) put32 put32_def

val inverses32 (u:unit) : Lemma (DV.inverses get32 put32)

let up_view32 = inverses32(); BV.View 4 get32 put32
let down_view32 = inverses32(); DV.View 4 put32 get32

let get64_def (s:Seq.lseq U8.t 8) =
  UInt64.uint_to_t (le_bytes_to_nat64 (seq_uint8_to_seq_nat8 s))
[@"opaque_to_smt"] let get64 = opaque_make get64_def
irreducible let get64_reveal = opaque_revealer (`%get64) get64 get64_def

let put64_def (a:UInt64.t) : GTot (Seq.lseq U8.t 8) =
  seq_nat8_to_seq_uint8 (le_nat64_to_bytes (UInt64.v a))
[@"opaque_to_smt"] let put64 = opaque_make put64_def
irreducible let put64_reveal = opaque_revealer (`%put64) put64 put64_def

val inverses64 (u:unit) : Lemma (DV.inverses get64 put64)

let up_view64 = inverses64 (); BV.View 8 get64 put64
let down_view64 = inverses64 (); DV.View 8 put64 get64

let get128_def (s:Seq.lseq U8.t 16) =
  le_bytes_to_quad32 (seq_uint8_to_seq_nat8 s)
[@"opaque_to_smt"] let get128 = opaque_make get128_def
irreducible let get128_reveal = opaque_revealer (`%get128) get128 get128_def

let put128_def (a:quad32) : GTot (Seq.lseq U8.t 16) =
  seq_nat8_to_seq_uint8 (le_quad32_to_bytes a)
[@"opaque_to_smt"] let put128 = opaque_make put128_def
irreducible let put128_reveal = opaque_revealer (`%put128) put128 put128_def

val inverses128 (u:unit) : Lemma (DV.inverses get128 put128)

let up_view128 = inverses128 (); BV.View 16 get128 put128
let down_view128 = inverses128 (); DV.View 16 put128 get128

let nat32s_to_nat128 (v1 v2 v3 v4: nat32): nat128 =
  v1 + v2 * 0x100000000 + v3 * 0x1000000000000 + v4 * 0x1000000000000000000000000

module U32 = FStar.UInt32

let get32_128_def (s: Seq.lseq U32.t 4) : quad32 =
  seq_to_four_LE (seq_map UInt32.v s)
[@"opaque_to_smt"] let get32_128 = opaque_make get32_128_def
irreducible let get32_128_reveal = opaque_revealer (`%get32_128) get32_128 get32_128_def

let put32_128_def (a:quad32) : GTot (Seq.lseq U32.t 4) =
  seq_map UInt32.uint_to_t (four_to_seq_LE a)
[@"opaque_to_smt"] let put32_128 = opaque_make put32_128_def
irreducible let put32_128_reveal = opaque_revealer (`%put32_128) put32_128 put32_128_def

val inverses32_128 (u: unit): Lemma (DV.inverses get32_128 put32_128)

let view32_128 = inverses32_128 (); BV.View 4 get32_128 put32_128
