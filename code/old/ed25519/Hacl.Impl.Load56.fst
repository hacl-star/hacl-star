module Hacl.Impl.Load56

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul
open FStar.Buffer
open FStar.Old.Endianness
open Hacl.Endianness
open Hacl.UInt64


open Hacl.Spec.Endianness

#reset-options "--max_fuel 0 --z3rlimit 20"


inline_for_extraction
private
val hload56_le:
  b:hint8_p{length b = 64} ->
  off:u32{UInt32.v off <= 56} ->
  Stack h64
    (requires (fun h -> live h b))
    (ensures (fun h0 z h1 -> h0 == h1 /\ live h0 b /\
      v z == hlittle_endian (Seq.slice (as_seq h0 b) (UInt32.v off) (UInt32.v off + 7)) /\
      v z < pow2 56))

let hload56_le b off =
  let b8 = Buffer.sub b off 8ul in
  let z  = hload64_le b8 in
  let z' = z &^ (Hacl.Cast.uint64_to_sint64 0xffffffffffffffuL) in
  assert_norm(pow2 56 = 0x100000000000000);
  UInt.logand_mask (v z) 56;
  assert(v z' = v z % pow2 56);
  let h  = ST.get() in
  Seq.lemma_eq_intro (as_seq h b8) (Seq.append (Seq.slice (as_seq h b8) 0 7) (Seq.slice (as_seq h b8) 7 8));
  FStar.Old.Endianness.little_endian_append (reveal_sbytes (Seq.slice (as_seq h b8) 0 7)) (reveal_sbytes (Seq.slice (as_seq h b8) 7 8));
  FStar.Old.Endianness.lemma_little_endian_is_bounded (reveal_sbytes (Seq.slice (as_seq h b8) 0 7));
  Seq.lemma_eq_intro (as_seq h (Buffer.sub b off 7ul)) (Seq.slice (as_seq h b8) 0 7);
  z'

#reset-options "--max_fuel 0 --z3rlimit 200"

private
val lemma_append_10:
  b0:Seq.seq Hacl.UInt8.t{Seq.length b0 = 7} ->
  b1:Seq.seq Hacl.UInt8.t{Seq.length b1 = 7} ->
  b2:Seq.seq Hacl.UInt8.t{Seq.length b2 = 7} ->
  b3:Seq.seq Hacl.UInt8.t{Seq.length b3 = 7} ->
  b4:Seq.seq Hacl.UInt8.t{Seq.length b4 = 7} ->
  b5:Seq.seq Hacl.UInt8.t{Seq.length b5 = 7} ->
  b6:Seq.seq Hacl.UInt8.t{Seq.length b6 = 7} ->
  b7:Seq.seq Hacl.UInt8.t{Seq.length b7 = 7} ->
  b8:Seq.seq Hacl.UInt8.t{Seq.length b8 = 7} ->
  b9:Seq.seq Hacl.UInt8.t{Seq.length b9 = 1} ->
  Lemma (hlittle_endian FStar.Seq.(b0 @| b1 @| b2 @| b3 @| b4 @| b5 @| b6 @| b7 @| b8 @| b9)
  == hlittle_endian b0 + pow2 56 * hlittle_endian b1
    + pow2 112 * hlittle_endian b2 + pow2 168 * hlittle_endian b3
    + pow2 224 * hlittle_endian b4 + pow2 280 * hlittle_endian b5
    + pow2 336 * hlittle_endian b6 + pow2 392 * hlittle_endian b7
    + pow2 448 * hlittle_endian b8 + pow2 504 * hlittle_endian b9)
let lemma_append_10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 =
  let open FStar.Seq in
  let b = b0 @| b1 @| b2 @| b3 @| b4 @| b5 @| b6 @| b7 @| b8 @| b9 in
  Seq.lemma_eq_intro ((b0 @| b1 @| b2 @| b3 @| b4 @| b5 @| b6 @| b7 @| b8) @| b9) b;
  FStar.Old.Endianness.little_endian_append (reveal_sbytes (b0 @| b1 @| b2 @| b3 @| b4 @| b5 @| b6 @| b7 @| b8)) (reveal_sbytes b9);
  Seq.lemma_eq_intro ((b0 @| b1 @| b2 @| b3 @| b4 @| b5 @| b6 @| b7) @| b8) (b0 @| b1 @| b2 @| b3 @| b4 @| b5 @| b6 @| b7 @| b8);
  FStar.Old.Endianness.little_endian_append (reveal_sbytes (b0 @| b1 @| b2 @| b3 @| b4 @| b5 @| b6 @| b7)) (reveal_sbytes b8);
  Seq.lemma_eq_intro ((b0 @| b1 @| b2 @| b3 @| b4 @| b5 @| b6) @| b7) (b0 @| b1 @| b2 @| b3 @| b4 @| b5 @| b6 @| b7);
  FStar.Old.Endianness.little_endian_append (reveal_sbytes (b0 @| b1 @| b2 @| b3 @| b4 @| b5 @| b6)) (reveal_sbytes b7);
  Seq.lemma_eq_intro ((b0 @| b1 @| b2 @| b3 @| b4 @| b5) @| b6) (b0 @| b1 @| b2 @| b3 @| b4 @| b5 @| b6);
  FStar.Old.Endianness.little_endian_append (reveal_sbytes (b0 @| b1 @| b2 @| b3 @| b4 @| b5)) (reveal_sbytes b6);
  Seq.lemma_eq_intro ((b0 @| b1 @| b2 @| b3 @| b4) @| b5) (b0 @| b1 @| b2 @| b3 @| b4 @| b5);
  FStar.Old.Endianness.little_endian_append (reveal_sbytes (b0 @| b1 @| b2 @| b3 @| b4)) (reveal_sbytes b5);
  Seq.lemma_eq_intro ((b0 @| b1 @| b2 @| b3) @| b4) (b0 @| b1 @| b2 @| b3 @| b4);
  FStar.Old.Endianness.little_endian_append (reveal_sbytes (b0 @| b1 @| b2 @| b3)) (reveal_sbytes b4);
  Seq.lemma_eq_intro ((b0 @| b1 @| b2) @| b3) (b0 @| b1 @| b2 @| b3);
  FStar.Old.Endianness.little_endian_append (reveal_sbytes (b0 @| b1 @| b2)) (reveal_sbytes b3);
  Seq.lemma_eq_intro ((b0 @| b1) @| b2) (b0 @| b1 @| b2);
  FStar.Old.Endianness.little_endian_append (reveal_sbytes (b0 @| b1)) (reveal_sbytes b2);
  FStar.Old.Endianness.little_endian_append (reveal_sbytes b0) (reveal_sbytes b1)


private
val lemma_append_5:
  b0:Seq.seq Hacl.UInt8.t{Seq.length b0 = 7} ->
  b1:Seq.seq Hacl.UInt8.t{Seq.length b1 = 7} ->
  b2:Seq.seq Hacl.UInt8.t{Seq.length b2 = 7} ->
  b3:Seq.seq Hacl.UInt8.t{Seq.length b3 = 7} ->
  b4:Seq.seq Hacl.UInt8.t{Seq.length b4 = 4} ->
  Lemma (hlittle_endian FStar.Seq.(b0 @| b1 @| b2 @| b3 @| b4) ==
    hlittle_endian b0 + pow2 56 * hlittle_endian b1 + pow2 112 * hlittle_endian b2 + pow2 168 * hlittle_endian b3 + pow2 224 * hlittle_endian b4)
let lemma_append_5 b0 b1 b2 b3 b4 =
  let open FStar.Seq in
  let b = b0 @| b1 @| b2 @| b3 @| b4 in
  Seq.lemma_eq_intro ((b0 @| b1 @| b2 @| b3) @| b4) b;
  FStar.Old.Endianness.little_endian_append (reveal_sbytes (b0 @| b1 @| b2 @| b3)) (reveal_sbytes b4);
  Seq.lemma_eq_intro ((b0 @| b1 @| b2) @| b3) (b0 @| b1 @| b2 @| b3);
  FStar.Old.Endianness.little_endian_append (reveal_sbytes (b0 @| b1 @| b2)) (reveal_sbytes b3);
  Seq.lemma_eq_intro ((b0 @| b1) @| b2) (b0 @| b1 @| b2);
  FStar.Old.Endianness.little_endian_append (reveal_sbytes (b0 @| b1)) (reveal_sbytes b2);
  FStar.Old.Endianness.little_endian_append (reveal_sbytes b0) (reveal_sbytes b1)


let load_64_bytes out b =
  let h0 = ST.get() in
  let b0 = hload56_le b 0ul in
  let b1 = hload56_le b 7ul in
  let b2 = hload56_le b 14ul in
  let b3 = hload56_le b 21ul in
  let b4 = hload56_le b 28ul in
  let b5 = hload56_le b 35ul in
  let b6 = hload56_le b 42ul in
  let b7 = hload56_le b 49ul in
  let b8 = hload56_le b 56ul in
  let b63 = b.(63ul) in
  let b9 = Hacl.Cast.sint8_to_sint64 b63 in
  Seq.lemma_eq_intro (Seq.create 1 b63) (Seq.slice (as_seq h0 b) 63 64);
  assert(v b0 = hlittle_endian (Seq.slice (as_seq h0 b) 0 7));
  assert(v b1 = hlittle_endian (Seq.slice (as_seq h0 b) 7 14));
  assert(v b2 = hlittle_endian (Seq.slice (as_seq h0 b) 14 21));
  assert(v b3 = hlittle_endian (Seq.slice (as_seq h0 b) 21 28));
  assert(v b4 = hlittle_endian (Seq.slice (as_seq h0 b) 28 35));
  assert(v b5 = hlittle_endian (Seq.slice (as_seq h0 b) 35 42));
  assert(v b6 = hlittle_endian (Seq.slice (as_seq h0 b) 42 49));
  assert(v b7 = hlittle_endian (Seq.slice (as_seq h0 b) 49 56));
  assert(v b8 = hlittle_endian (Seq.slice (as_seq h0 b) 56 63));
  FStar.Old.Endianness.little_endian_singleton (h8_to_u8 b63);
  assert(v b9 = hlittle_endian (Seq.slice (as_seq h0 b) 63 64));
  Seq.lemma_eq_intro (as_seq h0 b) FStar.Seq.(slice (as_seq h0 b) 0 7 @| slice (as_seq h0 b) 7 14 @| slice (as_seq h0 b) 14 21 @| slice (as_seq h0 b) 21 28 @| slice (as_seq h0 b) 28 35 @| slice (as_seq h0 b) 35 42 @| slice (as_seq h0 b) 42 49 @| slice (as_seq h0 b) 49 56 @| slice (as_seq h0 b) 56 63 @| slice (as_seq h0 b) 63 64);
  lemma_append_10 (Seq.slice (as_seq h0 b) 0 7) (Seq.slice (as_seq h0 b) 7 14) (Seq.slice (as_seq h0 b) 14 21) (Seq.slice (as_seq h0 b) 21 28) (Seq.slice (as_seq h0 b) 28 35) (Seq.slice (as_seq h0 b) 35 42) (Seq.slice (as_seq h0 b) 42 49) (Seq.slice (as_seq h0 b) 49 56) (Seq.slice (as_seq h0 b) 56 63) (Seq.slice (as_seq h0 b) 63 64);
  assert_norm(pow2 56 = Hacl.Spec.BignumQ.Eval.p1);
  assert_norm(pow2 112 = Hacl.Spec.BignumQ.Eval.p2);
  assert_norm(pow2 168 = Hacl.Spec.BignumQ.Eval.p3);
  assert_norm(pow2 224 = Hacl.Spec.BignumQ.Eval.p4);
  assert_norm(pow2 280 = Hacl.Spec.BignumQ.Eval.p5);
  assert_norm(pow2 336 = Hacl.Spec.BignumQ.Eval.p6);
  assert_norm(pow2 392 = Hacl.Spec.BignumQ.Eval.p7);
  assert_norm(pow2 448 = Hacl.Spec.BignumQ.Eval.p8);
  assert_norm(pow2 504 = Hacl.Spec.BignumQ.Eval.p9);
  FStar.Old.Endianness.lemma_little_endian_is_bounded (reveal_sbytes (as_seq h0 b));
  Hacl.Lib.Create64.make_h64_10 out b0 b1 b2 b3 b4 b5 b6 b7 b8 b9


inline_for_extraction
private
val hload56_le':
  b:hint8_p{length b = 32} ->
  off:u32{UInt32.v off <= 21} ->
  Stack h64
    (requires (fun h -> live h b))
    (ensures (fun h0 z h1 -> h0 == h1 /\ live h0 b /\
      v z == hlittle_endian (Seq.slice (as_seq h0 b) (UInt32.v off) (UInt32.v off + 7)) /\
      v z < pow2 56))

let hload56_le' b off =
  let b8 = Buffer.sub b off 8ul in
  let z  = hload64_le b8 in
  let z' = z &^ (Hacl.Cast.uint64_to_sint64 0xffffffffffffffuL) in
  assert_norm(pow2 56 = 0x100000000000000);
  UInt.logand_mask (v z) 56;
  assert(v z' = v z % pow2 56);
  let h  = ST.get() in
  Seq.lemma_eq_intro (as_seq h b8) (Seq.append (Seq.slice (as_seq h b8) 0 7) (Seq.slice (as_seq h b8) 7 8));
  FStar.Old.Endianness.little_endian_append (reveal_sbytes (Seq.slice (as_seq h b8) 0 7)) (reveal_sbytes (Seq.slice (as_seq h b8) 7 8));
  FStar.Old.Endianness.lemma_little_endian_is_bounded (reveal_sbytes (Seq.slice (as_seq h b8) 0 7));
  Seq.lemma_eq_intro (as_seq h (Buffer.sub b off 7ul)) (Seq.slice (as_seq h b8) 0 7);
  z'


let load_32_bytes out b =
  let h0 = ST.get() in
  let b0 = hload56_le' b 0ul in
  let b1 = hload56_le' b 7ul in
  let b2 = hload56_le' b 14ul in
  let b3 = hload56_le' b 21ul in
  let b4 = hload32_le (Buffer.sub b 28ul 4ul) in
  Seq.lemma_eq_intro (as_seq h0 (Buffer.sub b 28ul 4ul)) (Seq.slice (as_seq h0 b) 28 32);
  let b4 = Hacl.Cast.sint32_to_sint64 b4 in
  assert_norm(pow2 56 = Hacl.Spec.BignumQ.Eval.p1);
  assert_norm(pow2 112 = Hacl.Spec.BignumQ.Eval.p2);
  assert_norm(pow2 168 = Hacl.Spec.BignumQ.Eval.p3);
  assert_norm(pow2 224 = Hacl.Spec.BignumQ.Eval.p4);
  lemma_append_5 (Seq.slice (as_seq h0 b) 0 7) (Seq.slice (as_seq h0 b) 7 14) (Seq.slice (as_seq h0 b) 14 21) (Seq.slice (as_seq h0 b) 21 28) (Seq.slice (as_seq h0 b) 28 32);
  Seq.lemma_eq_intro (as_seq h0 b) FStar.Seq.(slice (as_seq h0 b) 0 7 @| slice (as_seq h0 b) 7 14 @| (slice (as_seq h0 b) 14 21) @| (slice (as_seq h0 b) 21 28) @| (slice (as_seq h0 b) 28 32));
  Hacl.Lib.Create64.make_h64_5 out b0 b1 b2 b3 b4
