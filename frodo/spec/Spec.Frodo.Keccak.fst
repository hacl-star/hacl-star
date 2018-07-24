module Spec.Frodo.Keccak

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open FStar.Mul
open Spec.Keccak

module Seq = Lib.Sequence

val cshake128_frodo:
    input_len:size_nat
  -> input:lbytes input_len
  -> cstm:uint16
  -> output_len:size_nat
  -> lbytes output_len
let cshake128_frodo input_len input cstm output_len =
  let s = Seq.create 25 (u64 0) in
  let s = s.[0] <- (u64 0x10010001a801) |. (shift_left (to_u64 cstm) (u32 48)) in
  let s = state_permute s in
  let s = absorb s 168 input_len input (u8 0x04) in
  squeeze s 168 output_len

val cshake256_frodo:
    input_len: size_nat
  -> input: lbytes input_len
  -> cstm: uint16
  -> output_len: size_nat
  -> lbytes output_len
let cshake256_frodo input_len input cstm output_len =
  let s = Seq.create 25 (u64 0) in
  let s = s.[0] <- (u64 0x100100018801) |. (shift_left (to_u64 cstm) (u32 48)) in
  let s = state_permute s in
  let s = absorb s 136 input_len input (u8 0x04) in
  squeeze s 136 output_len
