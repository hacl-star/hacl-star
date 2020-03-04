module Spec.Ascon.Hash

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.ByteSequence.Tuples
open Lib.LoopCombinators

open Spec.Ascon


inline_for_extraction
let vsize_hash: size_nat = 32

inline_for_extraction
let rate: size_nat = 64 / 8

inline_for_extraction
let pa_rounds: size_nat = 12

inline_for_extraction
let max_input: nat = pow2 64 - 1

inline_for_extraction
let iv: uint64 = ((u64 (8 * rate)) <<. size 48) |. ((u64 pa_rounds) <<. size 40)


val absorb_block: lbytes rate -> state_s -> state_s
let absorb_block block s =
  let s = s.[0] <- uint_from_bytes_be block in
  p12 s


val absorb: bytes -> state_s -> state_s
let absorb input s =
  let len = length input in
  let n = len / rate in
  let rem = len % rate in
  let blocks = Seq.slice input 0 (n * rate) in
  let last = Seq.slice input (n * rate) len in
  let s = repeat_blocks_multi rate blocks absorb_block s in
  let s = s.[0] <- s.[0] ^. (u64 rem) in
  let sv64 = (u64 0x80) <<. ((size 56) -. (size 8) *. (size rem)) in
  let s = s.[0] <- s.[0] ^. sv64 in
  p12 s


val squeeze: state_s -> len:size_nat{rate <= len} -> lbytes len
let squeeze s0 len =
  let n = len / rate in
  let rem = len % rate in
  let f0 = create len (u8 0) in
  let f,o = repeati n (fun i (f,s) ->
    let f: lbytes len = update_slice f (i * rate) ((i+1) * rate) (uint_to_bytes_be s.[0]) in
    let s: state_s = p12 s in (f,s)
  ) (f0,s0) in
  sub f 0 len


val vhash: input:bytes -> olen:size_nat{rate <= olen} -> lbytes olen
let vhash input olen =
  let s = create_state () in
  let s = s.[0] <- iv in
  let s = p12 s in
  let s = absorb input s in
  let s = p12 s in
  squeeze s olen


val hash: input:bytes -> lbytes vsize_hash
let hash input =
  vhash input vsize_hash
