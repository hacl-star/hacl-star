module Spec.ESCH

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators


inline_for_extraction
let vsize_block = 16

inline_for_extraction
let pos_constM256: size_nat = 23

inline_for_extraction
let pos_constM384: size_nat = 31


val pad: b:bytes{length b <= vsize_block} -> Tot (uint8 & lbytes vsize_block)
let pad b =
  let blen: size_nat = length b in
  let output = create vsize_block (u8 0) in
  if blen = vsize_block then ((u8 2), b)
  else begin
    let b80 = create 1 (u8 0x80) in
    let output: lbytes vsize_block = update_sub output 0 blen b in
    let output: lbytes vsize_block = update_sub output blen 1 b80 in
    ((u8 1), output) end


val absorb256: block: lbytes 16 -> state: lbytes 48 -> Tot (lbytes 48)
let absorb256 block state =
  let rate = sub state 0 vsize_block in
  let merge: lbytes 16 = map2 (fun a b -> a ^. b) block rate in
  let state = update_sub state 0 vsize_block merge in
  Spec.SPARKLE.sparkle384 7 state


val absorb_last256: input: bytes{length input <= vsize_block} -> state: lbytes 48 -> Tot (lbytes 48)
let absorb_last256 input state =
  let c, block = pad input in
  let cm = c ^. state.[pos_constM256] in
  let state = state.[pos_constM256] <- cm in
  Spec.SPARKLE.sparkle384 11 state


val absorb384: block: lbytes 16 -> state: lbytes 64 -> Tot (lbytes 64)
let absorb384 block state =
  let rate = sub state 0 vsize_block in
  let merge: lbytes 16 = map2 (fun a b -> a ^. b) block rate in
  let state = update_sub state 0 vsize_block merge in
  Spec.SPARKLE.sparkle512 8 state


val absorb_last384: input: bytes{length input <= vsize_block} -> state: lbytes 64 -> Tot (lbytes 64)
let absorb_last384 input state =
  let c, block = pad input in
  let cm = c ^. state.[pos_constM384] in
  let state = state.[pos_constM384] <- cm in
  Spec.SPARKLE.sparkle512 12 state


val squeeze256: state: lbytes 48 -> Tot (lbytes 32)
let squeeze256 state =
  let a = sub state 0 vsize_block in
  let state = Spec.SPARKLE.sparkle384 7 state in
  let b = sub state 0 vsize_block in
  a @| b


val squeeze384: state: lbytes 64 -> Tot (lbytes 48)
let squeeze384 state =
  let a = sub state 0 vsize_block in
  let state = Spec.SPARKLE.sparkle512 8 state in
  let b = sub state 0 vsize_block in
  let state = Spec.SPARKLE.sparkle512 8 state in
  let c = sub state 0 vsize_block in
  a @| b @| c


val esch256: input:bytes -> Tot (lbytes 32)
let esch256 input =
  let state = create 48 (u8 0) in
  let len = length input in
  let state: lbytes 48 =
    repeati_blocks vsize_block input
      (fun _ b s -> absorb256 b s)
      (fun _ _ l s -> absorb_last256 l s)
    state in
  squeeze256 state


val esch384: input:bytes -> Tot (lbytes 48)
let esch384 input =
  let state = create 64 (u8 0) in
  let len = length input in
  let state: lbytes 64 =
    repeati_blocks vsize_block input
      (fun _ b s -> absorb384 b s)
      (fun _ _ l s -> absorb_last384 l s)
    state in
  squeeze384 state
