module Spec.ESCH

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators

#set-options "--z3rlimit 15 --max_fuel 0"


type algorithm =
  | ESCH_256
  | ESCH_384

inline_for_extraction
let vsize_block = 16


inline_for_extraction
let vsize_state (a:algorithm) =
  match a with
  | ESCH_256 -> 48
  | ESCH_384 -> 64

inline_for_extraction
let vsize_hash (a:algorithm) =
  match a with
  | ESCH_256 -> 32
  | ESCH_384 -> 48

inline_for_extraction
let pos_constM (a:algorithm) =
  match a with
  | ESCH_256 -> 23
  | ESCH_384 -> 31

inline_for_extraction
let rounds_absorb (a:algorithm) =
  match a with
  | ESCH_256 -> 7
  | ESCH_384 -> 8

inline_for_extraction
let rounds_absorb_last (a:algorithm) =
  match a with
  | ESCH_256 -> 11
  | ESCH_384 -> 12


type state_s (a:algorithm) = lbytes (vsize_state a)


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


val permute: a:algorithm -> Tot (steps: size_nat -> state:lbytes (vsize_state a) -> Tot (state:lbytes (vsize_state a)))
let permute a =
  match a with
  | ESCH_256 -> Spec.SPARKLE.sparkle384
  | ESCH_384 -> Spec.SPARKLE.sparkle512


val absorb: a:algorithm -> block: lbytes 16 -> state: state_s a -> Tot (state_s a)
let absorb a block state =
  let rate = sub state 0 vsize_block in
  let merge: lbytes 16 = map2 (fun a b -> a ^. b) block rate in
  let state = update_sub state 0 vsize_block merge in
  permute a (rounds_absorb a) state


val absorb_last: a:algorithm -> input: bytes{length input <= vsize_block} -> state: state_s a -> Tot (state_s a)
let absorb_last a input state =
  let c, block = pad input in
  let cm = c ^. state.[(pos_constM a)] in
  let state = state.[(pos_constM a)] <- cm in
  permute a (rounds_absorb_last a) state


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


val squeeze: a:algorithm -> state_s a -> Tot (lbytes (vsize_hash a))
let squeeze a state =
  match a with
  | ESCH_256 -> squeeze256 state
  | ESCH_384 -> squeeze384 state


val esch: a:algorithm -> input:bytes -> Tot (lbytes (vsize_hash a))
let esch a input =
  let state = create (vsize_state a) (u8 0) in
  let state =
    repeat_blocks vsize_block input
      (absorb a)
      (fun _ -> absorb_last a)
    state in
  squeeze a state
