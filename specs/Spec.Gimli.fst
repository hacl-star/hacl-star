module Spec.Gimli

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Spec.Lib.RawIntTypes


let size_state : size_nat = 12

let column = i:size_nat{i < size_state}
let state = intseq U32 size_state

let column_looped (c:column{c < 4}) (st:state) =
  let x = st.[c] <<<. u32 24 in
  let y = st.[c + 4] <<<. u32 9 in
  let z = st.[c + 8] in
  let st : state = upd st (c + 8) ((x ^. (z <<. u32 1)) ^. ((y &. z) <<. u32 2)) in
  let st : state = upd st (c + 4) (y ^. x ^. ((x |. z) <<. u32 1)) in
  let st : state = upd st (c) (z ^. y ^. ((x &. y) <<. u32 3)) in
  st

let small_swap (st:state) : state =
  let x = st.[0] in
  let y = st.[1] in
  let st = st.[1] <- x in
  let st = st.[0] <- y in
  let x = st.[2] in
  let y = st.[3] in
  let st = st.[2] <- y in
  let st = st.[3] <- x in
  st

let big_swap (st:state) : state =
  let x = st.[0] in
  let y = st.[2] in
  let st = st.[2] <- x in
  let st = st.[0] <- y in
  let x = st.[1] in
  let y = st.[3] in
  let st = st.[1] <- y in
  let st = st.[3] <- x in
  st

let c0 = u32 0x9e377800

let round_add (r:size_nat) (st:state) : state =
  let x = st.[0] in
  let st = st.[0] <- x ^. (c0 ^. u32 r) in
  st

let inner_loop (st:state) : state =
  repeati 4 (fun i st -> column_looped i st) st

let round (r:size_nat{r <= 24}) (st:state) : state =
  let st = inner_loop st in
  let st = if (u32 r &. u32 3) = u32 0 then small_swap st else st in
  let st = if (u32 r &. u32 3) = u32 2 then big_swap st else st in
  let st = if (u32 r &. u32 3) = u32 0 then round_add r st else st in
  st

let gimli (st:state) : state =
  repeati 24 (fun i st -> round (24 - i) st) st
