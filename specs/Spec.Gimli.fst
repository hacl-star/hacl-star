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

let cst = u32 0x9e377800

let round_add (r:size_nat) (st:state) : state =
  let x = st.[0] in
  let st = st.[0] <- x ^. (cst ^. u32 r) in
  st

let inner_loop (st:state) : state =
  repeati 4 (fun i st -> column_looped i st) st

let rec gimli_round (r:size_nat{r<=24}) (st:state) : state =
  if r = 0 then
    st
  else begin
    let r = r - 1 in
    let st = inner_loop st in
    if uint_v ((u32 3) &. (u32 r)) = 0 then begin
      st end
      // let st = small_swap st in
      // let st = round_add r st in
      // gimli_round r st end
    else begin
      if uint_v ((u32 r) &. (u32 3)) = 2 then
      st end
//      let st = big_swap st in st end
//      gimli_round r st end`
   end

let gimli = gimli_round 24
