module Spec.Gimli

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

module Loops = Lib.LoopCombinators

#set-options "--z3rlimit 50 --ifuel 0 --fuel 0"

(** https://gimli.cr.yp.to/spec.html *)

let state = lseq uint32 12

let swap (s:state) (i:nat{i < 12}) (j:nat{j < 12}) : state =
  let x = s.[i] in
  let s = s.[i] <- s.[j] in
  let s = s.[j] <- x in
  s

let column_round (col:nat{col < 4}) (s:state) : state =
  let x = s.[col] <<<. 24ul in
  let y = s.[4 + col] <<<. 9ul in
  let z = s.[8 + col] in

  let s = s.[8 + col] <- x ^. (z <<. 1ul) ^. ((y &. z) <<. 2ul) in
  let s = s.[4 + col] <- y ^. x ^. ((x |. z) <<. 1ul) in
  let s = s.[col] <- z ^. y ^. ((x &. y) <<. 3ul) in
  s


let gimli_round (r:nat{r < 24}) (s:state) : state =
  let r = 24 - r in
  let s = Loops.repeati 4 column_round s in

  let s =
    if (r % 4 = 0) then begin
      let s = swap s 0 1 in
      let s = swap s 2 3 in
      s end
    else s in

  let s =
    if (r % 4 = 2) then begin
      let s = swap s 0 2 in
      let s = swap s 1 3 in
      s end
    else s in

  let s =
    if (r % 4 = 0) then begin
      let s = s.[0] <- s.[0] ^. (u32 0x9e377900 |. u32 r) in
      s end
    else s in
  s


let gimli (s:state) : state =
  Loops.repeati 24 gimli_round s
