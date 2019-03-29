module Spec.Gimli

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators
open Lib.NatMod


let size_state : size_nat = 12
let rate : size_nat = 16

let column = i:size_nat{i < size_state}
let state = lseq uint32 size_state

let column_looped (c:column{c < 4}) (st:state) =
  let x = st.[c] <<<. 24ul in
  let y = st.[c + 4] <<<. 9ul in
  let z = st.[c + 8] in
  let st : state = upd st (c + 8) ((x ^. (z <<. 1ul)) ^. ((y &. z) <<. 2ul)) in
  let st : state = upd st (c + 4) (y ^. x ^. ((x |. z) <<. 1ul)) in
  let st : state = upd st (c) (z ^. y ^. ((x &. y) <<. 3ul)) in
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
  st.[0] <- x ^. (c0 ^. u32 r)

let inner_loop (st:state) : state =
  repeati 4 (fun i st -> column_looped i st) st

assume val nat_and: size_nat -> size_nat -> Tot size_nat

let round (r:size_nat{r <= 24}) (st:state) : state =
  let st = inner_loop st in
  let st = if (nat_and r 3) = 0 then small_swap st else st in
  let st = if (nat_and r 3) = 2 then big_swap st else st in
  let st = if (nat_and r 3) = 0 then round_add r st else st in
  st

let gimli (st:state) : state =
  repeati 24 (fun i st -> round (24 - i) st) st

///
/// Hash Function
///

let vsize_block = 16

let update_block (block: lbytes vsize_block) (st:state): Tot state =
  let st8 = uints_to_bytes_be st in
  let x = map2 (fun a b -> a ^. b) block (sub st8 0 vsize_block) in
  let st8 = update_sub st8 0 vsize_block x in
  let st32 = uints_from_bytes_be #U32 #SEC st8 in
  gimli st

let update_last (last:bytes{length last < vsize_block}) (st:state): Tot state =
  let len = length last in
  let block = create 48 (u8 0) in
  let block = update_sub block 0 len last in
  let block = block.[len] <- (u8 1) in
  let block = block.[47] <- (u8 1) in
  let st8 = uints_to_bytes_be st in
  let st8 = map2 (fun a b -> a ^. b) block st8 in
  let st32 = uints_from_bytes_be #U32 #SEC #size_state st8 in
  gimli st

let hash (input: bytes) : Tot (lbytes 32) =
  let n = (length input) / vsize_block in
  let rem = length input % vsize_block in
  let output = create 32 (u8 0) in
  let st0 = create size_state (u32 0) in
  let st = repeati_blocks vsize_block input
    (fun i block st -> update_block block st)
    (fun i rem block st -> update_last block st) st0
  in
  let w3 = sub st 0 3 in
  let w3 = uints_to_bytes_be #U32 #SEC w3 in
  let output = update_sub output 0 (3 * numbytes U32) w3 in
  let st = gimli st in

  let w3 = sub st 0 3 in
  let w3 = uints_to_bytes_be #U32 #SEC w3 in
  let output = update_sub output (3 * numbytes U32) (3 * numbytes U32) w3 in
  output
