module Spec.SPARKLE

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators


type branch = (uint32 & uint32)

val arx: c:uint32 -> branch -> Tot branch
let arx c b =
  let x, y = b in

  let x = x +. (y >>>. 31ul) in
  let y = y ^. (x >>>. 24ul) in
  let x = x ^. c in

  let x = x +. (y >>>. 17ul) in
  let y = y ^. (x >>>. 17ul) in
  let x = x ^. c in

  let x = x +. y in
  let y = y ^. (x >>>. 31ul) in
  let x = x ^. c in

  let x = x +. (y >>>. 24ul) in
  let y = y ^. (x >>>. 16ul) in
  let x = x ^. c in

  x,y


val l1: x:uint32 -> Tot uint32
let l1 x = (x <<<. size 16)  ^. (x &. (u32 0xffff))


val m2: branch -> branch -> Tot (branch & branch)
let m2 x y =
  let x0 = fst x in
  let y0 = snd x in
  let x1 = fst y in
  let y1 = snd y in
  let u = y0 ^. y1 in
  let v = x0 ^. x1 in
  let lu = l1 u in
  let lv = l1 v in
  let t0 = x0 ^. lu in
  let t1 = x1 ^. lu in
  let w0 = y0 ^. lv in
  let w1 = y1 ^. lv in
  (t0, w0), (t1, w1)


val l4: branch -> branch -> branch -> branch -> Tot (branch & branch & branch & branch)
let l4 b0 b1 b2 b3 =
  let (p0, p1) = m2 b0 b1 in
  let o0 = (fst b3 ^. fst p1), (snd b3 ^. snd p1) in
  let o1 = (fst b2 ^. fst p0), (snd b2 ^. snd p0) in
  (o0, o1, b0, b1)


let size_word: size_nat = 4


inline_for_extraction
let vsize_rcon: size_nat = 8

inline_for_extraction
let rcon_list: l:List.Tot.llist uint32 vsize_rcon =
  [@inline_let]
  let l = List.Tot.map u32 [0; 0; 0; 0; 0; 0; 0; 0] in
  assert_norm(List.Tot.length l == vsize_rcon);
  l

let rcon: lseq uint32 vsize_rcon  = createL rcon_list

val add: i:size_nat -> branch -> branch -> branch -> branch -> Tot (branch & branch & branch & branch)
let add i b0 b1 b2 b3 =
  let y0 = snd b0 in
  let y1 = snd b1 in
  let y0 = y0 ^. rcon.[(i % vsize_rcon)] in
  let y1 = y1 ^. (u32 i) in
  (b0, b1, b2, b3)


val sparkle256: steps:size_nat -> lbytes 32 -> Tot (lbytes 32)
let sparkle256 steps input =
  let bx0 = sub input 0 size_word in
  let by0 = sub input (1 * size_word) size_word in
  let bx1 = sub input (2 * size_word) size_word in
  let by1 = sub input (3 * size_word) size_word in
  let bx2 = sub input (4 * size_word) size_word in
  let by2 = sub input (5 * size_word) size_word in
  let bx3 = sub input (6 * size_word) size_word in
  let by3 = sub input (7 * size_word) size_word in
  let x0 = uint_from_bytes_le bx0 in
  let y0 = uint_from_bytes_le by0 in
  let x1 = uint_from_bytes_le bx1 in
  let y1 = uint_from_bytes_le by1 in
  let x2 = uint_from_bytes_le bx2 in
  let y2 = uint_from_bytes_le by2 in
  let x3 = uint_from_bytes_le bx3 in
  let y3 = uint_from_bytes_le by3 in

  let b0 = x0, y0 in
  let b1 = x1, y1 in
  let b2 = x2, y2 in
  let b3 = x3, y3 in

  let (b0, b1, b2, b3) =
    repeati steps (fun i (b0,b1,b2,b3) ->
    let (b0,b1,b2,b3) = add i b0 b1 b2 b3 in
    let b0 = arx rcon.[0] b0 in
    let b1 = arx rcon.[1] b1 in
    let b2 = arx rcon.[2] b2 in
    let b3 = arx rcon.[3] b3 in
    let b0, b1, b2, b3 = l4 b0 b1 b2 b3 in
    (b0, b1, b2, b3)
  ) (b0,b1,b2,b3)
  in

  let x0, y0 = b0 in
  let x1, y1 = b1 in
  let x2, y2 = b2 in
  let x3, y3 = b3 in

  let bx0 = uint_to_bytes_be x0 in
  let by0 = uint_to_bytes_be y0 in
  let bx1 = uint_to_bytes_be x1 in
  let by1 = uint_to_bytes_be y1 in
  let bx2 = uint_to_bytes_be x2 in
  let by2 = uint_to_bytes_be y2 in
  let bx3 = uint_to_bytes_be x3 in
  let by3 = uint_to_bytes_be y3 in
  let input = update_sub input 0 size_word bx0 in
  let input = update_sub input (1 * size_word) size_word by0 in
  let input = update_sub input (2 * size_word) size_word bx1 in
  let input = update_sub input (3 * size_word) size_word by1 in
  let input = update_sub input (4 * size_word) size_word bx2 in
  let input = update_sub input (5 * size_word) size_word by2 in
  let input = update_sub input (6 * size_word) size_word bx3 in
  let input = update_sub input (7 * size_word) size_word by3 in
  input
