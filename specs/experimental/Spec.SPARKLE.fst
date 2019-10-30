module Spec.SPARKLE

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators


#set-options "--z3rlimit 15 --max_fuel 0"


let size_word: size_nat = 4


inline_for_extraction
let vsize_rcon: size_nat = 8

inline_for_extraction
let rcon_list: l:List.Tot.llist uint32 vsize_rcon =
  [@inline_let]
  let l = List.Tot.map u32 [
    0xB7E15162; 0xBF715880; 0x38B4DA56; 0x324E7738;
    0xBB1185EB; 0x4F7C7B57; 0xCFBFA1C8; 0xC2B3293D] in
  assert_norm(List.Tot.length l == vsize_rcon);
  l

let rcon: lseq uint32 vsize_rcon  = createL rcon_list


type branch = (uint32 & uint32)
type branch2 = (branch & branch)
type branch3 = (branch & branch & branch)
type branch4 = (branch & branch & branch & branch)
type branch6 = (branch & branch & branch & branch & branch & branch)
type branch8 = (branch & branch & branch & branch & branch & branch & branch & branch)

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


val m2: branch2 -> Tot branch2
let m2 b =
  let x,y = b in
  let x0,y0 = x in
  let x1,y1 = y in
  let u = y0 ^. y1 in
  let v = x0 ^. x1 in
  let lu = l1 u in
  let lv = l1 v in
  let t0 = x0 ^. lu in
  let t1 = x1 ^. lu in
  let w0 = y0 ^. lv in
  let w1 = y1 ^. lv in
  (t0,w0), (t1,w1)


val m3: branch3 -> Tot branch3
let m3 b =
  let b0,b1,b2 = b in
  let x0,y0 = b0 in
  let x1,y1 = b1 in
  let x2,y2 = b2 in
  let u = y0 ^. y1 ^. y2 in
  let v = x0 ^. x1 ^. x2 in
  let lu = l1 u in
  let lv = l1 v in
  let t0 = x0 ^. lu in
  let t1 = x1 ^. lu in
  let t2 = x2 ^. lu in
  let w0 = y0 ^. lv in
  let w1 = y1 ^. lv in
  let w2 = y2 ^. lv in
  (t0,w0), (t1,w1), (t2,w2)


val m4: branch4 -> Tot branch4
let m4 b =
  let b0,b1,b2,b3 = b in
  let x0,y0 = b0 in
  let x1,y1 = b1 in
  let x2,y2 = b2 in
  let x3,y3 = b3 in
  let u = y0 ^. y1 ^. y2 ^. y3 in
  let v = x0 ^. x1 ^. x2 ^. x3 in
  let lu = l1 u in
  let lv = l1 v in
  let t0 = x0 ^. lu in
  let t1 = x1 ^. lu in
  let t2 = x2 ^. lu in
  let t3 = x3 ^. lu in
  let w0 = y0 ^. lv in
  let w1 = y1 ^. lv in
  let w2 = y2 ^. lv in
  let w3 = y3 ^. lv in
  (t0,w0), (t1,w1), (t2,w2), (t3,w3)


val l4: branch4 -> Tot branch4
let l4 b =
  let (b0,b1,b2,b3) = b in
  let (p0,p1) = m2 (b0,b1) in
  let o0 = (fst b3 ^. fst p1), (snd b3 ^. snd p1) in
  let o1 = (fst b2 ^. fst p0), (snd b2 ^. snd p0) in
  (o0,o1,b0,b1)


val l6: branch6 -> Tot branch6
let l6 b =
  let (b0,b1,b2,b3,b4,b5) = b in
  let (p0,p1,p2) = m3 (b0,b1,b2) in
  let o0 = (fst b4 ^. fst p1), (snd b4 ^. snd p1) in
  let o1 = (fst b5 ^. fst p2), (snd b5 ^. snd p2) in
  let o2 = (fst b3 ^. fst p0), (snd b3 ^. snd p0) in
  (o0,o1,o2,b0,b1,b2)


val l8: branch8 -> Tot branch8
let l8 b =
  let (b0,b1,b2,b3,b4,b5,b6,b7) = b in
  let (p0,p1,p2,p3) = m4 (b0,b1,b2,b3) in
  let o0 = (fst b5 ^. fst p1), (snd b5 ^. snd p1) in
  let o1 = (fst b6 ^. fst p2), (snd b6 ^. snd p2) in
  let o2 = (fst b7 ^. fst p3), (snd b7 ^. snd p3) in
  let o3 = (fst b4 ^. fst p0), (snd b4 ^. snd p0) in
  (o0,o1,o2,o3,b0,b1,b2,b3)


val add2: i:size_nat -> branch2 -> Tot branch2
let add2 i b =
  let ((x0,y0),(x1,y1)) = b in
  let y0 = y0 ^. rcon.[(i % vsize_rcon)] in
  let y1 = y1 ^. (u32 i) in
  (x0,y0),(x1,y1)


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

  let (b0,b1,b2,b3) =
    repeati steps (fun i (b0,b1,b2,b3) ->
      let (b0,b1) = add2 i (b0,b1) in
      let b0 = arx rcon.[0] b0 in
      let b1 = arx rcon.[1] b1 in
      let b2 = arx rcon.[2] b2 in
      let b3 = arx rcon.[3] b3 in
      l4 (b0,b1,b2,b3)
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


val sparkle384: steps:size_nat -> lbytes 48 -> Tot (lbytes 48)
let sparkle384 steps input =
  let bx0 = sub input 0 size_word in
  let by0 = sub input (1 * size_word) size_word in
  let bx1 = sub input (2 * size_word) size_word in
  let by1 = sub input (3 * size_word) size_word in
  let bx2 = sub input (4 * size_word) size_word in
  let by2 = sub input (5 * size_word) size_word in
  let bx3 = sub input (6 * size_word) size_word in
  let by3 = sub input (7 * size_word) size_word in
  let bx4 = sub input (8 * size_word) size_word in
  let by4 = sub input (9 * size_word) size_word in
  let bx5 = sub input (10 * size_word) size_word in
  let by5 = sub input (11 * size_word) size_word in
  let x0 = uint_from_bytes_le bx0 in
  let y0 = uint_from_bytes_le by0 in
  let x1 = uint_from_bytes_le bx1 in
  let y1 = uint_from_bytes_le by1 in
  let x2 = uint_from_bytes_le bx2 in
  let y2 = uint_from_bytes_le by2 in
  let x3 = uint_from_bytes_le bx3 in
  let y3 = uint_from_bytes_le by3 in
  let x4 = uint_from_bytes_le bx4 in
  let y4 = uint_from_bytes_le by4 in
  let x5 = uint_from_bytes_le bx5 in
  let y5 = uint_from_bytes_le by5 in

  let b0 = x0, y0 in
  let b1 = x1, y1 in
  let b2 = x2, y2 in
  let b3 = x3, y3 in
  let b4 = x4, y4 in
  let b5 = x5, y5 in

  let (b0,b1,b2,b3,b4,b5) =
    repeati steps (fun i (b0,b1,b2,b3,b4,b5) ->
      let (b0,b1) = add2 i (b0,b1) in
      let b0 = arx rcon.[0] b0 in
      let b1 = arx rcon.[1] b1 in
      let b2 = arx rcon.[2] b2 in
      let b3 = arx rcon.[3] b3 in
      let b4 = arx rcon.[4] b4 in
      let b5 = arx rcon.[5] b5 in
      l6 (b0,b1,b2,b3,b4,b5)
  ) (b0,b1,b2,b3,b4,b5)
  in

  let x0, y0 = b0 in
  let x1, y1 = b1 in
  let x2, y2 = b2 in
  let x3, y3 = b3 in
  let x4, y4 = b4 in
  let x5, y5 = b5 in

  let bx0 = uint_to_bytes_be x0 in
  let by0 = uint_to_bytes_be y0 in
  let bx1 = uint_to_bytes_be x1 in
  let by1 = uint_to_bytes_be y1 in
  let bx2 = uint_to_bytes_be x2 in
  let by2 = uint_to_bytes_be y2 in
  let bx3 = uint_to_bytes_be x3 in
  let by3 = uint_to_bytes_be y3 in
  let bx4 = uint_to_bytes_be x4 in
  let by4 = uint_to_bytes_be y4 in
  let bx5 = uint_to_bytes_be x5 in
  let by5 = uint_to_bytes_be y5 in
  let input = update_sub input 0 size_word bx0 in
  let input = update_sub input (1 * size_word) size_word by0 in
  let input = update_sub input (2 * size_word) size_word bx1 in
  let input = update_sub input (3 * size_word) size_word by1 in
  let input = update_sub input (4 * size_word) size_word bx2 in
  let input = update_sub input (5 * size_word) size_word by2 in
  let input = update_sub input (6 * size_word) size_word bx3 in
  let input = update_sub input (7 * size_word) size_word by3 in
  let input = update_sub input (8 * size_word) size_word bx4 in
  let input = update_sub input (9 * size_word) size_word by4 in
  let input = update_sub input (10 * size_word) size_word bx5 in
  let input = update_sub input (11 * size_word) size_word by5 in
  input


val sparkle512: steps:size_nat -> lbytes 64 -> Tot (lbytes 64)
let sparkle512 steps input =
  let bx0 = sub input 0 size_word in
  let by0 = sub input (1 * size_word) size_word in
  let bx1 = sub input (2 * size_word) size_word in
  let by1 = sub input (3 * size_word) size_word in
  let bx2 = sub input (4 * size_word) size_word in
  let by2 = sub input (5 * size_word) size_word in
  let bx3 = sub input (6 * size_word) size_word in
  let by3 = sub input (7 * size_word) size_word in
  let bx4 = sub input (8 * size_word) size_word in
  let by4 = sub input (9 * size_word) size_word in
  let bx5 = sub input (10 * size_word) size_word in
  let by5 = sub input (11 * size_word) size_word in
  let bx6 = sub input (12 * size_word) size_word in
  let by6 = sub input (13 * size_word) size_word in
  let bx7 = sub input (14 * size_word) size_word in
  let by7 = sub input (15 * size_word) size_word in
  let x0 = uint_from_bytes_le bx0 in
  let y0 = uint_from_bytes_le by0 in
  let x1 = uint_from_bytes_le bx1 in
  let y1 = uint_from_bytes_le by1 in
  let x2 = uint_from_bytes_le bx2 in
  let y2 = uint_from_bytes_le by2 in
  let x3 = uint_from_bytes_le bx3 in
  let y3 = uint_from_bytes_le by3 in
  let x4 = uint_from_bytes_le bx4 in
  let y4 = uint_from_bytes_le by4 in
  let x5 = uint_from_bytes_le bx5 in
  let y5 = uint_from_bytes_le by5 in
  let x6 = uint_from_bytes_le bx6 in
  let y6 = uint_from_bytes_le by6 in
  let x7 = uint_from_bytes_le bx7 in
  let y7 = uint_from_bytes_le by7 in

  let b0 = x0, y0 in
  let b1 = x1, y1 in
  let b2 = x2, y2 in
  let b3 = x3, y3 in
  let b4 = x4, y4 in
  let b5 = x5, y5 in
  let b6 = x6, y6 in
  let b7 = x7, y7 in

  let (b0,b1,b2,b3,b4,b5,b6,b7) =
    repeati steps (fun i (b0,b1,b2,b3,b4,b5,b6,b7) ->
      let (b0,b1) = add2 i (b0,b1) in
      let b0 = arx rcon.[0] b0 in
      let b1 = arx rcon.[1] b1 in
      let b2 = arx rcon.[2] b2 in
      let b3 = arx rcon.[3] b3 in
      let b4 = arx rcon.[4] b4 in
      let b5 = arx rcon.[5] b5 in
      let b6 = arx rcon.[6] b6 in
      let b7 = arx rcon.[7] b7 in
      l8 (b0,b1,b2,b3,b4,b5,b6,b7)
  ) (b0,b1,b2,b3,b4,b5,b6,b7)
  in

  let x0, y0 = b0 in
  let x1, y1 = b1 in
  let x2, y2 = b2 in
  let x3, y3 = b3 in
  let x4, y4 = b4 in
  let x5, y5 = b5 in
  let x6, y6 = b6 in
  let x7, y7 = b7 in

  let bx0 = uint_to_bytes_be x0 in
  let by0 = uint_to_bytes_be y0 in
  let bx1 = uint_to_bytes_be x1 in
  let by1 = uint_to_bytes_be y1 in
  let bx2 = uint_to_bytes_be x2 in
  let by2 = uint_to_bytes_be y2 in
  let bx3 = uint_to_bytes_be x3 in
  let by3 = uint_to_bytes_be y3 in
  let bx4 = uint_to_bytes_be x4 in
  let by4 = uint_to_bytes_be y4 in
  let bx5 = uint_to_bytes_be x5 in
  let by5 = uint_to_bytes_be y5 in
  let bx6 = uint_to_bytes_be x6 in
  let by6 = uint_to_bytes_be y6 in
  let bx7 = uint_to_bytes_be x7 in
  let by7 = uint_to_bytes_be y7 in
  let input = update_sub input 0 size_word bx0 in
  let input = update_sub input (1 * size_word) size_word by0 in
  let input = update_sub input (2 * size_word) size_word bx1 in
  let input = update_sub input (3 * size_word) size_word by1 in
  let input = update_sub input (4 * size_word) size_word bx2 in
  let input = update_sub input (5 * size_word) size_word by2 in
  let input = update_sub input (6 * size_word) size_word bx3 in
  let input = update_sub input (7 * size_word) size_word by3 in
  let input = update_sub input (8 * size_word) size_word bx4 in
  let input = update_sub input (9 * size_word) size_word by4 in
  let input = update_sub input (10 * size_word) size_word bx5 in
  let input = update_sub input (11 * size_word) size_word by5 in
  let input = update_sub input (12 * size_word) size_word bx6 in
  let input = update_sub input (13 * size_word) size_word by6 in
  let input = update_sub input (14 * size_word) size_word bx7 in
  let input = update_sub input (15 * size_word) size_word by7 in
  input
