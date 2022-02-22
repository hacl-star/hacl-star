module Spec.SPARKLE

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators
open Lib.ByteSequence.Tuples

#set-options "--z3rlimit 15"


inline_for_extraction
let vsize_rcon: size_nat = 8

inline_for_extraction
let rcon_list: x:list uint32 {List.Tot.length x == vsize_rcon} =
  [@inline_let]
  let l =  [
    u32 0xB7E15162; u32 0xBF715880; u32 0x38B4DA56; u32 0x324E7738;
    u32 0xBB1185EB; u32 0x4F7C7B57; u32 0xCFBFA1C8; u32 0xC2B3293D] in
  assert_norm(List.Tot.length l == vsize_rcon);
  l

let rcon: lseq uint32 vsize_rcon  = createL rcon_list


type branch_len =  n: nat {n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 6 \/ n = 8}

type branch1 = (uint32 & uint32)


inline_for_extraction noextract
val arx: c:uint32 -> branch1 -> Tot branch1

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


inline_for_extraction noextract
let l1 x = (x <<<. size 16)  ^. (x &. (u32 0xffff))


type branch (n: nat) = branch_n: seq uint32 {Seq.Base.length branch_n == n * 2}


val getBranch: #n: branch_len -> i: nat {i < n} -> branch n -> branch1
let getBranch #n i b = Seq.Base.index b (2 * i), Seq.Base.index b (2 * i + 1)


val setBranch: #n: branch_len -> i: nat {i < n} -> branch1 -> branch n -> branch n
let setBranch #n i (x, y) b =
  let b = upd #uint32 #(2 * n) b (2 * i) x in 
  upd #uint32 #(2 * n) b (2 * i + 1) y


let xor_step (#n : branch_len) b (index : nat{index < n}) (tx, ty) = 
  let (xi, yi) = getBranch #n index b in 
  xi ^. tx, yi ^. ty 

let xor #n b = 
  Lib.LoopCombinators.repeati #(tuple2 uint32 uint32) n (Spec.SPARKLE2.xor_step #n b) (u32 0, u32 0)


let xor_x_step (#n: branch_len) (lty, ltx)  (b : branch n) (i : nat {i < n}) (temp: branch n) = 
  let xi, yi = getBranch #n i b in 
  let xi_n, yi_n = xi ^. lty, yi ^. ltx in
  setBranch i (xi_n, yi_n) temp


let xor_x (#n : branch_len) b (lty, ltx) (temp: branch n) : branch n = 
  Lib.LoopCombinators.repeati n (xor_x_step #n (lty, ltx) b) temp


let m #n b temp = 
  let tx, ty = xor #n b in 
  let ltx, lty = l1 tx, l1 ty in
  xor_x #n b (lty, ltx) temp


let l0_step (#n: branch_len) (right : branch n) (i:nat {i < n}) (m: branch n) : branch n = 
  let (xi, yi) = getBranch i right in 
  let (p0i, p1i) = getBranch i m in 
  let branchIUpd = p0i ^. xi, p1i ^. yi in 
  setBranch #n i branchIUpd m


let l1_step (#n: branch_len) (left: branch n)  (i: nat {i < n}) (right: branch n) = 
  setBranch #n i (Spec.SPARKLE2.getBranch #n i left) right


let l2_step (#n: branch_len) (result: branch n) (i: nat {i < n}) (left: branch n) = 
  let j = (i - 1) % pow2 32 % n in 
  setBranch j (getBranch i result) left


val l: #n: branch_len {n % 2 == 0} -> b: branch n -> branch n

let l #n b = 
  let temp = Lib.Sequence.create #uint32 n (u32 0) in  
  let left = sub #uint32 #(2 * n) b 0 n in 
  let right = sub #uint32 #(2 * n) b n n in 
  
  let temp0 = m #(n / 2) left temp in 
  
  let temp1 = Lib.LoopCombinators.repeati #(branch (n / 2)) (n / 2) (l0_step #(n / 2) right) temp0 in 
  let right = Lib.LoopCombinators.repeati #(branch (n / 2)) (n / 2) (l1_step #(n / 2) left) right in 
  let left = Lib.LoopCombinators.repeati #(branch (n / 2)) (n / 2) (l2_step #(n / 2) temp1) left in 

  concat #uint32 #n #n left right


val add2: #n: branch_len {n > 1} -> i: size_nat -> branch n -> Tot (branch n)

let add2 #n i b =
  let (x0,y0) = getBranch 0 b in 
  let (x1,y1) = getBranch 1 b in 
  let y0 = y0 ^. rcon.[(i % vsize_rcon)] in
  let y1 = y1 ^. (u32 i) in
  let b = setBranch 0 (x0, y0) b in setBranch 1 (x1, y1) b


val toBranch: #n: branch_len -> lbytes (8 * n) -> branch n

let toBranch #n input = uints_from_bytes_le #_ #_ #(2 * n) input


val fromBranch: #n: branch_len -> branch n -> lbytes (8 * n)

let fromBranch #n input = uints_to_bytes_le #_ #_ #(2 * n) input


val arx_n_step: #n: branch_len -> i: size_nat {i < n} -> branch n -> branch n

let arx_n_step #n i b = 
  let branchI = getBranch i b in 
  let bi = arx rcon.[i] branchI in 
  setBranch i bi b 


val arx_n: #n: branch_len -> branch n -> branch n 

let arx_n #n b = Lib.LoopCombinators.repeati n arx_n_step b


val mainLoop_step: #n: branch_len {n % 2 == 0} -> i: size_nat -> branch n -> branch n

let mainLoop_step #n i b = 
  let branchZeroMod = add2 #n i b in 
  let arxedBranch = arx_n #n branchZeroMod in 
  l #n arxedBranch


val mainLoop: #n: branch_len {n % 2 == 0} -> branch n -> steps: size_nat -> branch n 

let mainLoop #n b steps = 
  Lib.LoopCombinators.repeati steps mainLoop_step b


val sparkle256: steps: size_nat -> lbytes 32 -> Tot (lbytes 32)

let sparkle256 steps input = 
  let b = toBranch input in 
  let permB = mainLoop b steps in 
  fromBranch #4 permB


val sparkle384: steps: size_nat -> lbytes 48 -> Tot (lbytes 48)

let sparkle384 steps input = 
  let b = toBranch input in 
  let permB = mainLoop b steps in 
  fromBranch #6 permB


val sparkle512: steps: size_nat -> lbytes 64 -> Tot (lbytes 64)

let sparkle512 steps input = 
  let b = toBranch input in 
  let permB = mainLoop b steps in 
  fromBranch #8 permB

