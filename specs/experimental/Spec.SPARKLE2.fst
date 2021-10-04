module Spec.SPARKLE2

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators
open Lib.ByteSequence.Tuples

#set-options "--z3rlimit 15"


let size_word: size_nat = 4


inline_for_extraction
let vsize_rcon: size_nat = 8

inline_for_extraction
let rcon_list: x:list uint32 =
  [@inline_let]
  let l =  [
    u32 0xB7E15162; u32 0xBF715880; u32 0x38B4DA56; u32 0x324E7738;
    u32 0xBB1185EB; u32 0x4F7C7B57; u32 0xCFBFA1C8; u32 0xC2B3293D] in
  assert_norm(List.Tot.length l == vsize_rcon);
  l

let rcon: lseq uint32 vsize_rcon  = createL rcon_list

type branch_len =  n: nat {n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 6 \/ n = 8}

type branch1 = (uint32 & uint32)

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


val l1: x:uint32 -> Tot uint32
let l1 x = (x <<<. size 16)  ^. (x &. (u32 0xffff))


type branch (n: nat) = branch_n: seq uint32 {Seq.Base.length branch_n == n * 2}


val getBranch: #n: branch_len -> i: nat {i < n} -> branch n -> branch1

let getBranch #n i b = Seq.Base.index b (2 * i), Seq.Base.index b (2 * i + 1)


val setBranch: #n: branch_len -> i: nat {i < n} -> branch1 -> branch n -> branch n

let setBranch #n i (x, y) b =
  let b = upd #uint32 #(2 * n) b (2 * i) x in 
  upd #uint32 #(2 * n) b (2 * i + 1) y


val xor: #n: branch_len -> b: branch n -> Tot branch1

let xor #n b = 
  let xor_step (n : branch_len) b (index : nat {index + 1 < n}) (tx, ty) = 
    let (xi, yi) = getBranch #n (index + 1) b in xi ^. tx, yi ^. ty in 
  let zeroBranch = getBranch 0 b in 
  Lib.LoopCombinators.repeati (n - 1) (xor_step n b) zeroBranch


val xor_x: #n: branch_len -> b: branch n -> lty: uint32 -> ltx: uint32 -> branch n

let xor_x #n b lty ltx = 
  let xor_x_step (#n: branch_len) (lty, ltx) (index : nat {index < n}) (b : branch n) = 
    let xi, yi = getBranch #n index b in 
    let xi_n, yi_n = xi ^. lty, yi ^. ltx in
    let s = setBranch index (xi_n, yi_n) b in s in
  Lib.LoopCombinators.repeati n (xor_x_step #n (lty, ltx)) b


val m: #n: branch_len -> branch n -> Tot (branch n)

let m #n b = 
  let tx, ty = xor #n b in 
  let ltx, lty = l1 tx, l1 ty in
  xor_x #n b lty ltx


val l: #n: branch_len {n % 2 == 0} -> b: branch n -> branch n

let l #n0 b = 
  let leftBranch: branch (n0 / 2)  = sub #_ #(2 * n0) b 0 n0 in 
  let rightBranch: branch (n0 / 2) = sub #_ #(2 * n0) b n0 n0 in 
  let perm = m leftBranch in 
  
  let seqEmpty: branch (n0 / 2) = create n0 (u32 0) in 
  
  let l_step (#n: branch_len) (rightBranch : branch n) (perm: branch n) (i:nat {i < n}) (branchResult : branch n) : branch n = 
    let (xi, yi) = getBranch i rightBranch in 
    let (p0i, p1i) = getBranch i perm in 
    let branchIUpd = xi ^. p0i, yi ^. p1i in 
    let s = setBranch #n ((i - 1) % n) branchIUpd branchResult in s in  

  let r = Lib.LoopCombinators.repeati (n0 / 2) (l_step rightBranch perm) seqEmpty in 
  concat #_ #n0 #n0 r leftBranch


val add2: #n: branch_len {n >= 2} -> i: size_nat -> branch n -> Tot (branch n)

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


val arx_n_step: #n: branch_len -> i: size_nat {i < n} -> branch n-> branch n

let arx_n_step #n i b = 
  let branchI = getBranch i b in 
  let bi = arx rcon.[i] branchI in 
  setBranch i bi b 


val arx_n: #n: branch_len -> branch n -> branch n 

let arx_n #n b = Lib.LoopCombinators.repeati n arx_n_step b


val mainLoop_step: #n: branch_len {n % 2 == 0 } ->  i: size_nat -> branch n -> branch n

let mainLoop_step #n i b = 
  let branchZeroMod = add2 i b in 
  let arxedBranch = arx_n branchZeroMod in 
  l branchZeroMod


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
