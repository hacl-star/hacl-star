module Spec.SHA2.Generic

open FStar.Mul
open FStar.Seq
open FStar.UInt32
open Spec.Loops
open Spec.Lib

type lseq 'a n = s:seq 'a{length s = n}
type byte = UInt8.t 
type u8 = UInt8.t
type u32 = UInt32.t
type u64 = UInt32.t
type rotval (size:nat) = r:u32{v r > 0 /\ v r < size}

let rec big_bytes #max (start:nat) (len:nat{start+len <= max}) (n:nat{n < pow2 (8 * len)}) (s:lseq u8 max) : lseq u8 max =
  if len = 0 then 
    s
  else
    let len = len - 1 in 
    let byte = UInt8.uint_to_t (n % 256) in
    let n' = n / 256 in 
    let s = s.[start+len] <- byte in
    big_bytes #max start len n' s

let write #n (s:lseq 'a n) (i:nat{i < n}) (v:'a) : (t:lseq 'a n) = 
    upd s i v
   

noeq
type word (w:Type) (size:nat) = {
     word0: w;
     to_be: len:nat -> lseq w len -> lseq byte (size * len);
     from_be: len:nat -> lseq byte (size * len) -> lseq w len;
     add_mod: w -> w -> w;
     logxor: w -> w -> w;
     logand: w -> w -> w;
     logor: w -> w -> w;
     lognot: w -> w;
     shift_right: w -> s:u32{v s < 8 * size} -> w;
     rotate_right: w -> rotval size -> w
     }
     

noeq type sha2_params =
  | MkParams: wt:Type -> sz:nat{sz = 4 \/ sz = 8} -> w:word wt sz -> 
	      opTable: lseq (rotval sz) 12 ->
	      lenSize: nat{lenSize > 0 /\ lenSize <= 16} ->
	      kSize: nat{kSize > 16} ->
	      kTable: lseq wt kSize ->
	      h0: lseq wt 8 -> 
	      hashSize: nat {hashSize <= 8 * sz} ->
	      sha2_params

let _Ch p x y z = p.w.logxor (p.w.logand x y)
                           (p.w.logand (p.w.lognot x) z)

let _Maj p x y z = p.w.logxor (p.w.logand x y)
                            (p.w.logxor (p.w.logand x z)
                                         (p.w.logand y z))

let _Sigma0 p x = p.w.logxor (p.w.rotate_right x p.opTable.[0])
                                (p.w.logxor (p.w.rotate_right x p.opTable.[1])
                                               (p.w.rotate_right x p.opTable.[2]))

let _Sigma1 p x = p.w.logxor (p.w.rotate_right x p.opTable.[3])
                                (p.w.logxor (p.w.rotate_right x p.opTable.[4])
                                               (p.w.rotate_right x p.opTable.[5]))

let _sigma0 p x = p.w.logxor (p.w.rotate_right x p.opTable.[6])
                                (p.w.logxor (p.w.rotate_right x p.opTable.[7])
                                               (p.w.shift_right x p.opTable.[8]))

let _sigma1 p x = p.w.logxor (p.w.rotate_right x p.opTable.[9])
                                (p.w.logxor (p.w.rotate_right x p.opTable.[10])
                                               (p.w.shift_right x p.opTable.[11]))


type block_w p = b:lseq p.wt 16
type hash_w p = b:lseq p.wt 8
let size_block p = 16 * p.sz
let size_hash p = 8 * p.sz

let op_String_Access = Seq.index
let op_String_Assignment = Seq.upd

let step_ws0 p (b:block_w p) (s:lseq p.wt p.kSize) (i:nat{i >= 0 /\ i < 16}) : (t:lseq p.wt p.kSize) = 
    s.[i] <- b.[i]

let step_ws1 p (s:lseq p.wt p.kSize) (i:nat{i >= 16 /\ i < p.kSize}) : (t:lseq p.wt p.kSize) =
      let t16 = s.[i - 16] in
      let t15 = s.[i - 15] in
      let t7  = s.[i - 7] in
      let t2  = s.[i - 2] in
      let s1 = _sigma1 p t2 in
      let s0 = _sigma0 p t15 in
      s.[i] <- p.w.add_mod s1 (p.w.add_mod t7 (p.w.add_mod s0 t16))
      
let ws p (b:block_w p) =
  let s = Seq.create p.kSize p.w.word0 in
  let s = Spec.Loops.repeat_range_spec 0 16 (step_ws0 p b) s in
  let s = Spec.Loops.repeat_range_spec 16 p.kSize (step_ws1 p) s in
  s
  
(* Core shuffling function *)
let shuffle_core p (wsTable:lseq p.wt p.kSize) (hash:hash_w p) (t:nat{t >= 0 /\ t < p.kSize}) : Tot (hash_w p) =
  let a0 = hash.[0] in
  let b0 = hash.[1] in
  let c0 = hash.[2] in
  let d0 = hash.[3] in
  let e0 = hash.[4] in
  let f0 = hash.[5] in
  let g0 = hash.[6] in
  let h0 = hash.[7] in

  let t1 = p.w.add_mod h0 (p.w.add_mod (_Sigma1 p e0) (p.w.add_mod (_Ch p e0 f0 g0) (p.w.add_mod p.kTable.[t] (wsTable.[t])))) in
  let t2 = p.w.add_mod (_Sigma0 p a0) (_Maj p a0 b0 c0) in

  let hash = hash.[0] <- p.w.add_mod t1 t2 in
  let hash = hash.[1] <- a0 in
  let hash = hash.[2] <- b0 in
  let hash = hash.[3] <- c0 in
  let hash = hash.[4] <- (p.w.add_mod d0 t1) in
  let hash = hash.[5] <- e0 in
  let hash = hash.[6] <- f0 in
  let hash = hash.[7] <- g0 in
  hash


(* Full shuffling function *)
let shuffle (p:sha2_params) (wsTable:lseq p.wt p.kSize) (hash:hash_w p) : Tot (hash_w p) =
  Spec.Loops.repeat_range_spec 0 p.kSize (shuffle_core p wsTable) hash


(* Compression function *)
let update_block (p:sha2_params) (block:bytes{length block = size_block p}) (hash:hash_w p) : Tot (hash_w p) =
  let block_w = p.w.from_be 16 block in
  let wsTable = ws p block_w in
  let hash_1 = shuffle p wsTable hash in
  Spec.Lib.map2 (fun x y -> p.w.add_mod x y) hash hash_1

let update_multi (p:sha2_params) (n:nat) (blocks:bytes{length blocks = n * size_block p}) (hash:hash_w p) : Tot (hash_w p) =
  let bl = size_block p in
  Spec.Loops.repeat_range_spec 0 n 
    (fun h i -> update_block p (Seq.slice blocks (bl * i) (bl * (i+1))) h)
    hash
  
let padding_blocks p (len:nat) : nat = 
  if (len < size_block p - p.lenSize) then 1 else 2

let padding_size p (len:nat) = size_block p * padding_blocks p len 

let pad p (n:nat) (last:seq u8{length last < size_block p /\ 
			     8 * (n * size_block p + length last) < pow2 (8 * p.lenSize)}) : 
				    lseq u8 (padding_size p (length last)) =
  let lastlen = length last in
  let blocks = padding_blocks p lastlen in
  let plen = blocks * size_block p in
  let padding : lseq byte plen = Seq.create plen 0uy in
  let tlen = n * size_block p + lastlen in
  let padding = Spec.Loops.repeat_range_spec 0 lastlen 
			(fun s i -> write #byte #plen s i last.[i]) padding in 
  let padding = Spec.Loops.repeat_range_spec (lastlen + 1) (plen - p.lenSize)
			(fun s i -> write #byte #plen s i 0uy) padding in 
  let tlenbits = FStar.Mul.(tlen * 8) in  
  let padding = big_bytes #plen (plen - p.lenSize) p.lenSize tlenbits padding in
  padding
  
let update_last p (n:nat) (last:seq u8{
		             length last < size_block p /\ 
			     8 * (n * size_block p + length last) < pow2 (8 * p.lenSize)}) 
		        (hash:hash_w p) : Tot (hash_w p) =
  let blocks = pad p n last in
  update_multi p (padding_blocks p (length last)) blocks hash

let finish p (hash:hash_w p) : lseq byte p.hashSize =
  let hash_final = p.w.to_be 8 hash in
  let h,_ = Seq.split hash_final p.hashSize in
  h

#reset-options "--z3rlimit 10"

let hash p (input:bytes{8 * length input < pow2 (8 * p.lenSize)}) : lseq byte p.hashSize = 
  let n = Seq.length input / (size_block p) in
  let prevlen = n * (size_block p) in
  let (bs,l) = Seq.split input prevlen in
  let hash = update_multi p n bs p.h0 in
  let hash = update_last p n l hash in
  finish p hash

let hash' p (input:bytes{8 * length input < pow2 (8 * p.lenSize)}) : lseq byte p.hashSize = 
  let n = Seq.length input / (size_block p) in
  let prevlen = n * (size_block p) in
  let (blocks,last) = Seq.split input prevlen in
  let padding = pad p n last in 
  let lastlen = length last in
  let padn = padding_blocks p lastlen in
  finish p (update_multi p (n + padn) (blocks @| padding) p.h0)

(*************)

let rotate_right32 (x:UInt32.t) (s:UInt32.t{0 < v s /\ v s < 32}) : Tot UInt32.t =
  ((x >>^ s) |^ (x <<^ (32ul -^ s)))

let rotate_right64 (a:UInt64.t) (s:UInt32.t{0 < v s /\ v s < 64}) : Tot UInt64.t =
  FStar.UInt64.((a >>^ s) |^ (a <<^ (UInt32.sub 64ul s)))

val u32s_from_be: len:nat -> lseq byte (4 * len) -> lseq u32 len
let u32s_from_be l s = Spec.Lib.uint32s_from_be l s 

val shift_right32: n:u32 -> s:u32{v s < 32} -> u32
let shift_right32 n s = UInt32.shift_right n s 

val u64s_from_be: len:nat -> lseq byte (8 * len) -> lseq u64 len
let u64s_from_be l s = Spec.Lib.uint64s_from_be l s 

val shift_right64: n:u64 -> s:u32{v s < 64} -> u64
let shift_right64 n s = UInt64.shift_right n s 

let word32 : word u32 4 = {
  word0 = 0ul;
  to_be = Spec.Lib.uint32s_to_be;
  from_be = u32s_from_be;
  add_mod = UInt32.add_mod;
  logxor = UInt32.logxor;
  logand = UInt32.logand;
  logor = UInt32.logor;
  lognot = UInt32.lognot;
  shift_right = shift_right32;
  rotate_right = rotate_right32;
}

let word64 : word u32 8 = {
  word0 = 0uL;
  to_be = Spec.Lib.uint64s_to_be;
  from_be = u64s_from_be;
  add_mod = UInt64.add_mod;
  logxor = UInt64.logxor;
  logand = UInt64.logand;
  logor = UInt64.logor;
  lognot = UInt64.lognot;
  shift_right = shift_right64;
  rotate_right = rotate_right64;
}
