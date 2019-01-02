module Spec.Poly1305_Vec

#reset-options "--z3rlimit 60 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.IntVector

/// Constants and Types

(* Field types and parameters *)
let prime : pos =
  let p = pow2 130 - 5 in
  assert_norm(p >0);
  p

let pfelem = (x:nat{x < prime})
let pfadd (x:pfelem) (y:pfelem) : pfelem = (x + y) % prime
let pfmul (x:pfelem) (y:pfelem) : pfelem = (x * y) % prime

let lanes = w:width{w == 1 \/ w == 2 \/ w == 4}
type elem (w:lanes) = lseq pfelem w

let to_elem (w:lanes) (x:pfelem) : elem w = create w x
let from_elem (#w:lanes) (x:elem w) : pfelem = x.[0]
let zero (w:lanes) : elem w = to_elem  w 0

let fadd (#w:lanes) (x:elem w) (y:elem w) : elem w = 
    map2 pfadd x y 
let fmul (#w:lanes) (x:elem w) (y:elem w) : elem w = 
    map2 pfmul x y 

(* Poly1305 parameters *)
let size_block : size_nat = 16
let size_key   : size_nat = 32

(* TODO: Remove, left here to avoid breaking implementation *)
let blocksize = size_block
let keysize = size_key

type block = lbytes size_block
type tag   = lbytes size_block
type key   = lbytes size_key

let load_elem1 (b:block) : elem 1 =
  assert_norm (pow2 128 < prime);
  to_elem 1 (nat_from_bytes_le b)

let load_elem2 (b:lbytes (2 * size_block)) : elem 2 =
  assert_norm (pow2 128 < prime);
  let b1 = nat_from_bytes_le (sub b 0 size_block) in
  let b2 = nat_from_bytes_le (sub b size_block size_block) in
  create2 b1 b2

let load_elem4 (b:lbytes (4 * size_block)) : elem 4 =
  assert_norm (pow2 128 < prime);
  let b1 = nat_from_bytes_le (sub b 0 size_block) in
  let b2 = nat_from_bytes_le (sub b size_block size_block) in
  let b3 = nat_from_bytes_le (sub b (2 * size_block) size_block) in
  let b4 = nat_from_bytes_le (sub b (3 * size_block) size_block) in
  create4 b1 b2 b3 b4

let load_elem (#w:lanes) (b:lbytes (w * size_block)) : elem w =
  match w with
  | 1 -> load_elem1 b
  | 2 -> load_elem2 b
  | 4 -> load_elem4 b
  

/// Specification

let update1 (#w:lanes) (r:elem w) (len:size_nat{len <= size_block}) (b:lbytes len) (acc:elem w) : Tot (elem w) =
  Math.Lemmas.pow2_le_compat 128 (8 * len);
  assert (pow2 (8 * len) <= pow2 128);
  assert_norm (pow2 128 + pow2 128 < prime);
  let n = to_elem w (pow2 (8 * len) + nat_from_bytes_le b) in
  let acc : elem w = fmul (fadd n acc) r in
  acc

let updaten (#w:lanes) (r_w:elem w) (b:lbytes (w * size_block)) (acc:elem w) : Tot (elem w) =
  Math.Lemmas.pow2_le_compat 128 (8 * 16);
  assert (pow2 (8 * 16) <= pow2 128);
  assert_norm (pow2 128 + pow2 128 < prime);
  let e = load_elem #w b in
  let e = map (pfadd (pow2 128)) e in
  let acc : elem w = fadd (fmul acc r_w) e in
  acc

let normalize_1 (acc:elem 1) (r:elem 1) : Tot (elem 1) = 
    fmul acc r
let normalize_2 (acc:elem 2) (r:elem 2) : Tot (elem 2) =
    assert_norm ( 1 < prime ) ;
    let r1 = r.[0] in
    let r2 = pfmul r1 r1  in
    let r21 = create2 r2 r1 in
    let a = fmul acc r21 in
    let a0 = pfadd a.[0] a.[1] in
    (to_elem 2 a0)
let normalize_4 (acc:elem 4) (r:elem 4) : Tot (elem 4) =
    assert_norm ( 1 < prime ) ;
    let r1 = r.[0] in
    let r2 = pfmul r1 r1  in
    let r3 = pfmul r2 r1 in
    let r4 = pfmul r2 r2 in
    let r4321 = create4 r4 r3 r2 r1 in
    let a = fmul acc r4321 in
    let a0 = pfadd (pfadd (pfadd a.[0] a.[1]) a.[2]) a.[3] in
    (to_elem 4 a0)
let normalize_n (#w:lanes) (acc:elem w) (r:elem w) : Tot (elem w) =
  match w with
  | 1 -> normalize_1 acc r
  | 2 -> normalize_2 acc r
  | 4 -> normalize_4 acc r


let compute_r1 (#w:lanes) (r:elem w) : elem w = r
let compute_r2 (#w:lanes) (r:elem w) : elem w = 
    fmul r r
let compute_r4 (#w:lanes) (r:elem w) : elem w = 
    fmul (fmul r r) (fmul r r)
let compute_rw (#w:lanes) (r:elem w) : elem w = 
  match w with
  | 1 -> compute_r1 r
  | 2 -> compute_r2 r
  | 4 -> compute_r4 r
  
let poly (#w:lanes) (text:bytes) (acc:elem w) (r:elem w) : Tot (elem w) =
  let rw = compute_rw r in
  repeat_blocks #uint8 #(elem w) (w * size_block) text
    (fun b -> updaten rw b)
    (fun l b res -> 
      let ne = normalize_n res r in
      repeat_blocks #uint8 #(elem w) size_block b
      (fun bl -> update1 r size_block bl)
      (fun l b res -> if l = 0 then res else update1 r l b res)
      ne 
    )
    acc

let finish (#w:lanes) (acc:elem w) (s:nat{s < pow2 128}) : Tot tag =
  let n = (from_elem acc + s) % pow2 128 in
  nat_to_bytes_le 16 n

let encode_r (#w:lanes) (rb:block) : Tot (elem w) =
  assert_norm (pow2 128 < prime);
  let (&.) = logand #U8 in
  let rb = rb.[3] <- rb.[3] &. u8 15 in
  let rb = rb.[7] <- rb.[7] &. u8 15 in
  let rb = rb.[11] <- rb.[11] &. u8 15 in
  let rb = rb.[15] <- rb.[15] &. u8 15 in
  let rb = rb.[4] <- rb.[4] &. u8 252 in
  let rb : lseq uint8 16 = rb.[8] <- rb.[8] &. u8 252 in
  let rb : lseq uint8 16 = rb.[12] <- rb.[12] &. u8 252 in
  to_elem w (nat_from_bytes_le rb)

let poly1305_init (#w:lanes) (k:key) : Tot (elem w & elem w & n:nat{n < pow2 128}) =
  let r = encode_r (slice k 0 16) in
  let s = nat_from_bytes_le (slice k 16 32) in
  zero w, r, s

let poly1305 (#w:lanes) (msg:bytes) (k:key) : Tot tag =
  let (acc,r,s) = poly1305_init #w k in
  let acc = poly #w msg acc r in
  finish acc s
