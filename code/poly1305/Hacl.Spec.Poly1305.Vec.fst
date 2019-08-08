module Hacl.Spec.Poly1305.Vec

#reset-options "--z3rlimit 60 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.IntVector

module Scalar = Spec.Poly1305

(* Field types and parameters *)
val lemma_pow2_128: n:nat ->
  Lemma
  (requires n <= 128)
  (ensures pow2 n < Scalar.prime)
  [SMTPat (pow2 n)]
let lemma_pow2_128 n =
  Math.Lemmas.pow2_le_compat 128 n;
  assert (pow2 n <= pow2 128);
  assert_norm (pow2 128 < Scalar.prime)

let prime = Scalar.prime
let pfelem = Scalar.felem
let pfadd (x:pfelem) (y:pfelem) : pfelem = Scalar.fadd x y
let pfmul (x:pfelem) (y:pfelem) : pfelem = Scalar.fmul x y

let lanes = w:width{w == 1 \/ w == 2 \/ w == 4}
type elem (w:lanes) = lseq pfelem w


let to_elem (w:lanes) (x:pfelem) : elem w = create w x
let from_elem (#w:lanes) (x:elem w) : pfelem = x.[0]
let zero (w:lanes) : elem w = to_elem w 0

let fadd (#w:lanes) (x:elem w) (y:elem w) : elem w =
  map2 pfadd x y
let fmul (#w:lanes) (x:elem w) (y:elem w) : elem w =
  map2 pfmul x y

(* Specification *)
let size_block : size_nat = Scalar.size_block

let load_elem1 (b:Scalar.block) : elem 1 =
  to_elem 1 (nat_from_bytes_le b)

let load_elem2 (b:lbytes (2 * size_block)) : elem 2 =
  let b1 = nat_from_bytes_le (sub b 0 size_block) in
  let b2 = nat_from_bytes_le (sub b size_block size_block) in
  create2 b1 b2

let load_elem4 (b:lbytes (4 * size_block)) : elem 4 =
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

let load_blocks (#w:lanes) (b:lbytes (w * size_block)) : elem w =
  let e = load_elem #w b in
  let e = map (pfadd (pow2 128)) e in
  e

let load_acc1 (text:lbytes size_block) (acc:pfelem) : elem 1 =
  let acc = create 1 acc in
  fadd acc (load_blocks #1 text)

let load_acc2 (text:lbytes (2 * size_block)) (acc:pfelem) : elem 2 =
  let acc = create2 acc 0 in
  fadd acc (load_blocks #2 text)

let load_acc4 (text:lbytes (4 * size_block)) (acc:pfelem) : elem 4 =
  let acc = create4 acc 0 0 0 in
  fadd acc (load_blocks #4 text)

let load_acc (#w:lanes) (text:lbytes (w * size_block)) (acc:pfelem) : elem w =
  match w with
  | 1 -> load_acc1 text acc
  | 2 -> load_acc2 text acc
  | 4 -> load_acc4 text acc

let normalize_1 (r:pfelem) (acc:elem 1) : pfelem =
  pfmul acc.[0] r

let normalize_2 (r:pfelem) (acc:elem 2) : pfelem =
  let r2 = pfmul r r in
  let r21 = create2 r2 r in
  let a = fmul acc r21 in
  pfadd a.[0] a.[1]

let normalize_4 (r:pfelem) (acc:elem 4) : pfelem =
  let r2 = pfmul r r in
  let r3 = pfmul r2 r in
  let r4 = pfmul r2 r2 in
  let r4321 = create4 r4 r3 r2 r in
  let a = fmul acc r4321 in
  pfadd (pfadd (pfadd a.[0] a.[1]) a.[2]) a.[3]

let normalize_n (#w:lanes) (r:pfelem) (acc:elem w) : pfelem =
  match w with
  | 1 -> normalize_1 r acc
  | 2 -> normalize_2 r acc
  | 4 -> normalize_4 r acc

let compute_r1 (r:pfelem) : elem 1 = to_elem 1 r
let compute_r2 (r:pfelem) : elem 2 = to_elem 2 (pfmul r r)
let compute_r4 (r:pfelem) : elem 4 = to_elem 4 (pfmul (pfmul r r) (pfmul r r))
let compute_rw (#w:lanes) (r:pfelem) : elem w =
  match w with
  | 1 -> compute_r1 r
  | 2 -> compute_r2 r
  | 4 -> compute_r4 r


let poly1305_update_nblocks (#w:lanes) (r_w:elem w) (b:lbytes (w * size_block)) (acc:elem w) : elem w =
  let e = load_blocks b in
  let acc = fadd (fmul acc r_w) e in
  acc


let poly1305_update_multi (#w:lanes) (text:bytes{0 < length text /\ length text % (w * size_block) = 0}) (acc:pfelem) (r:pfelem) : pfelem =
  let rw = compute_rw r in
  let acc = load_acc (Seq.slice text 0 (w * size_block)) acc in
  let text = Seq.slice text (w * size_block) (length text) in
  let acc = repeat_blocks_multi #uint8 #(elem w) (w * size_block) text (poly1305_update_nblocks rw) acc in
  let acc = normalize_n r acc in
  acc


let poly1305_update_vec (#w:lanes) (text:bytes) (acc:pfelem) (r:pfelem) : pfelem =
  let len = length text in
  let sz_block = w * size_block in
  let len0 = len / sz_block * sz_block in
  let t0 = Seq.slice text 0 len0 in
  let acc = if len0 > 0 then poly1305_update_multi #w t0 acc r else acc in

  let t1 = Seq.slice text len0 len in
  Scalar.poly1305_update t1 acc r


let poly1305_update (#w:lanes) (text:bytes) (acc:pfelem) (r:pfelem) : pfelem =
  match w with
  | 1 -> Scalar.poly1305_update text acc r
  | 2 -> poly1305_update_vec #2 text acc r
  | 4 -> poly1305_update_vec #4 text acc r


let poly1305_mac (#w:lanes) (msg:bytes) (k:Scalar.key) : Scalar.tag =
  let acc, r = Scalar.poly1305_init k in
  let acc = poly1305_update #w msg acc r in
  Scalar.poly1305_finish k acc
