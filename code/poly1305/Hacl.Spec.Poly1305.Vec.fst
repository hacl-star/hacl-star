module Hacl.Spec.Poly1305.Vec

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.IntVector

module Scalar = Spec.Poly1305

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

(* Field types and parameters *)
val lemma_pow2_128: n:nat -> Lemma
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

let lanes = w:width{w == 1 \/ w == 2 \/ w == 4 \/ w == 8}
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

let load_elem1 (#w:lanes) (b:lbytes (w * size_block)) (i:nat{i < w}) : pfelem =
  nat_from_bytes_le (sub b (i * size_block) size_block)

let load_elem (#w:lanes) (b:lbytes (w * size_block)) : elem w =
  createi w (load_elem1 #w b)

let load_blocks (#w:lanes) (b:lbytes (w * size_block)) : elem w =
  let e = load_elem #w b in
  map (pfadd (pow2 128)) e

let load_acc (#w:lanes) (text:lbytes (w * size_block)) (acc0:pfelem) : elem w =
  let acc = create w 0 in
  let acc = acc.[0] <- acc0 in
  fadd acc (load_blocks #w text)

let precomp_rw1 (r:pfelem) : elem 1 =
  to_elem 1 r

let precomp_rw2 (r:pfelem) : elem 2 =
  let r2 = pfmul r r in
  create2 r2 r

let precomp_rw4 (r:pfelem) : elem 4 =
  let r2 = pfmul r r in
  let r3 = pfmul r2 r in
  let r4 = pfmul r2 r2 in
  create4 r4 r3 r2 r

let precomp_rw8 (r:pfelem) : elem 8 =
  let r2 = pfmul r r in
  let r3 = pfmul r2 r in
  let r4 = pfmul r2 r2 in
  let r5 = pfmul r3 r2 in
  let r6 = pfmul r4 r2 in
  let r7 = pfmul r5 r2 in
  let r8 = pfmul r6 r2 in
  create8 r8 r7 r6 r5 r4 r3 r2 r

let precomp_rw (#w:lanes) (r:pfelem) : elem w =
  match w with
  | 1 -> precomp_rw1 r
  | 2 -> precomp_rw2 r
  | 4 -> precomp_rw4 r
  | 8 -> precomp_rw8 r

let normalize1 (a:elem 1) : pfelem = a.[0]
let normalize2 (a:elem 2) : pfelem = pfadd a.[0] a.[1]
let normalize4 (a:elem 4) : pfelem = pfadd (pfadd (pfadd a.[0] a.[1]) a.[2]) a.[3]
let normalize8 (a:elem 8) : pfelem = pfadd (pfadd (pfadd (pfadd (pfadd (pfadd (pfadd a.[0] a.[1]) a.[2]) a.[3]) a.[4]) a.[5]) a.[6]) a.[7]

let normalize_n (#w:lanes) (r:pfelem) (acc:elem w) : pfelem =
  let pre = precomp_rw #w r in
  let acc = fmul acc pre in
  match w with
  | 1 -> normalize1 acc
  | 2 -> normalize2 acc
  | 4 -> normalize4 acc
  | 8 -> normalize8 acc

// TODO:
// let pre = precomp_rw #w r in
// create w pre.[0] == compute_rw #w r
let compute_r1 (r:pfelem) : elem 1 = to_elem 1 r
let compute_r2 (r:pfelem) : elem 2 = to_elem 2 (pfmul r r)
let compute_r4 (r:pfelem) : elem 4 = to_elem 4 (pfmul (pfmul r r) (pfmul r r))
let compute_r8 (r:pfelem) : elem 8 = to_elem 8 (pfmul (pfmul (pfmul r r) (pfmul r r)) (pfmul (pfmul r r) (pfmul r r)))
let compute_rw (#w:lanes) (r:pfelem) : elem w =
  match w with
  | 1 -> compute_r1 r
  | 2 -> compute_r2 r
  | 4 -> compute_r4 r
  | 8 -> compute_r8 r


let poly1305_update_nblocks (#w:lanes) (r_w:elem w) (b:lbytes (w * size_block)) (acc:elem w) : elem w =
  let e = load_blocks b in
  let acc = fadd (fmul acc r_w) e in
  acc


let poly1305_update_multi (#w:lanes) (text:bytes{0 < length text /\ length text % (w * size_block) = 0}) (acc:pfelem) (r:pfelem) : pfelem =
  let rw = compute_rw #w r in
  let blocksize_v = w * size_block in
  let t0 = Seq.slice text 0 blocksize_v in
  let t1 = Seq.slice text blocksize_v (length text) in

  let acc = load_acc #w t0 acc in
  let acc = repeat_blocks_multi #uint8 #(elem w) blocksize_v t1 (poly1305_update_nblocks rw) acc in
  let acc = normalize_n #w r acc in
  acc


let poly1305_update_vec (#w:lanes) (text:bytes) (acc:pfelem) (r:pfelem) : pfelem =
  let len = length text in
  let blocksize_v = w * size_block in
  let len0 = len / blocksize_v * blocksize_v in
  let t0 = Seq.slice text 0 len0 in
  let acc = if len0 > 0 then poly1305_update_multi #w t0 acc r else acc in

  let t1 = Seq.slice text len0 len in
  Scalar.poly1305_update t1 acc r


let poly1305_update (#w:lanes) (text:bytes) (acc:pfelem) (r:pfelem) : pfelem =
  match w with
  | 1 -> Scalar.poly1305_update text acc r
  | 2 -> poly1305_update_vec #2 text acc r
  | 4 -> poly1305_update_vec #4 text acc r
  | 8 -> poly1305_update_vec #8 text acc r


let poly1305_mac (#w:lanes) (msg:bytes) (k:Scalar.key) : Scalar.tag =
  let acc, r = Scalar.poly1305_init k in
  let acc = poly1305_update #w msg acc r in
  Scalar.poly1305_finish k acc
