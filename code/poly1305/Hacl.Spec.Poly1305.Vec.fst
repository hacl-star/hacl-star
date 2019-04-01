module Hacl.Spec.Poly1305.Vec

#reset-options "--z3rlimit 60 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.IntVector

(* Field types and parameters *)
let prime : pos =
  let p = pow2 130 - 5 in
  assert_norm (p > 0);
  p

val lemma_pow2_128: n:nat ->
  Lemma
  (requires n <= 128)
  (ensures pow2 n < prime)
  [SMTPat (pow2 n)]
let lemma_pow2_128 n =
  Math.Lemmas.pow2_le_compat 128 n;
  assert (pow2 n <= pow2 128);
  assert_norm (pow2 128 < prime)

let pfelem = x:nat{x < prime}
let pfadd (x:pfelem) (y:pfelem) : pfelem = (x + y) % prime
let pfmul (x:pfelem) (y:pfelem) : pfelem = (x * y) % prime

let lanes = w:width{w == 1 \/ w == 2 \/ w == 4}
type elem (w:lanes) = lseq pfelem w

unfold
let to_elem (w:lanes) (x:pfelem) : elem w = create w x
let from_elem (#w:lanes) (x:elem w) : pfelem = x.[0]
let zero (w:lanes) : elem w = to_elem w 0

let fadd (#w:lanes) (x:elem w) (y:elem w) : elem w =
  map2 pfadd x y
let fmul (#w:lanes) (x:elem w) (y:elem w) : elem w =
  map2 pfmul x y

(* Specification *)
let size_block : size_nat = 16
let size_key   : size_nat = 32

type block = lbytes size_block
type tag   = lbytes size_block
type key   = lbytes size_key

let load_elem1 (b:block) : elem 1 =
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


let update1 (r:pfelem) (len:size_nat{len <= size_block}) (b:lbytes len) (acc:pfelem) : pfelem =
  let e = nat_from_bytes_le b in
  let e = pfadd (pow2 (8 * len)) e in
  let acc = pfmul (pfadd acc e) r in
  acc

let updaten (#w:lanes) (r_w:elem w) (b:lbytes (w * size_block)) (acc:elem w) : elem w =
  let e = load_elem #w b in
  let e = map (pfadd (pow2 128)) e in
  let acc = fadd (fmul acc r_w) e in
  acc

let normalize_1 (acc:elem 1) (r:elem 1) : pfelem =
  pfmul acc.[0] r.[0]

let normalize_2 (acc:elem 2) (r:elem 2) : pfelem =
  let r = r.[0] in
  let r2 = pfmul r r in
  let r21 = create2 r2 r in
  let a = fmul acc r21 in
  pfadd a.[0] a.[1]

let normalize_4 (acc:elem 4) (r:elem 4) : pfelem =
  let r = r.[0] in
  let r2 = pfmul r r in
  let r3 = pfmul r2 r in
  let r4 = pfmul r2 r2 in
  let r4321 = create4 r4 r3 r2 r in
  let a = fmul acc r4321 in
  pfadd (pfadd (pfadd a.[0] a.[1]) a.[2]) a.[3]

let normalize_n (#w:lanes) (acc:elem w) (r:elem w) : pfelem =
  match w with
  | 1 -> normalize_1 acc r
  | 2 -> normalize_2 acc r
  | 4 -> normalize_4 acc r

let compute_r1 (#w:lanes) (r:elem w) : elem w = r
let compute_r2 (#w:lanes) (r:elem w) : elem w = fmul r r
let compute_r4 (#w:lanes) (r:elem w) : elem w = fmul (fmul r r) (fmul r r)
let compute_rw (#w:lanes) (r:elem w) : elem w =
  match w with
  | 1 -> compute_r1 r
  | 2 -> compute_r2 r
  | 4 -> compute_r4 r

let poly_update_multi (#w:lanes) (text:bytes{length text % (w * size_block) = 0}) (acc:elem w) (r:elem w) : pfelem =
  let rw = compute_rw r in
  let acc = repeat_blocks_multi #uint8 #(elem w) (w * size_block) text (updaten rw) acc in
  normalize_n acc r

let poly_update1_rem (r:pfelem) (l:size_nat{l < 16}) (block:lbytes l) (acc:pfelem) : pfelem =
  if l = 0 then acc else update1 r l block acc

let poly_update1 (text:bytes) (acc:pfelem) (r:pfelem) : pfelem =
  repeat_blocks #uint8 #pfelem size_block text
  (update1 r size_block)
  (poly_update1_rem r)
  acc

let poly (#w:lanes) (text:bytes) (acc:elem w) (r:elem w) : pfelem =
  let len = length text in
  let sz_block = w * size_block in
  let len0 = len / sz_block * sz_block in
  let t0 = Seq.slice text 0 len0 in
  let acc = poly_update_multi t0 acc r in

  let t1 = Seq.slice text len0 len in
  poly_update1 t1 acc (from_elem r)

let poly_update (#w:lanes) (text:bytes) (acc:elem w) (r:elem w) : pfelem =
  match w with
  | 1 -> poly_update1 text (from_elem acc) (from_elem r)
  | 2 -> poly text acc r
  | 4 -> poly text acc r

let finish (k:key) (acc:pfelem) : tag =
  let s = nat_from_bytes_le (sub k 16 16) in
  let n = (acc + s) % pow2 128 in
  nat_to_bytes_le 16 n

let encode_r (#w:lanes) (rb:block) : elem w =
  let lo = uint_from_bytes_le (sub rb 0 8) in
  let hi = uint_from_bytes_le (sub rb 8 8) in
  let mask0 = u64 0x0ffffffc0fffffff in
  let mask1 = u64 0x0ffffffc0ffffffc in
  let lo = lo &. mask0 in
  let hi = hi &. mask1 in
  to_elem w (uint_v hi * pow2 64 + uint_v lo)

let poly1305_init (#w:lanes) (k:key) : elem w & elem w =
  let r = encode_r (sub k 0 16) in
  zero w, r

let poly1305 (#w:lanes) (msg:bytes) (k:key) : tag =
  let acc, r = poly1305_init #w k in
  let acc = poly_update #w msg acc r in
  finish k acc

let poly1305_vec_is_poly1305 (#w: lanes) (msg: bytes) (k: key):
  Lemma
    (ensures (poly1305 #w msg k == Spec.Poly1305.poly1305 msg k))
=
  // The central spec equivalence lemma. Proved for the case M32 (see
  // Hacl.Spec.Poly1305.Equiv). The vectorized spec is in progress and we disable
  // for EverCrypt v1 the vectorized implementations.
  admit ()
