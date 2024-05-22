module Hacl.Spec.GF128.Vec

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.IntVector

open Spec.GaloisField

module Scalar = Spec.GF128

type gf128_spec =
  | NI

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let _: squash (inversion gf128_spec) = allow_inversion gf128_spec

let elem = Scalar.elem_le
let gf128 = Scalar.gf128_le

let elem2 = lseq elem 2

let elem4 = lseq elem 4
let fadd4 (a:elem4) (b:elem4) : elem4 = map2 fadd a b
let fmul4 (a:elem4) (b:elem4) : elem4 = map2 (fun x y -> reverse (fmul (reverse x) (reverse y))) a b

let load_elem4 (b:lbytes 64) : elem4 =
  let b1 = load_felem_be #gf128 (sub b 0 16) in
  let b2 = load_felem_be #gf128 (sub b 16 16) in
  let b3 = load_felem_be #gf128 (sub b 32 16) in
  let b4 = load_felem_be #gf128 (sub b 48 16) in
  create4 b1 b2 b3 b4

let encode4 (w:lbytes 64) : Tot elem4 = load_elem4 w

let load_acc (text:lbytes 64) (acc:elem): elem4 =
  fadd4 (create4 acc zero zero zero) (encode4 text)

let normalize4 (pre:elem4) (acc:elem4) : elem =
  let a = fmul4 acc pre in
  fadd (fadd (fadd a.[0] a.[1]) a.[2]) a.[3]

let load_precompute_r (r:elem) : elem4 =
  let r2 = reverse (reverse r `fmul` reverse r) in
  let r3 = reverse (reverse r `fmul` reverse r2) in
  let r4 =reverse (reverse r `fmul` reverse r3) in
  create4 r4 r3 r2 r

let gf128_update4_add_mul (pre:elem4) (b:lbytes 64) (acc:elem) : Tot elem =
  let acc = load_acc b acc in
  normalize4 pre acc

let gf128_update_multi_add_mul (text:bytes{0 < length text /\ length text % 64 = 0}) (acc:elem) (r:elem) : elem =
  let pre = load_precompute_r r in
  repeat_blocks_multi #uint8 #elem 64 text (gf128_update4_add_mul pre) acc

let gf128_update_multi (text:bytes{0 < length text /\ length text % 64 = 0}) (acc:elem) (r:elem) : elem =
  gf128_update_multi_add_mul text acc r

let gf128_update_vec (text:bytes) (acc:elem) (r:elem) : Tot elem =
  let len = length text in
  let len0 = len / 64 * 64 in
  let t0 = Seq.slice text 0 len0 in
  let acc = if len0 > 0 then gf128_update_multi t0 acc r else acc in

  let t1 = Seq.slice text len0 len in
  Scalar.gf128_update t1 acc r
