module Hacl.Poly

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence


#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

///
///  Local definition of the repeat_blocks function
///


let repeat_blocks (#a:Type0) (#b:Type0) (#c:Type0)
  (blocksize:size_pos)
  (inp:seq a)
  (f:(lseq a blocksize -> b -> b))
  (g:(len:size_nat{len == length inp % blocksize} -> s:lseq a len -> b -> c))
  (init:b) : c
 =
   let len = length inp in
   let nb = len / blocksize in
   let rem = len % blocksize in
   let acc = Lib.LoopCombinators.repeati nb (repeat_blocks_f blocksize inp f nb) init in
   let last = Seq.slice inp (nb * blocksize) len in
   let acc = g rem last acc in
   acc


///
///  Poly semiring
///

val felem : Type
val zero : felem
val one :  felem

val fadd: felem -> felem -> felem
val fmul: felem -> felem -> felem

let ( +% ) (a b:felem) : felem = fadd a b
let ( *% ) (a b:felem) : felem = fmul a b



val blocksize:size_pos
let block = lseq uint8 blocksize

val encode: b:block -> felem
val encode_last: len:nat{len < blocksize} -> b:lbytes len -> felem

///
///  Poly evaluation function
///

let poly_update1 (r:felem) (b:block) (acc:felem) : felem =
  (encode b +% acc) *% r

let poly_update_last (r:felem) (len:nat{len < blocksize}) (b:lbytes len) (acc:felem) : felem =
  if len = 0 then acc else (encode_last len b +% acc) *% r

let poly_update (text:bytes) (acc:felem) (r:felem) : felem =
  repeat_blocks #uint8 #felem blocksize text
    (poly_update1 r)
    (poly_update_last r)
  acc


///
///  PolyxN
///

let lanes = w:size_pos{w * blocksize <= max_size_t}

type felem_v (w:lanes) = lseq felem w

let fadd_v (#w:lanes) (x:felem_v w) (y:felem_v w) : felem_v w = map2 fadd x y
let fmul_v (#w:lanes) (x:felem_v w) (y:felem_v w) : felem_v w = map2 fmul x y

val load_acc_v: #w:lanes -> b:lbytes (w * blocksize) -> acc:felem -> felem_v w
val normalize_v: #w:lanes -> r:felem -> acc:felem_v w -> felem

let lemma_mul_lt (w:pos) (i:nat{i < w}) (bs:pos) : Lemma ((i + 1) * bs <= w * bs) = ()

let encode_v (#w:lanes) (b:lbytes (w * blocksize)) : felem_v w =
  createi w (fun i ->
    lemma_mul_lt w i blocksize;
    let b_i = sub b (i * blocksize) blocksize in
    encode b_i)

let rec pow_w (w:pos) (r:felem) : felem =
  if w = 1 then r else  r *% pow_w (w - 1) r

let poly_update_nblocks (#w:lanes) (pre:felem_v w) (b:lbytes (w * blocksize)) (acc:felem_v w) : felem_v w =
  fadd_v (fmul_v acc pre) (encode_v b)

let poly_update_last_v (#w:lanes) (r:felem) (len:nat{len < w * blocksize}) (b:lbytes len) (acc_v:felem_v w) : felem =
  let acc = normalize_v r acc_v in
  poly_update b acc r

let poly_update_v (#w:lanes) (text:bytes{w * blocksize <= length text}) (acc:felem) (r:felem) : felem =
  let len = length text in
  let blocksize_v = w * blocksize in
  let text0 = Seq.slice text 0 blocksize_v in
  let acc_v = load_acc_v #w text0 acc in

  let pre = create w (pow_w w r) in
  let text1 = Seq.slice text blocksize_v len in
  repeat_blocks blocksize_v text1
    (poly_update_nblocks #w pre)
    (poly_update_last_v #w r)
  acc_v


///
///  Poly evaluation properties
///

val load_acc_v_lemma: #w:lanes -> b:lbytes (w * blocksize) -> acc0:felem -> r:felem -> Lemma
  (FStar.Math.Lemmas.cancel_mul_mod w blocksize;
   normalize_v r (load_acc_v b acc0) == repeat_blocks_multi blocksize b (poly_update1 r) acc0)


val poly_update_nblocks_lemma: #w:lanes -> r:felem -> b:lbytes (w * blocksize) -> acc_v0:felem_v w -> Lemma
  (let pre = create w (pow_w w r) in
  FStar.Math.Lemmas.cancel_mul_mod w blocksize;
  normalize_v r (poly_update_nblocks #w pre b acc_v0) == repeat_blocks_multi blocksize b (poly_update1 r) (normalize_v r acc_v0))
