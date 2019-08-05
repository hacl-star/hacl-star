module Hacl.Spec.GF128.Equiv

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.IntVector

open Spec.GaloisField

module Loops = Lib.LoopCombinators
module PLoops = Lib.Loops.Lemmas
module S = Spec.GF128

include Hacl.Spec.GF128.Vec

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"


val gf128_update_multi_add_mul_lemma_aux:
    b0:elem -> b1:elem -> b2:elem -> b3:elem
  -> r:elem -> r2:elem{r2 == fmul_be r r} -> r3:elem{r3 == fmul_be r r2} -> r4:elem{r4 == fmul_be r r3} ->
  Lemma
  (fmul_be b0 r4 `fadd` fmul_be b1 r3 `fadd` fmul_be b2 r2 `fadd` fmul_be b3 r ==
    fmul_be (fadd (fmul_be (fadd (fmul_be (fadd (fmul_be b0 r) b1) r) b2) r) b3) r)

let gf128_update_multi_add_mul_lemma_aux b0 b1 b2 b3 r r2 r3 r4 = admit()

val gf128_add_zero: f:elem -> Lemma (fadd zero f == f)
let gf128_add_zero f = admit()

val gf128_add_commutativity: a:elem -> b:elem -> Lemma (fadd a b == fadd b a)
let gf128_add_commutativity a b = admit()


val gf128_update4_add_mul_lemma:
    pre:elem4
  -> b:lbytes 64
  -> acc:elem ->
  Lemma
   (let b0 = S.encode (Seq.slice b 0 16) in
    let b1 = S.encode (Seq.slice b 16 32) in
    let b2 = S.encode (Seq.slice b 32 48) in
    let b3 = S.encode (Seq.slice b 48 64) in

    gf128_update4_add_mul pre b acc ==
    fmul_be (b0 `fadd` acc) pre.[0] `fadd` fmul_be b1 pre.[1] `fadd` fmul_be b2 pre.[2] `fadd` fmul_be b3 pre.[3])

let gf128_update4_add_mul_lemma pre b acc =
  let acc1 = load_acc b acc in
  let b0 = S.encode (Seq.slice b 0 16) in
  let b1 = S.encode (Seq.slice b 16 32) in
  let b2 = S.encode (Seq.slice b 32 48) in
  let b3 = S.encode (Seq.slice b 48 64) in
  assert (acc1.[0] == fadd acc b0);
  gf128_add_zero b1;
  gf128_add_zero b2;
  gf128_add_zero b3;
  gf128_add_commutativity acc b0


val gf128_update_multi_add_mul_lemma_loop:
    r:elem
  -> text:bytes{64 <= length text /\ length text % 64 = 0}
  -> acc0:elem
  -> i:nat{i < length text / 64}
  -> acc:elem ->
  Lemma
  (let pre = load_precompute_r r in
   let len = length text in

   let f = S.gf128_update1 r in
   let f_vec = gf128_update4_add_mul pre in
   let repeat_bf_sc = repeat_blocks_f 16 text f (len / 16) in
   let repeat_bf_vec = repeat_blocks_f 64 text f_vec (len / 64) in

   repeat_bf_vec i acc == PLoops.repeat_w 4 (len / 64) repeat_bf_sc i acc)

let gf128_update_multi_add_mul_lemma_loop r text acc0 i acc =
  let pre = load_precompute_r r in
  let len = length text in

  let f = S.gf128_update1 r in
  let f_vec = gf128_update4_add_mul pre in
  let repeat_bf_sc = repeat_blocks_f 16 text f (len / 16) in
  let repeat_bf_vec = repeat_blocks_f 64 text f_vec (len / 64) in

  let acc1 = repeat_bf_vec i acc in
  let b = Seq.slice text (i * 64) (i * 64 + 64) in
  assert (acc1 == gf128_update4_add_mul pre b acc);
  assert (acc1 == normalize4 pre (load_acc b acc));
  let b0 = S.encode (Seq.slice text (i * 64) (i * 64 + 16)) in
  let b1 = S.encode (Seq.slice text (i * 64 + 16) (i * 64 + 32)) in
  let b2 = S.encode (Seq.slice text (i * 64 + 32) (i * 64 + 48)) in
  let b3 = S.encode (Seq.slice text (i * 64 + 48) (i * 64 + 64)) in

  gf128_update4_add_mul_lemma pre b acc;
  assert (acc1 == fmul_be (fadd b0 acc) pre.[0] `fadd` fmul_be b1 pre.[1] `fadd` fmul_be b2 pre.[2] `fadd` fmul_be b3 pre.[3]);
  let acc2 = repeat_bf_sc (4*i+3) (repeat_bf_sc (4*i+2) (repeat_bf_sc (4*i+1) (repeat_bf_sc (4*i) acc))) in
  assert (acc2 == fmul_be (fadd (fmul_be (fadd (fmul_be (fadd (fmul_be (fadd acc b0) r) b1) r) b2) r) b3) r);
  gf128_update_multi_add_mul_lemma_aux (fadd acc b0) b1 b2 b3 pre.[3] pre.[2] pre.[1] pre.[0];
  gf128_add_commutativity b0 acc;
  assert (acc2 == acc1)


val gf128_update_multi_add_mul_lemma:
    text:bytes{64 <= length text /\ length text % 64 = 0}
  -> acc0:elem
  -> r:elem ->
    Lemma
    (gf128_update_multi_add_mul text acc0 r ==
      repeat_blocks_multi #uint8 #elem 16 text (S.gf128_update1 r) acc0)

let gf128_update_multi_add_mul_lemma text acc0 r =
  let pre = load_precompute_r r in
  let len = length text in

  let f = S.gf128_update1 r in
  let f_vec = gf128_update4_add_mul pre in
  let repeat_bf_sc = repeat_blocks_f 16 text f (len / 16) in
  let repeat_bf_vec = repeat_blocks_f 64 text f_vec (len / 64) in

  let acc1 = repeat_blocks_multi #uint8 #elem 64 text f_vec acc0 in
  lemma_repeat_blocks_multi #uint8 #elem 64 text f_vec acc0;
  assert (acc1 == Loops.repeati (len / 64) repeat_bf_vec acc0);

  FStar.Classical.forall_intro_2 (gf128_update_multi_add_mul_lemma_loop r text acc0);
  PLoops.lemma_repeati_vec #elem #elem 4 (len / 64) (fun x -> x) repeat_bf_sc repeat_bf_vec acc0;
  assert (acc1 == Loops.repeati (len / 16) repeat_bf_sc acc0);
  lemma_repeat_blocks_multi #uint8 #elem 16 text (S.gf128_update1 r) acc0


val gf128_update_multi_mul_add_lemma_load_acc:
    r:elem
  -> text:bytes{64 <= length text /\ length text % 64 = 0}
  -> acc0:elem ->
    Lemma
    (let t0 = Seq.slice text 0 64 in
     let pre = load_precompute_r r in
     let f = S.gf128_update1 r in
     let repeat_bf_t0 = repeat_blocks_f 16 t0 f 4 in
     normalize4 pre (load_acc t0 acc0) == PLoops.repeat_w #elem 4 1 repeat_bf_t0 0 acc0)

let gf128_update_multi_mul_add_lemma_load_acc r text acc0 = admit()


val gf128_update_multi_mul_add_lemma_loop:
    r:elem
  -> text:bytes{64 <= length text /\ length text % 64 = 0}
  -> i:nat{i < (length text - 64) / 64}
  -> acc_vec:elem4 ->
    Lemma
    (let pre = load_precompute_r r in
     let len = length text in
     let len1 = len - 64 in

     let nb_vec = len1 / 64 in
     let nb = len1 / 16 in
     assert (nb == 4 * nb_vec);

     let t1 = Seq.slice text 64 len in
     let f = S.gf128_update1 r in
     let f_vec = gf128_update4_mul_add pre in

     let repeat_bf_vec = repeat_blocks_f 64 t1 f_vec nb_vec in
     let repeat_bf_t1 = repeat_blocks_f 16 t1 f nb in

     normalize4 pre (repeat_bf_vec i acc_vec) ==
       PLoops.repeat_w #elem 4 nb_vec repeat_bf_t1 i (normalize4 pre acc_vec))

let gf128_update_multi_mul_add_lemma_loop r text i acc_vec = admit()


val gf128_update_multi_mul_add_lemma:
    text:bytes{64 <= length text /\ length text % 64 = 0}
  -> acc0:elem
  -> r:elem ->
    Lemma
    (gf128_update_multi_mul_add text acc0 r ==
      repeat_blocks_multi #uint8 #elem 16 text (S.gf128_update1 r) acc0)

let gf128_update_multi_mul_add_lemma text acc0 r =
  let pre = load_precompute_r r in

  let len = length text in
  let t0 = Seq.slice text 0 64 in
  let t1 = Seq.slice text 64 len in

  let f = S.gf128_update1 r in
  let f_vec = gf128_update4_mul_add pre in

  let acc1 = load_acc t0 acc0 in
  let acc2 = repeat_blocks_multi #uint8 #elem4 64 t1 f_vec acc1 in
  let acc3 = normalize4 pre acc2 in
  assert (acc3 == gf128_update_multi_mul_add text acc0 r);

  let len1 = len - 64 in
  let nb_vec = len1 / 64 in
  let nb = len1 / 16 in
  assert (nb == 4 * nb_vec);

  let repeat_bf_vec = repeat_blocks_f 64 t1 f_vec nb_vec in
  let repeat_bf_t0 = repeat_blocks_f 16 t0 f 4 in
  let repeat_bf_t1 = repeat_blocks_f 16 t1 f nb in

  gf128_update_multi_mul_add_lemma_load_acc r text acc0;
  //assert (normalize4 pre (load_acc t0 acc0) == PLoops.repeat_w #elem 4 1 repeat_bf_t0 0 acc0);
  FStar.Classical.forall_intro_2 (gf128_update_multi_mul_add_lemma_loop r text);
  //assert (forall (i:nat{i < nb_vec}) (acc_vec:elem4).
    //normalize4 pre (repeat_bf_vec i acc_vec) == PLoops.repeat_w #elem 4 nb_vec repeat_bf_t1 i (normalize4 pre acc_vec));

  PLoops.lemma_repeat_blocks_multi_vec #uint8 #elem #elem4
    4 16 text f f_vec (normalize4 pre) load_acc acc0

#push-options "--max_ifuel 1"
val gf128_update_multi_lemma:
    alg:gf128_spec
  -> text:bytes{64 <= length text /\ length text % 64 = 0}
  -> acc0:elem
  -> r:elem ->
    Lemma
    (gf128_update_multi alg text acc0 r ==
      repeat_blocks_multi #uint8 #elem 16 text (S.gf128_update1 r) acc0)

let gf128_update_multi_lemma alg text acc0 r =
  match alg with
  | NI -> gf128_update_multi_add_mul_lemma text acc0 r
  | PreComp -> gf128_update_multi_mul_add_lemma text acc0 r
#pop-options


val gf128_update_vec_eq_lemma:
    alg:gf128_spec
  -> text:bytes
  -> acc0:elem
  -> r:elem ->
  Lemma (gf128_update_vec alg text acc0 r == S.gf128_update text acc0 r)

let gf128_update_vec_eq_lemma alg text acc0 r =
  let len = length text in
  let len0 = len / 64 * 64 in

  assert (len0 % 64 = 0);
  assert (len0 % 16 = 0);
  let t0 = Seq.slice text 0 len0 in
  let f = S.gf128_update1 r in
  let l = S.gf128_update_last r in

  if len0 > 0 then begin
    gf128_update_multi_lemma alg t0 acc0 r;
    PLoops.repeat_blocks_split #uint8 #elem 16 len0 text f l acc0 end
  else ()
