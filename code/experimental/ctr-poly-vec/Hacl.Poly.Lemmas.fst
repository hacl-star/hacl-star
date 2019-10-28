module Hacl.Poly.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

open Hacl.Poly

module Loops = Lib.LoopCombinators


#set-options "--z3rlimit 50 --max_fuel 1 --max_ifuel 0"

val pow_w_eval_1: r:felem -> Lemma (pow_w 1 r == r)
let pow_w_eval_1 r = ()

val pow_w_unfold: w:pos{w > 1} -> r:felem -> Lemma (pow_w w r == r *% pow_w (w - 1) r)
let pow_w_unfold w r = ()


#set-options "--max_fuel 0"

val fsum_eval_1: x:felem_v 1 -> Lemma (fsum #1 x == x.[0])
let fsum_eval_1 x =
  let r = fsum #1 x in
  Loops.unfold_repeati 1 (fsum_f x) zero 0;
  Loops.eq_repeati0 1 (fsum_f x) zero;
  assert (r == fadd zero x.[0]);
  fadd_identity x.[0]


val repeat_blocks_multi_eval_1: b:block_v 1 -> acc0:felem -> r:felem -> Lemma
  (FStar.Math.Lemmas.cancel_mul_mod 1 blocksize;
   repeat_blocks_multi blocksize b (poly_update1 r) acc0 == poly_update1 r b acc0)

let repeat_blocks_multi_eval_1 b acc0 r =
  FStar.Math.Lemmas.cancel_mul_mod 1 blocksize;
  //let lp = repeat_blocks_multi blocksize b (poly_update1 r) acc0 in
  lemma_repeat_blocks_multi blocksize b (poly_update1 r) acc0;
  let repeat_bf = repeat_blocks_f blocksize b (poly_update1 r) 1 in
  //assert (lp == Loops.repeati 1 repeat_bf acc0);
  Loops.unfold_repeati 1 repeat_bf acc0 0;
  Loops.eq_repeati0 1 repeat_bf acc0

val load_acc_v_i: #w:lanes -> b:block_v w -> acc0:felem -> i:pos{i < w} -> Lemma
  (Math.Lemmas.lemma_mult_le_right blocksize i (w - 1);
   (load_acc_v b acc0).[i] == encode (sub b (i * blocksize) blocksize))

let load_acc_v_i #w b acc0 i =
  Math.Lemmas.lemma_mult_le_right blocksize i (w - 1);
  let b2 = sub b (i * blocksize) blocksize in
  assert ((load_acc_v b acc0).[i] == fadd zero (encode b2));
  fadd_identity (encode b2)

val rw_eq: #w:lanes{w > 1} -> r:felem -> i:pos{i < w} -> Lemma
  (let rw = createi w (rw_f #w r) in
   let rw1: lseq felem (w - 1) = createi (w - 1) (rw_f #(w-1) r) in
   rw.[i - 1] == fmul rw1.[i - 1] r)

let rw_eq #w r i =
  calc (==) {
    pow_w (w - i + 1) r;
    (==) { pow_w_unfold (w - i + 1) r }
    r *% pow_w (w - i) r;
    (==) { fmul_commutativity r (pow_w (w - i) r) }
    pow_w (w - i) r *% r;
  }


val fsum_unfold_step:
    #w:lanes{w > 1}
  -> acc_v0:felem_v w
  -> r:felem
  -> i:pos{i < w}
  -> rp_l1:felem -> Lemma
  (let rw = createi w (rw_f #w r) in
   let rw1 = createi (w - 1) (rw_f #(w-1) r) in

   rp_l1 *% r +% acc_v0.[i - 1] *% rw.[i - 1] ==
   (rp_l1 +% (sub acc_v0 0 (w - 1)).[i - 1] *% rw1.[i - 1]) *% r)

let fsum_unfold_step #w acc_v0 r i rp_l1 =
  let rw = createi w (rw_f #w r) in
  let rw1 = createi (w - 1) (rw_f #(w-1) r) in
  let acc_v1 = sub acc_v0 0 (w - 1) in

  calc (==) {
    rp_l1 *% r +% acc_v0.[i - 1] *% rw.[i - 1];
    (==) { rw_eq #w r i }
    rp_l1 *% r +% acc_v0.[i - 1] *% (rw1.[i - 1] *% r);
    (==) { fmul_associativity acc_v0.[i - 1] rw1.[i - 1] r }
    rp_l1 *% r +% acc_v0.[i - 1] *% rw1.[i - 1] *% r;
    (==) { fmul_add_distr_l rp_l1 (acc_v0.[i - 1] *% rw1.[i - 1]) r }
    (rp_l1 +% acc_v0.[i - 1] *% rw1.[i - 1]) *% r;
    (==) { }
    (rp_l1 +% acc_v1.[i - 1] *% rw1.[i - 1]) *% r;
  }


val fsum_unfold: #w:lanes{w > 1} -> acc_v0:felem_v w -> r:felem -> i:nat{i < w} -> Lemma
  (let rw = createi w (rw_f #w r) in
   let rw1 = createi (w - 1) (rw_f #(w-1) r) in

   Loops.repeati i (fsum_f (fmul_v acc_v0 rw)) zero ==
   fmul (Loops.repeati i (fsum_f (fmul_v (sub acc_v0 0 (w - 1)) rw1)) zero) r)

let rec fsum_unfold #w acc_v0 r i =
  let rw = createi w (rw_f #w r) in
  let rw1 = createi (w - 1) (rw_f #(w-1) r) in
  let acc_v1 = sub acc_v0 0 (w - 1) in
  if i = 0 then begin
    Loops.eq_repeati0 i (fsum_f (fmul_v acc_v0 rw)) zero;
    Loops.eq_repeati0 i (fsum_f (fmul_v acc_v1 rw1)) zero;
    fmul_zero_l r;
    () end
  else begin
    let lp1 = Loops.repeati (i - 1) (fsum_f (fmul_v acc_v0 rw)) zero in
    let rp_l1 = Loops.repeati (i - 1) (fsum_f (fmul_v acc_v1 rw1)) zero in
    fsum_unfold #w acc_v0 r (i - 1);
    assert (lp1 == rp_l1 *% r);
    let lp = Loops.repeati i (fsum_f (fmul_v acc_v0 rw)) zero in
    let rp_l = Loops.repeati i (fsum_f (fmul_v acc_v1 rw1)) zero in
    Loops.unfold_repeati i (fsum_f (fmul_v acc_v0 rw)) zero (i - 1);
    Loops.unfold_repeati i (fsum_f (fmul_v acc_v1 rw1)) zero (i - 1);
    assert (lp == fadd lp1 (fmul acc_v0.[i - 1] rw.[i - 1]));
    assert (rp_l == fadd rp_l1 (fmul acc_v1.[i - 1] rw1.[i - 1]));
    fsum_unfold_step #w acc_v0 r i rp_l1;
    assert (lp == rp_l *% r) end


val normalize_unfold: #w:lanes{w > 1} -> acc_v0:felem_v w -> r:felem -> Lemma
  (normalize_v r acc_v0 == fadd (fmul (normalize_v r (sub acc_v0 0 (w - 1))) r) (fmul acc_v0.[w - 1] r))

let normalize_unfold #w acc_v0 r =
  let acc_v1 = sub acc_v0 0 (w - 1) in
  let rw = createi w (rw_f #w r) in
  let rw1 = createi (w - 1) (rw_f #(w-1) r) in
  calc (==) {
    normalize_v r acc_v0;
    (==) { }
    Loops.repeati w (fsum_f (fmul_v acc_v0 rw)) zero;
    (==) { Loops.unfold_repeati w (fsum_f (fmul_v acc_v0 rw)) zero (w - 1) }
    fsum_f (fmul_v acc_v0 rw) (w - 1) (Loops.repeati (w - 1) (fsum_f (fmul_v acc_v0 rw)) zero);
    (==) { fsum_unfold #w acc_v0 r (w - 1) }
    fsum_f (fmul_v acc_v0 rw) (w - 1) (fmul (Loops.repeati (w - 1) (fsum_f (fmul_v acc_v1 rw1)) zero) r);
    (==) { }
    fsum_f (fmul_v acc_v0 rw) (w - 1) (fmul (normalize_v r acc_v1) r);
    (==) { }
    fadd (fmul (normalize_v r acc_v1) r) (fmul_v acc_v0 rw).[w - 1];
    (==) { pow_w_eval_1 r }
    fadd (fmul (normalize_v r acc_v1) r) (fmul acc_v0.[w - 1] r);
  }


val repeat_blocks_multi_unfold_eq: #w:lanes{w > 1} -> b:block_v w -> acc0:felem -> r:felem -> Lemma
  (let b1 = sub b 0 ((w - 1) * blocksize) in
   Math.Lemmas.cancel_mul_div w blocksize;
   Math.Lemmas.cancel_mul_div (w - 1) blocksize;
   let repeat_bf_b = repeat_blocks_f blocksize b (poly_update1 r) w in
   let repeat_bf_b1 = repeat_blocks_f blocksize b1 (poly_update1 r) (w - 1) in
   Loops.repeati (w - 1) repeat_bf_b acc0 == Loops.repeati (w - 1) repeat_bf_b1 acc0)

let repeat_blocks_multi_unfold_eq #w b acc0 r =
  let b1 = sub b 0 ((w - 1) * blocksize) in
  Math.Lemmas.cancel_mul_div w blocksize;
  Math.Lemmas.cancel_mul_div (w - 1) blocksize;

  let repeat_bf_b = repeat_blocks_f blocksize b (poly_update1 r) w in
  let repeat_bf_b1 = repeat_blocks_f blocksize b1 (poly_update1 r) (w - 1) in

  let lemma_aux (i:nat{i < w - 1}) (acc:felem) : Lemma (repeat_bf_b1 i acc == repeat_bf_b i acc) =
    Math.Lemmas.lemma_mult_le_right blocksize (i + 1) (w - 1);
    let b3 = sub b1 (i * blocksize) blocksize in
    FStar.Seq.slice_slice b 0 ((w - 1) * blocksize) (i * blocksize) ((i + 1) * blocksize);
    let b4 = sub b (i * blocksize) blocksize in
    assert (repeat_bf_b1 i acc == poly_update1 r b3 acc);
    assert (repeat_bf_b i acc == poly_update1 r b4 acc);
    () in
  Classical.forall_intro_2 lemma_aux;
  Lib.Sequence.Lemmas.repeati_extensionality (w - 1) repeat_bf_b repeat_bf_b1 acc0


val repeat_blocks_multi_unfold: #w:lanes{w > 1} -> b:block_v w -> acc0:felem -> r:felem -> Lemma
  (let b1 = sub b 0 ((w - 1) * blocksize) in
   let b2 = sub b ((w - 1) * blocksize) blocksize in
   Math.Lemmas.cancel_mul_mod w blocksize;
   Math.Lemmas.cancel_mul_mod (w - 1) blocksize;
   repeat_blocks_multi blocksize b (poly_update1 r) acc0 ==
   poly_update1 r b2 (repeat_blocks_multi blocksize b1 (poly_update1 r) acc0))

let repeat_blocks_multi_unfold #w b acc0 r =
  let b1 = sub b 0 ((w - 1) * blocksize) in
  let b2 = sub b ((w - 1) * blocksize) blocksize in
  Math.Lemmas.cancel_mul_mod w blocksize;
  Math.Lemmas.cancel_mul_div w blocksize;
  Math.Lemmas.cancel_mul_mod (w - 1) blocksize;
  Math.Lemmas.cancel_mul_div (w - 1) blocksize;

  let repeat_bf_b = repeat_blocks_f blocksize b (poly_update1 r) w in
  let repeat_bf_b1 = repeat_blocks_f blocksize b1 (poly_update1 r) (w - 1) in
  calc (==) {
    repeat_blocks_multi blocksize b (poly_update1 r) acc0;
    (==) { lemma_repeat_blocks_multi blocksize b (poly_update1 r) acc0 }
    Loops.repeati w repeat_bf_b acc0;
    (==) { Loops.unfold_repeati w repeat_bf_b acc0 (w - 1) }
    repeat_bf_b (w - 1) (Loops.repeati (w - 1) repeat_bf_b acc0);
    (==) { }
    poly_update1 r b2 (Loops.repeati (w - 1) repeat_bf_b acc0);
    (==) { repeat_blocks_multi_unfold_eq b acc0 r }
    poly_update1 r b2 (Loops.repeati (w - 1) repeat_bf_b1 acc0);
    (==) { Math.Lemmas.cancel_mul_mod (w - 1) blocksize;
           lemma_repeat_blocks_multi blocksize b1 (poly_update1 r) acc0 }
    poly_update1 r b2 (repeat_blocks_multi blocksize b1 (poly_update1 r) acc0);
  }


val load_acc_v_sub: #w:lanes{w > 1} -> b:block_v w -> acc0:felem -> r:felem -> Lemma
  (load_acc_v #(w - 1) (sub b 0 ((w - 1) * blocksize)) acc0 == sub (load_acc_v #w b acc0) 0 (w - 1))
let load_acc_v_sub #w b acc0 r =
  let bs = sub b 0 ((w - 1) * blocksize) in
  let b1 = load_acc_v #(w - 1) bs acc0 in
  let b2 = sub (load_acc_v #w b acc0) 0 (w - 1) in
  let lemma_aux (i:nat{i < w - 1}) : Lemma (b1.[i] == b2.[i]) =
    Seq.slice_slice b 0 ((w - 1) * blocksize) (i * blocksize) ((i + 1) * blocksize) in
  Classical.forall_intro lemma_aux;
  eq_intro b1 b2


// val load_acc_v_lemma: #w:lanes -> b:block_v w -> acc0:felem -> r:felem -> Lemma
//   (FStar.Math.Lemmas.cancel_mul_mod w blocksize;
//    normalize_v r (load_acc_v b acc0) == repeat_blocks_multi blocksize b (poly_update1 r) acc0)

let rec load_acc_v_lemma #w b acc0 r =
  let acc_v0 = load_acc_v b acc0 in
  let lp = normalize_v r acc_v0 in
  Math.Lemmas.cancel_mul_mod w blocksize;
  let rp = repeat_blocks_multi blocksize b (poly_update1 r) acc0 in

  if w = 1 then begin
    let rw = createi w (rw_f #w r) in
    pow_w_eval_1 r;
    let acc_rw = fmul_v acc_v0 rw in
    fsum_eval_1 acc_rw;
    //assert (lp == fmul (fadd acc0 (encode b)) rw.[0]);

    repeat_blocks_multi_eval_1 b acc0 r;
    //assert (rp == fmul (fadd (encode b) acc0) r);
    fadd_commutativity (encode b) acc0;
    () end
  else begin
    let b1 = sub b 0 ((w - 1) * blocksize) in
    let b2 = sub b ((w - 1) * blocksize) blocksize in
    load_acc_v_lemma #(w - 1) b1 acc0 r;
    Math.Lemmas.cancel_mul_mod (w - 1) blocksize;
    let lp1 = normalize_v r (load_acc_v b1 acc0) in
    let rp1 = repeat_blocks_multi blocksize b1 (poly_update1 r) acc0 in
    assert (lp1 == rp1);
    repeat_blocks_multi_unfold #w b acc0 r;
    assert (rp == fmul (fadd (encode b2) lp1) r);
    calc (==) {
      normalize_v r acc_v0;
      (==) { normalize_unfold #w acc_v0 r; load_acc_v_sub #w b acc0 r }
      fadd (fmul lp1 r) (fmul acc_v0.[w - 1] r);
      (==) { load_acc_v_i #w b acc0 (w - 1) }
      lp1 *% r +% encode b2 *% r;
      (==) { fmul_add_distr_l lp1 (encode b2) r }
      (lp1 +% encode b2) *% r;
      (==) { fadd_commutativity lp1 (encode b2) }
      (encode b2 +% lp1) *% r;
    }; () end


// val poly_update_nblocks_lemma: #w:lanes -> r:felem -> b:block_v w -> acc_v0:felem_v w -> Lemma
//   (let pre = create w (pow_w w r) in
//   FStar.Math.Lemmas.cancel_mul_mod w blocksize;
//   normalize_v r (poly_update_nblocks #w pre b acc_v0) == repeat_blocks_multi blocksize b (poly_update1 r) (normalize_v r acc_v0))


let rec poly_update_nblocks_lemma #w r b acc_v0 =
  let pre = create w (pow_w w r) in
  let acc_v = poly_update_nblocks #w pre b acc_v0 in
  let lp = normalize_v r acc_v in
  Math.Lemmas.cancel_mul_mod w blocksize;
  let rp = repeat_blocks_multi blocksize b (poly_update1 r) (normalize_v r acc_v0) in
  if w = 1 then begin
    repeat_blocks_multi_eval_1 b (normalize_v r acc_v0) r;
    let rw = createi w (rw_f #w r) in
    let acc_rw0 = fmul_v acc_v0 rw in
    fsum_eval_1 acc_rw0;
    pow_w_eval_1 r;
    assert (rp == (encode b +% acc_v0.[0] *% r) *% r);

    let acc_rw = fmul_v acc_v rw in
    fsum_eval_1 acc_rw;
    assert (lp == (acc_v0.[0] *% r +% encode b) *% r);
    fadd_commutativity (acc_v0.[0] *% r) (encode b);
    () end
  else begin
    let b1 = sub b 0 ((w - 1) * blocksize) in
    let b2 = sub b ((w - 1) * blocksize) blocksize in
    Math.Lemmas.cancel_mul_mod (w - 1) blocksize;
    let pre1 = create (w - 1) (pow_w (w - 1) r) in
    let acc_v1 = sub acc_v0 0 (w - 1) in

    poly_update_nblocks_lemma #(w - 1) r b1 acc_v1;
    assert (
      normalize_v r (poly_update_nblocks #(w - 1) pre1 b1 acc_v1) ==
      repeat_blocks_multi blocksize b1 (poly_update1 r) (normalize_v r acc_v1));

    calc (==) {
      normalize_v r acc_v;
      (==) { normalize_unfold acc_v r }
      normalize_v r (sub acc_v 0 (w - 1)) *% r +% (acc_v0.[w - 1] *% pow_w w r +% encode b2) *% r;
    };

    admit() end
