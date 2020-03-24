module Hacl.Poly.Lemmas

open FStar.Mul
open Lib.Sequence
open Hacl.Poly

module Loops = Lib.LoopCombinators
module Lemmas = Lib.Sequence.Lemmas


#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

val fmul_add_distr_r: a:felem -> b:felem -> c:felem -> Lemma
  (a *% c +% b *% c == (a +% b) *% c)
let fmul_add_distr_r a b c =
  calc (==) {
    (a +% b) *% c;
    (==) { fmul_commutativity (a +% b) c }
    c *% (a +% b);
    (==) { fmul_add_distr_l c a b }
    c *% a +% c *% b;
    (==) { fmul_commutativity c a; fmul_commutativity c b }
    a *% c +% b *% c;
  }

///
///  If (felem, +%, *%) is a semiring then (felem_v, fadd_v, fmul_v) is a semiring as well
///

val fmul_add_distr_r_v: #w:lanes -> a:felem_v w -> b:felem_v w -> c:felem_v w ->
  Lemma (fmul_v (fadd_v a b) c == fadd_v (fmul_v a c) (fmul_v b c))
let fmul_add_distr_r_v #w a b c =
  let aux (i:nat{i < w}) : Lemma ((fmul_v (fadd_v a b) c).[i] == (fadd_v (fmul_v a c) (fmul_v b c)).[i]) =
    fmul_add_distr_r a.[i] b.[i] c.[i] in
  Classical.forall_intro aux;
  eq_intro (fmul_v (fadd_v a b) c) (fadd_v (fmul_v a c) (fmul_v b c))


val fmul_associativity_v: #w:lanes -> a:felem_v w -> b:felem_v w -> c:felem_v w ->
  Lemma (fmul_v (fmul_v a b) c == fmul_v a (fmul_v b c))
let fmul_associativity_v #w a b c =
  let aux (i:nat{i < w}) : Lemma ((fmul_v (fmul_v a b) c).[i] == (fmul_v a (fmul_v b c)).[i]) =
    fmul_associativity a.[i] b.[i] c.[i] in
  Classical.forall_intro aux;
  eq_intro (fmul_v (fmul_v a b) c) (fmul_v a (fmul_v b c))


val fmul_commutativity_v: #w:lanes -> a:felem_v w -> b:felem_v w ->
  Lemma (fmul_v a b == fmul_v b a)
let fmul_commutativity_v #w a b =
  let aux (i:nat{i < w}) : Lemma ((fmul_v a b).[i] == (fmul_v b a).[i]) =
    fmul_commutativity a.[i] b.[i] in
  Classical.forall_intro aux;
  eq_intro (fmul_v a b) (fmul_v b a)

///
///  Lemma
///   (fsum (fadd_v x y) == fsum x +% fsum y /\
///    fsum (fmul_v x (create w y)) == fsum x *% y)
///

val fsum_add_i_step: a:felem -> b:felem -> c:felem -> d:felem -> Lemma
  ((a +% b) +% (c +% d) == (a +% c) +% (b +% d))
let fsum_add_i_step a b c d =
  calc (==) {
    (a +% b) +% (c +% d);
    (==) { fadd_associativity (a +% b) c d }
    ((a +% b) +% c) +% d;
    (==) { fadd_associativity a b c; fadd_commutativity b c; fadd_associativity a c b }
    ((a +% c) +% b) +% d;
    (==) { fadd_associativity (a +% c) b d }
    (a +% c) +% (b +% d);
  }


val fsum_add_i: #w:lanes -> x:felem_v w -> y:felem_v w -> i:nat{i <= w} -> Lemma
  (Loops.repeati i (fsum_f (fadd_v x y)) zero ==
   Loops.repeati i (fsum_f x) zero +% Loops.repeati i (fsum_f y) zero)
let rec fsum_add_i #w x y i =
  let z = fadd_v x y in
  if i = 0 then begin
    Loops.eq_repeati0 i (fsum_f x) zero;
    Loops.eq_repeati0 i (fsum_f y) zero;
    Loops.eq_repeati0 i (fsum_f z) zero;
    fadd_identity zero end
  else begin
    let zi1 = Loops.repeati (i - 1) (fsum_f z) zero in
    let xi1 = Loops.repeati (i - 1) (fsum_f x) zero in
    let yi1 = Loops.repeati (i - 1) (fsum_f y) zero in
    fsum_add_i #w x y (i - 1);
    assert (zi1 == xi1 +% yi1);
    Loops.unfold_repeati i (fsum_f z) zero (i - 1);
    Loops.unfold_repeati i (fsum_f x) zero (i - 1);
    Loops.unfold_repeati i (fsum_f y) zero (i - 1);
    fsum_add_i_step xi1 x.[i - 1] yi1 y.[i - 1] end

val fsum_add: #w:lanes -> x:felem_v w -> y:felem_v w -> Lemma
  (fsum (fadd_v x y) == fsum x +% fsum y)
let fsum_add #w x y = fsum_add_i #w x y w

val fsum_mul_felem_i: #w:lanes -> x:felem_v w -> y:felem -> i:nat{i <= w} -> Lemma
  (Loops.repeati i (fsum_f (fmul_v x (create w y))) zero ==
   Loops.repeati i (fsum_f x) zero *% y)
let rec fsum_mul_felem_i #w x y i =
  let z = fmul_v x (create w y) in
  if i = 0 then begin
    Loops.eq_repeati0 i (fsum_f x) zero;
    Loops.eq_repeati0 i (fsum_f z) zero;
    fmul_zero_l y end
  else begin
    let zi1 = Loops.repeati (i - 1) (fsum_f z) zero in
    let xi1 = Loops.repeati (i - 1) (fsum_f x) zero in
    fsum_mul_felem_i #w x y (i - 1);
    assert (zi1 == xi1 *% y);
    Loops.unfold_repeati i (fsum_f z) zero (i - 1);
    Loops.unfold_repeati i (fsum_f x) zero (i - 1);
    fmul_add_distr_r xi1 x.[i - 1] y end

val fsum_mul_felem: #w:lanes -> x:felem_v w -> y:felem -> Lemma
  (fsum (fmul_v x (create w y)) == fsum x *% y)
let fsum_mul_felem #w x y = fsum_mul_felem_i #w x y w

///
///  Pow-related properties
///

#push-options "--max_fuel 1"
val pow_w_eval_0: r:felem -> Lemma (pow_w 0 r == one)
let pow_w_eval_0 r = ()

val pow_w_unfold: w:pos -> r:felem -> Lemma (pow_w w r == r *% pow_w (w - 1) r)
let pow_w_unfold w r = ()
#pop-options

val pow_w_eval_1: r:felem -> Lemma (pow_w 1 r == r)
let pow_w_eval_1 r =
  pow_w_unfold 1 r;
  pow_w_eval_0 r;
  fmul_commutativity r one;
  fmul_identity r

///
///  Poly evaluation properties
///

val repeat_blocks_multi_fsum_i_step: a:felem -> acc0:felem -> r:felem -> b:felem -> i:pos -> Lemma
  ((a +% (acc0 *% pow_w (i - 1) r +% b)) *% r == acc0 *% pow_w i r +% (b *% r +% a *% r))
let repeat_blocks_multi_fsum_i_step a acc0 r b i =
  calc (==) {
    (a +% (acc0 *% pow_w (i - 1) r +% b)) *% r;
    (==) { fmul_add_distr_r a (acc0 *% pow_w (i - 1) r +% b) r }
    a *% r +% (acc0 *% pow_w (i - 1) r +% b) *% r;
    (==) { fmul_add_distr_r (acc0 *% pow_w (i - 1) r) b r }
    a *% r +% (acc0 *% pow_w (i - 1) r *% r +% b *% r);
    (==) { fmul_associativity acc0 (pow_w (i - 1) r) r }
    a *% r +% (acc0 *% (pow_w (i - 1) r *% r) +% b *% r);
    (==) { fmul_commutativity (pow_w (i - 1) r) r; pow_w_unfold i r }
    a *% r +% (acc0 *% pow_w i r +% b *% r);
    (==) {fadd_commutativity (a *% r) (acc0 *% pow_w i r +% b *% r) }
    (acc0 *% pow_w i r +% b *% r) +% a *% r;
    (==) { fadd_associativity (acc0 *% pow_w i r) (b *% r) (a *% r) }
    acc0 *% pow_w i r +% (b *% r +% a *% r);
    }


let rw_f_one (w:lanes) (n:nat{n <= w}) (r:felem) (i:nat{i < w}) : felem =
  if i < n then pow_w (n - i) r else one

val fsum_mul_r: #w:lanes -> z:felem_v w -> r:felem -> i:nat{i < w} -> Lemma
  (Loops.repeati i (fsum_f z) zero *% r == Loops.repeati i (fsum_f (fmul_v z (create w r))) zero)
let rec fsum_mul_r #w z r i =
  let x = fmul_v z (create w r) in
  if i = 0 then begin
    Loops.eq_repeati0 i (fsum_f z) zero;
    Loops.eq_repeati0 i (fsum_f x) zero;
    fmul_zero_l r end
  else begin
    let lp0 = Loops.repeati (i - 1) (fsum_f z) zero in
    let rp0 = Loops.repeati (i - 1) (fsum_f x) zero in
    fsum_mul_r #w z r (i - 1);
    assert (lp0 *% r == rp0);
    Loops.unfold_repeati i (fsum_f z) zero (i - 1);
    Loops.unfold_repeati i (fsum_f x) zero (i - 1);
    fmul_add_distr_r lp0 z.[i - 1] r end


val repeat_blocks_multi_fsum_i_aux:
  #w:lanes -> b:block_v w -> acc0:felem -> r:felem -> i:nat{i < w} -> Lemma
  (let ri = createi w (rw_f_one w i r) in
   let z = fmul_v (encode_v b) ri in
   let ri1 = createi w (rw_f_one w (i + 1) r) in
   let z1 = fmul_v (encode_v b) ri1 in
   Loops.repeati i (fsum_f z1) zero == Loops.repeati i (fsum_f z) zero *% r)

let repeat_blocks_multi_fsum_i_aux #w b acc0 r i =
  let ri = createi w (rw_f_one w i r) in
  let z = fmul_v (encode_v b) ri in
  let ri1 = createi w (rw_f_one w (i + 1) r) in
  let z1 = fmul_v (encode_v b) ri1 in

  fsum_mul_r #w z r i;

  let aux (k:nat{k < i}) (acc:felem) : Lemma (fsum_f z1 k acc == fsum_f (fmul_v z (create w r)) k acc) =
    assert (ri1.[k] == pow_w (i + 1 - k) r);
    fmul_associativity (encode_v b).[k] ri.[k] r;
    assert (ri.[k] == pow_w (i - k) r);
    pow_w_unfold (i - k + 1) r;
    fmul_commutativity r (pow_w (i - k) r) in

  Classical.forall_intro_2 aux;
  Lemmas.repeati_extensionality i (fsum_f z1) (fsum_f (fmul_v z (create w r))) zero


val repeat_blocks_multi_fsum_i: #w:lanes -> b:block_v w -> acc0:felem -> r:felem -> i:nat{i <= w} -> Lemma
  (let ri = createi w (rw_f_one w i r) in
   let z = fmul_v (encode_v b) ri in
   Math.Lemmas.cancel_mul_mod w blocksize;
   Loops.repeati i (repeat_blocks_f blocksize b (poly_update1 r) w) acc0 ==
   acc0 *% pow_w i r +% Loops.repeati i (fsum_f z) zero)

let rec repeat_blocks_multi_fsum_i #w b acc0 r i =
  Math.Lemmas.cancel_mul_mod w blocksize;
  let f_poly = repeat_blocks_f blocksize b (poly_update1 r) w in
  let acc = Loops.repeati i f_poly acc0 in
  let ri = createi w (rw_f_one w i r) in
  let z = fmul_v (encode_v b) ri in
  let rp = Loops.repeati i (fsum_f z) zero in

  if i = 0 then begin
    Loops.eq_repeati0 i (fsum_f z) zero;
    Loops.eq_repeati0 i f_poly acc0;
    pow_w_eval_0 r;
    fmul_commutativity acc0 one;
    fmul_identity acc0;
    fadd_identity acc0;
    fadd_commutativity acc0 zero end
  else begin
    let fi1 = Loops.repeati (i - 1) f_poly acc0 in
    let ri1 = createi w (rw_f_one w (i - 1) r) in
    let z1 = fmul_v (encode_v b) ri1 in
    let bi1 = Loops.repeati (i - 1) (fsum_f z1) zero in
    repeat_blocks_multi_fsum_i #w b acc0 r (i - 1);
    //assert (fi1 == acc0 *% pow_w (i - 1) r +% bi1);
    Loops.unfold_repeati i f_poly acc0 (i - 1);
    //assert (acc == ((encode_v b).[i - 1] +% (acc0 *% pow_w (i - 1) r +% bi1)) *% r);
    repeat_blocks_multi_fsum_i_aux #w b acc0 r (i - 1);
    //assert (Loops.repeati (i - 1) (fsum_f z) zero == bi1 *% r);
    assert (ri.[i - 1] == pow_w 1 r);
    pow_w_eval_1 r;
    Loops.unfold_repeati i (fsum_f z) zero (i - 1);
    //assert (rp == bi1 *% r +% (encode_v b).[i - 1] *% r);
    repeat_blocks_multi_fsum_i_step (encode_v b).[i - 1] acc0 r bi1 i;
    //assert (acc == acc0 *% pow_w i r +% (bi1 *% r +% (encode_v b).[i - 1] *% r));
    () end


val repeat_blocks_multi_fsum: #w:lanes -> b:block_v w -> acc0:felem -> r:felem -> Lemma
  (let rw = createi w (rw_f #w r) in
   Math.Lemmas.cancel_mul_mod w blocksize;
   repeat_blocks_multi blocksize b (poly_update1 r) acc0 ==
   acc0 *% pow_w w r +% fsum #w (fmul_v (encode_v b) rw))

let repeat_blocks_multi_fsum #w b acc0 r =
  Math.Lemmas.cancel_mul_mod w blocksize;
  lemma_repeat_blocks_multi blocksize b (poly_update1 r) acc0;
  repeat_blocks_multi_fsum_i #w b acc0 r w;
  let rw = createi w (rw_f #w r) in
  let ri = createi w (rw_f_one w w r) in
  eq_intro rw ri


val load_acc_v_lemma_aux: #w:lanes{w > 0} -> x:felem_v w -> y:felem -> i:pos{i <= w} -> Lemma
  (requires x.[0] == y /\ (forall (i:pos{i < w}). x.[i] == zero))
  (ensures  Loops.repeati i (fsum_f x) zero == y)

let rec load_acc_v_lemma_aux #w x y i =
  let fs = Loops.repeati i (fsum_f x) zero in

  if i = 1 then begin
    Loops.unfold_repeati i (fsum_f x) zero (i - 1);
    Loops.eq_repeati0 i (fsum_f x) zero;
    fadd_identity x.[0] end
  else begin
    let fs1 = Loops.repeati (i - 1) (fsum_f x) zero in
    load_acc_v_lemma_aux #w x y (i - 1);
    assert (fs1 == y);
    Loops.unfold_repeati i (fsum_f x) zero (i - 1);
    assert (fs == y +% zero);
    fadd_commutativity y zero;
    fadd_identity y end


val load_acc_v_lemma: #w:lanes{w > 0} -> b:block_v w -> acc0:felem -> r:felem -> Lemma
  (Math.Lemmas.cancel_mul_mod w blocksize;
   normalize_v r (load_acc_v b acc0) == repeat_blocks_multi blocksize b (poly_update1 r) acc0)

let load_acc_v_lemma #w b acc0 r =
  Math.Lemmas.cancel_mul_mod w blocksize;
  let rw = createi w (rw_f #w r) in
  let rp = repeat_blocks_multi blocksize b (poly_update1 r) acc0 in
  let lp = normalize_v r (load_acc_v b acc0) in
  repeat_blocks_multi_fsum #w b acc0 r;
  assert (rp == acc0 *% pow_w w r +% fsum #w (fmul_v (encode_v b) rw));
  let acc_v = create w zero in
  let acc_v = upd acc_v 0 acc0 in
  calc (==) {
    fsum (fmul_v (fadd_v acc_v (encode_v b)) rw);
    (==) { fmul_add_distr_r_v acc_v (encode_v b) rw }
    fsum (fadd_v (fmul_v acc_v rw) (fmul_v (encode_v b) rw));
    (==) { fsum_add (fmul_v acc_v rw) (fmul_v (encode_v b) rw) }
    fsum (fmul_v acc_v rw) +% fsum (fmul_v (encode_v b) rw);
  };

  let aux (i:pos{i < w}) : Lemma ((fmul_v acc_v rw).[i] == zero) =
    fmul_commutativity zero rw.[i];
    fmul_zero_l rw.[i] in
  Classical.forall_intro aux;
  assert (forall (i:pos{i < w}). (fmul_v acc_v rw).[i] == zero);
  assert ((fmul_v acc_v rw).[0] == acc0 *% rw.[0]);
  load_acc_v_lemma_aux #w (fmul_v acc_v rw) (acc0 *% rw.[0]) w;
  assert (fsum (fmul_v acc_v rw) == acc0 *% rw.[0])


val poly_update_nblocks_lemma_aux: #w:lanes -> a:felem_v w -> b:felem_v w -> c:felem_v w -> Lemma
  (fmul_v (fmul_v a b) c == fmul_v (fmul_v a c) b)
let poly_update_nblocks_lemma_aux #w a b c =
  calc (==) {
    fmul_v (fmul_v a b) c;
    (==) { fmul_associativity_v a b c }
    fmul_v a (fmul_v b c);
    (==) { fmul_commutativity_v b c }
    fmul_v a (fmul_v c b);
    (==) { fmul_associativity_v a c b }
    fmul_v (fmul_v a c) b;
  }


val poly_update_nblocks_lemma:
  #w:lanes -> r:felem -> b:block_v w -> acc_v0:felem_v w -> Lemma
  (let pre = create w (pow_w w r) in
  FStar.Math.Lemmas.cancel_mul_mod w blocksize;
  normalize_v r (poly_update_nblocks #w pre b acc_v0) ==
  repeat_blocks_multi blocksize b (poly_update1 r) (normalize_v r acc_v0))

let poly_update_nblocks_lemma #w r b acc_v0 =
  let pre = create w (pow_w w r) in
  let rw = createi w (rw_f #w r) in
  let acc0 = normalize_v r acc_v0 in
  assert (acc0 == fsum (fmul_v acc_v0 rw));
  FStar.Math.Lemmas.cancel_mul_mod w blocksize;
  let acc = repeat_blocks_multi blocksize b (poly_update1 r) acc0 in
  repeat_blocks_multi_fsum #w b acc0 r;
  assert (acc == acc0 *% pow_w w r +% fsum (fmul_v (encode_v b) rw));

  let acc_v = poly_update_nblocks #w pre b acc_v0 in
  calc (==) {
    normalize_v r acc_v;
    (==) { }
    fsum (fmul_v (fadd_v (fmul_v acc_v0 pre) (encode_v b)) rw);
    (==) { fmul_add_distr_r_v (fmul_v acc_v0 pre) (encode_v b) rw }
    fsum (fadd_v (fmul_v (fmul_v acc_v0 pre) rw) (fmul_v (encode_v b) rw));
    (==) { fsum_add (fmul_v (fmul_v acc_v0 pre) rw) (fmul_v (encode_v b) rw) }
    fsum (fmul_v (fmul_v acc_v0 pre) rw) +% fsum (fmul_v (encode_v b) rw);
    (==) { poly_update_nblocks_lemma_aux acc_v0 pre rw }
    fsum (fmul_v (fmul_v acc_v0 rw) pre) +% fsum (fmul_v (encode_v b) rw);
    (==) { fsum_mul_felem (fmul_v acc_v0 rw) (pow_w w r) }
    fsum (fmul_v acc_v0 rw) *% pow_w w r +% fsum (fmul_v (encode_v b) rw);
    (==) { }
    acc;
  }
