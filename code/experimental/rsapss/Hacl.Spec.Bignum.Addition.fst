module Hacl.Spec.Bignum.Addition

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Bignum
open Hacl.Spec.Bignum.Base

module Loops = Lib.LoopCombinators

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let generate_elem_a (t:Type0) (a:Type0) (max:nat) (i:nat{i <= max}) = a & s:seq t{length s == i}

val generate_elem_f:
    #t:Type0
  -> #a:Type0
  -> max:nat
  -> f:(i:nat{i < max} -> a -> a & t)
  -> i:nat{i < max}
  -> acc:generate_elem_a t a max i ->
  generate_elem_a t a max (i + 1)

let generate_elem_f #t #a max f i (c, res) =
  let c', e = f i c in
  let res' = Seq.snoc res e in
  c', res'


val generate_elems:
    #t:Type0
  -> #a:Type0
  -> max:nat
  -> n:nat{n <= max}
  -> f:(i:nat{i < max} -> a -> a & t)
  -> init:a ->
  Tot (a & s:seq t{length s == n})

let generate_elems #t #a max n f init =
  let init2 : generate_elem_a t a max 0 = (init, Seq.empty) in
  Loops.repeat_gen n (generate_elem_a t a max) (generate_elem_f max f) init2


val eq_generate_elems0:
    #t:Type0
  -> #a:Type0
  -> max:nat
  -> n:nat{n <= max}
  -> f:(i:nat{i < max} -> a -> a & t)
  -> init:a ->
  Lemma (generate_elems #t #a max 0 f init == (init, Seq.empty))

let eq_generate_elems0 #t #a max n f init =
  let init2 : generate_elem_a t a max 0 = (init, Seq.empty) in
  Loops.eq_repeat_gen0 n (generate_elem_a t a max) (generate_elem_f max f) init2


val generate_elems_unfold:
    #t:Type0
  -> #a:Type0
  -> max:nat
  -> n:nat{n <= max}
  -> f:(i:nat{i < max} -> a -> a & t)
  -> init:a
  -> i:nat{i < n} -> Lemma
  (generate_elems #t #a max (i + 1) f init ==
   generate_elem_f max f i (generate_elems #t #a max i f init))

let generate_elems_unfold #t #a max n f init i =
  let init2 : generate_elem_a t a max 0 = (init, Seq.empty) in
  Loops.unfold_repeat_gen (i + 1) (generate_elem_a t a max) (generate_elem_f max f) init2 i


val bn_sub_f:
    #aLen:size_nat
  -> #bLen:size_nat{bLen <= aLen}
  -> a:lbignum aLen
  -> b:lbignum bLen
  -> i:size_nat{i < aLen}
  -> c:carry ->
  carry & uint64

let bn_sub_f #aLen #bLen a b i c =
  subborrow_u64 c a.[i] (bval b i)


val bn_sub:
    #aLen:size_nat
  -> #bLen:size_nat{bLen <= aLen}
  -> a:lbignum aLen
  -> b:lbignum bLen ->
  tuple2 carry (lbignum aLen)

let bn_sub #aLen #bLen a b =
  generate_elems #uint64 #carry aLen aLen (bn_sub_f a b) (u64 0)



val bn_add_f:
    #aLen:size_nat
  -> #bLen:size_nat{bLen <= aLen}
  -> a:lbignum aLen
  -> b:lbignum bLen
  -> i:size_nat{i < aLen}
  -> c:carry ->
  carry & uint64

let bn_add_f #aLen #bLen a b i c =
  addcarry_u64 c a.[i] (bval b i)


val bn_add:
    #aLen:size_nat
  -> #bLen:size_nat{bLen <= aLen}
  -> a:lbignum aLen
  -> b:lbignum bLen ->
  carry & lbignum aLen

let bn_add #aLen #bLen a b =
  generate_elems #uint64 #carry aLen aLen (bn_add_f a b) (u64 0)


///
///  Lemma (let (c, res) = bn_add #aLen #bLen a b in v c * pow2 (64 * aLen) + bn_v res == bn_v a + bn_v b)
///

val bn_add_lemma_loop_step:
    #aLen:size_nat
  -> #bLen:size_nat{bLen <= aLen}
  -> a:lbignum aLen
  -> b:lbignum bLen
  -> i:pos{i <= aLen}
  -> c1_res1:generate_elem_a uint64 carry aLen (i - 1)
  -> Lemma
  (requires
   (let (c1, res1) = c1_res1 in
    v c1 * pow2 (64 * (i - 1)) + bn_v #(i - 1) res1 == eval_ aLen a (i - 1) + eval_bval bLen b (i - 1)))
  (ensures
   (let (c1, res1) = c1_res1 in
    let (c, res) = generate_elem_f #uint64 #carry aLen (bn_add_f a b) (i - 1) (c1, res1) in
    v c * pow2 (64 * i) + bn_v #i res == eval_ aLen a i + eval_bval bLen b i))

let bn_add_lemma_loop_step #aLen #bLen a b i (c1, res1) =
  let (c, res) = generate_elem_f #uint64 #carry aLen (bn_add_f a b) (i - 1) (c1, res1) in
  let c, e = bn_add_f a b (i - 1) c1 in
  let bi1 = if i - 1 < bLen then b.[i - 1] else u64 0 in
  assert (v e + v c * pow2 64 == v a.[i - 1] + v bi1 + v c1);

  calc (==) {
    v c * pow2 (64 * i) + bn_v #i res;
    (==) { bn_eval_snoc #(i - 1) res1 e }
    v c * pow2 (64 * i) + bn_v #(i - 1) res1 + v e * pow2 (64 * (i - 1));
    (==) { }
    v c * pow2 (64 * i) + eval_ aLen a (i - 1) + eval_bval bLen b (i - 1) - (v e + v c * pow2 64 - v a.[i - 1] - v bi1) * pow2 (64 * (i - 1)) + v e * pow2 (64 * (i - 1));
    (==) { Math.Lemmas.distributivity_sub_left (v e) (v e + v c * pow2 64 - v a.[i - 1] - v bi1) (pow2 (64 * (i - 1))) }
    v c * pow2 (64 * i) + eval_ aLen a (i - 1) + eval_bval bLen b (i - 1) + (v e - v e - v c * pow2 64 + v a.[i - 1] + v bi1) * pow2 (64 * (i - 1));
    (==) { Math.Lemmas.distributivity_sub_left (v a.[i - 1] + v bi1) (v c1 * pow2 64) (pow2 (64 * (i - 1))) }
    v c * pow2 (64 * i) + eval_ aLen a (i - 1) + eval_bval bLen b (i - 1) + (v a.[i - 1] + v bi1) * pow2 (64 * (i - 1)) - v c * pow2 64 * pow2 (64 * (i - 1));
    (==) { Math.Lemmas.paren_mul_right (v c) (pow2 64) (pow2 (64 * (i - 1))); Math.Lemmas.pow2_plus 64 (64 * (i - 1)) }
    eval_ aLen a (i - 1) + eval_bval bLen b (i - 1) + (v a.[i - 1] + v bi1) * pow2 (64 * (i - 1));
    (==) { Math.Lemmas.distributivity_add_left (v a.[i - 1]) (v bi1) (pow2 (64 * (i - 1))) }
    eval_ aLen a (i - 1) + eval_bval bLen b (i - 1) + v a.[i - 1] * pow2 (64 * (i - 1)) + v bi1 * pow2 (64 * (i - 1));
    (==) { bn_eval_unfold_i #aLen a i }
    eval_ aLen a i + eval_bval bLen b (i - 1) + v bi1 * pow2 (64 * (i - 1));
    (==) { bn_eval_bval_unfold_i #bLen b i }
    eval_ aLen a i + eval_bval bLen b i;
  };
  assert (v c * pow2 (64 * i) + bn_v #i res == eval_ aLen a i + eval_bval bLen b i)


val bn_add_lemma_loop:
    #aLen:size_nat
  -> #bLen:size_nat{bLen <= aLen}
  -> a:lbignum aLen
  -> b:lbignum bLen
  -> i:nat{i <= aLen} -> Lemma
  (let (c, res) : generate_elem_a uint64 carry aLen i = generate_elems #uint64 #carry aLen i (bn_add_f a b) (u64 0) in
   v c * pow2 (64 * i) + bn_v #i res == eval_ aLen a i + eval_bval bLen b i)

let rec bn_add_lemma_loop #aLen #bLen a b i =
  let (c, res) : generate_elem_a uint64 carry aLen i = generate_elems #uint64 #carry aLen i (bn_add_f a b) (u64 0) in
  if i = 0 then begin
    eq_generate_elems0 #uint64 #carry aLen i (bn_add_f a b) (u64 0);
    assert (c == u64 0 /\ res == Seq.empty);
    bn_eval0 #0 res;
    assert_norm (pow2 0 = 1);
    bn_eval0 a;
    bn_eval0 b;
    () end
  else begin
    let (c1, res1) : generate_elem_a uint64 carry aLen (i - 1) = generate_elems #uint64 #carry aLen (i - 1) (bn_add_f a b) (u64 0) in
    generate_elems_unfold #uint64 #carry aLen i (bn_add_f a b) (u64 0) (i - 1);
    assert (generate_elems #uint64 #carry aLen i (bn_add_f a b) (u64 0) ==
      generate_elem_f aLen (bn_add_f a b) (i - 1) (generate_elems #uint64 #carry aLen (i - 1) (bn_add_f a b) (u64 0)));
    assert ((c, res) == generate_elem_f #uint64 #carry aLen (bn_add_f a b) (i - 1) (c1, res1));
    bn_add_lemma_loop #aLen #bLen a b (i - 1);
    assert (v c1 * pow2 (64 * (i - 1)) + bn_v #(i - 1) res1 == eval_ aLen a (i - 1) + eval_bval bLen b (i - 1));
    bn_add_lemma_loop_step #aLen #bLen a b i (c1, res1);
    assert (v c * pow2 (64 * i) + bn_v #i res == eval_ aLen a i + eval_bval bLen b i);
    () end


val bn_add_lemma:
    #aLen:size_nat
  -> #bLen:size_nat{bLen <= aLen}
  -> a:lbignum aLen
  -> b:lbignum bLen -> Lemma
  (let (c, res) = bn_add #aLen #bLen a b in
   v c * pow2 (64 * aLen) + bn_v res == bn_v a + bn_v b)

let bn_add_lemma #aLen #bLen a b =
  let (c, res) = bn_add #aLen #bLen a b in
  bn_add_lemma_loop #aLen #bLen a b aLen


///
///  Lemma (let (c, res) = bn_sub #aLen #bLen a b in bn_v res - v c * pow2 (64 * aLen) == bn_v a - bn_v b)
///


val bn_sub_lemma_loop_step:
    #aLen:size_nat
  -> #bLen:size_nat{bLen <= aLen}
  -> a:lbignum aLen
  -> b:lbignum bLen
  -> i:pos{i <= aLen}
  -> c1_res1:generate_elem_a uint64 carry aLen (i - 1)
  -> Lemma
  (requires
   (let (c1, res1) = c1_res1 in
    bn_v #(i - 1) res1 - v c1 * pow2 (64 * (i - 1)) == eval_ aLen a (i - 1) - eval_bval bLen b (i - 1)))
  (ensures
   (let (c1, res1) = c1_res1 in
    let (c, res) = generate_elem_f #uint64 #carry aLen (bn_sub_f a b) (i - 1) (c1, res1) in
    bn_v #i res - v c * pow2 (64 * i) == eval_ aLen a i - eval_bval bLen b i))

let bn_sub_lemma_loop_step #aLen #bLen a b i (c1, res1) =
  let (c, res) = generate_elem_f #uint64 #carry aLen (bn_sub_f a b) (i - 1) (c1, res1) in
  let c, e = bn_sub_f a b (i - 1) c1 in
  let bi1 = if i - 1 < bLen then b.[i - 1] else u64 0 in
  assert (v e - v c * pow2 64 == v a.[i - 1] - v bi1 - v c1);

  calc (==) {
    bn_v #i res - v c * pow2 (64 * i);
    (==) { bn_eval_snoc #(i - 1) res1 e }
    bn_v #(i - 1) res1 + v e * pow2 (64 * (i - 1)) - v c * pow2 (64 * i);
    (==) { }
    eval_ aLen a (i - 1) - eval_bval bLen b (i - 1) + (v a.[i - 1] - v bi1 + v c * pow2 64 - v e) * pow2 (64 * (i - 1)) + v e * pow2 (64 * (i - 1)) - v c * pow2 (64 * i);
    (==) { Math.Lemmas.distributivity_sub_left (v a.[i - 1] - v bi1 + v c * pow2 64) (v e) (pow2 (64 * (i - 1))) }
    eval_ aLen a (i - 1) - eval_bval bLen b (i - 1) + (v a.[i - 1] - v bi1 + v c * pow2 64) * pow2 (64 * (i - 1)) - v c * pow2 (64 * i);
    (==) { Math.Lemmas.distributivity_add_left (v a.[i - 1] - v bi1) (v c * pow2 64) (pow2 (64 * (i - 1))) }
    eval_ aLen a (i - 1) - eval_bval bLen b (i - 1) + (v a.[i - 1] - v bi1) * pow2 (64 * (i - 1)) + v c * pow2 64 * pow2 (64 * (i - 1)) - v c * pow2 (64 * i);
    (==) { Math.Lemmas.paren_mul_right (v c) (pow2 64) (pow2 (64 * (i - 1))); Math.Lemmas.pow2_plus 64 (64 * (i - 1)) }
    eval_ aLen a (i - 1) - eval_bval bLen b (i - 1) + (v a.[i - 1] - v bi1) * pow2 (64 * (i - 1));
    (==) { Math.Lemmas.distributivity_sub_left (v a.[i - 1]) (v bi1) (pow2 (64 * (i - 1))) }
    eval_ aLen a (i - 1) - eval_bval bLen b (i - 1) + v a.[i - 1] * pow2 (64 * (i - 1)) - v bi1 * pow2 (64 * (i - 1));
    (==) { bn_eval_unfold_i #aLen a i }
    eval_ aLen a i - eval_bval bLen b (i - 1) - v bi1 * pow2 (64 * (i - 1));
    (==) { bn_eval_bval_unfold_i #bLen b i }
    eval_ aLen a i - eval_bval bLen b i;
  };
  assert (bn_v #i res - v c * pow2 (64 * i) == eval_ aLen a i - eval_bval bLen b i)


val bn_sub_lemma_loop:
    #aLen:size_nat
  -> #bLen:size_nat{bLen <= aLen}
  -> a:lbignum aLen
  -> b:lbignum bLen
  -> i:nat{i <= aLen} -> Lemma
  (let (c, res) : generate_elem_a uint64 carry aLen i = generate_elems #uint64 #carry aLen i (bn_sub_f a b) (u64 0) in
   bn_v #i res - v c * pow2 (64 * i) == eval_ aLen a i - eval_bval bLen b i)

let rec bn_sub_lemma_loop #aLen #bLen a b i =
  let (c, res) : generate_elem_a uint64 carry aLen i = generate_elems #uint64 #carry aLen i (bn_sub_f a b) (u64 0) in
  if i = 0 then begin
    eq_generate_elems0 #uint64 #carry aLen i (bn_sub_f a b) (u64 0);
    assert (c == u64 0 /\ res == Seq.empty);
    bn_eval0 #0 res;
    assert_norm (pow2 0 = 1);
    bn_eval0 a;
    bn_eval0 b;
    () end
  else begin
    let (c1, res1) : generate_elem_a uint64 carry aLen (i - 1) = generate_elems #uint64 #carry aLen (i - 1) (bn_sub_f a b) (u64 0) in
    generate_elems_unfold #uint64 #carry aLen i (bn_sub_f a b) (u64 0) (i - 1);
    assert (generate_elems #uint64 #carry aLen i (bn_sub_f a b) (u64 0) ==
      generate_elem_f aLen (bn_sub_f a b) (i - 1) (generate_elems #uint64 #carry aLen (i - 1) (bn_sub_f a b) (u64 0)));
    assert ((c, res) == generate_elem_f #uint64 #carry aLen (bn_sub_f a b) (i - 1) (c1, res1));
    bn_sub_lemma_loop #aLen #bLen a b (i - 1);
    assert (bn_v #(i - 1) res1 - v c1 * pow2 (64 * (i - 1)) == eval_ aLen a (i - 1) - eval_bval bLen b (i - 1));
    bn_sub_lemma_loop_step #aLen #bLen a b i (c1, res1);
    assert (bn_v #i res - v c * pow2 (64 * i) == eval_ aLen a i - eval_bval bLen b i);
    () end


val bn_sub_lemma:
    #aLen:size_nat
  -> #bLen:size_nat{bLen <= aLen}
  -> a:lbignum aLen
  -> b:lbignum bLen -> Lemma
  (let (c, res) = bn_sub #aLen #bLen a b in
   bn_v res - v c * pow2 (64 * aLen) == bn_v a - bn_v b)

let bn_sub_lemma #aLen #bLen a b =
  let (c, res) = bn_sub #aLen #bLen a b in
  bn_sub_lemma_loop #aLen #bLen a b aLen
