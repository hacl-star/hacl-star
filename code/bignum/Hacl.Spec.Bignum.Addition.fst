module Hacl.Spec.Bignum.Addition

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Bignum.Definitions
open Hacl.Spec.Bignum.Base
open Hacl.Spec.Lib


#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val bn_sub1_f: #aLen:size_nat -> a:lbignum aLen -> i:size_nat{i < aLen} -> c_in:carry -> carry & uint64
let bn_sub1_f #aLen a i c_in = subborrow_u64 c_in a.[i] (u64 0)

val bn_sub1: #aLen:size_nat -> a:lbignum aLen -> c_in:carry -> tuple2 carry (lbignum aLen)
let bn_sub1 #aLen a c_in = generate_elems #uint64 #carry aLen aLen (bn_sub1_f a) c_in

val bn_sub_f: #aLen:size_nat -> a:lbignum aLen -> b:lbignum aLen -> i:size_nat{i < aLen} -> c:carry -> carry & uint64
let bn_sub_f #aLen a b i c = subborrow_u64 c a.[i] b.[i]

val bn_sub: #aLen:size_nat -> #bLen:size_nat{bLen <= aLen} -> a:lbignum aLen -> b:lbignum bLen -> tuple2 carry (lbignum aLen)
let bn_sub #aLen #bLen a b =
  let c0, res0 = generate_elems #uint64 #carry bLen bLen (bn_sub_f (sub a 0 bLen) b) (u64 0) in

  if bLen < aLen then
    let c1, res1 = bn_sub1 (sub a bLen (aLen - bLen)) c0 in
    c1, concat #_ #bLen res0 res1
  else c0, res0


val bn_add1_f: #aLen:size_nat -> a:lbignum aLen -> i:size_nat{i < aLen} -> c_in:carry -> carry & uint64
let bn_add1_f #aLen a i c_in = addcarry_u64 c_in a.[i] (u64 0)

val bn_add1: #aLen:size_nat -> a:lbignum aLen -> c_in:carry -> tuple2 carry (lbignum aLen)
let bn_add1 #aLen a c_in = generate_elems #uint64 #carry aLen aLen (bn_add1_f a) c_in

val bn_add_f: #aLen:size_nat -> a:lbignum aLen -> b:lbignum aLen -> i:size_nat{i < aLen} -> c:carry -> carry & uint64
let bn_add_f #aLen a b i c = addcarry_u64 c a.[i] b.[i]

val bn_add: #aLen:size_nat -> #bLen:size_nat{bLen <= aLen} -> a:lbignum aLen -> b:lbignum bLen -> carry & lbignum aLen
let bn_add #aLen #bLen a b =
  let c0, res0 = generate_elems #uint64 #carry bLen bLen (bn_add_f (sub a 0 bLen) b) (u64 0) in

  if bLen < aLen then
    let c1, res1 = bn_add1 (sub a bLen (aLen - bLen)) c0 in
    c1, concat #_ #bLen res0 res1
  else c0, res0


val bn_add1_lemma_loop_step:
    #aLen:size_nat
  -> a:lbignum aLen
  -> c_in:carry
  -> i:pos{i <= aLen}
  -> c1_res1:generate_elem_a uint64 carry aLen (i - 1)
  -> Lemma
  (requires
   (let (c1, res1) = c1_res1 in
    v c1 * pow2 (64 * (i - 1)) + bn_v #(i - 1) res1 == eval_ aLen a (i - 1) + v c_in))
  (ensures
   (let (c_out, res) = generate_elem_f #uint64 #carry aLen (bn_add1_f a) (i - 1) c1_res1 in
    v c_out * pow2 (64 * i) + bn_v #i res == eval_ aLen a i + v c_in))

let bn_add1_lemma_loop_step #aLen a c_in i (c1, res1) =
  let (c_out, res) = generate_elem_f #uint64 #carry aLen (bn_add1_f a) (i - 1) (c1, res1) in
  let c, e = bn_add1_f a (i - 1) c1 in
  assert (v e + v c * pow2 64 == v a.[i - 1] + v c1);

  calc (==) {
    v c * pow2 (64 * i) + bn_v #i res;
    (==) { bn_eval_snoc #(i - 1) res1 e }
    v c * pow2 (64 * i) + bn_v #(i - 1) res1 + v e * pow2 (64 * (i - 1));
    (==) { }
    v c * pow2 (64 * i) + eval_ aLen a (i - 1) + v c_in - (v e + v c * pow2 64 - v a.[i - 1]) * pow2 (64 * (i - 1)) + v e * pow2 (64 * (i - 1));
    (==) { Math.Lemmas.distributivity_sub_left (v e) (v e + v c * pow2 64 - v a.[i - 1]) (pow2 (64 * (i - 1))) }
    v c * pow2 (64 * i) + eval_ aLen a (i - 1) + v c_in + (v e - v e - v c * pow2 64 + v a.[i - 1]) * pow2 (64 * (i - 1));
    (==) { Math.Lemmas.distributivity_sub_left (v a.[i - 1]) (v c * pow2 64) (pow2 (64 * (i - 1))) }
    v c * pow2 (64 * i) + eval_ aLen a (i - 1) + v c_in + v a.[i - 1] * pow2 (64 * (i - 1)) - v c * pow2 64 * pow2 (64 * (i - 1));
    (==) { Math.Lemmas.paren_mul_right (v c) (pow2 64) (pow2 (64 * (i - 1))); Math.Lemmas.pow2_plus 64 (64 * (i - 1)) }
    eval_ aLen a (i - 1) + v c_in + v a.[i - 1] * pow2 (64 * (i - 1));
    (==) { bn_eval_unfold_i #aLen a i }
    eval_ aLen a i + v c_in;
  };
  assert (v c * pow2 (64 * i) + bn_v #i res == eval_ aLen a i + v c_in)


val bn_add1_lemma_loop:
    #aLen:size_nat
  -> a:lbignum aLen
  -> c_in:carry
  -> i:nat{i <= aLen} -> Lemma
  (let (c_out, res) : generate_elem_a uint64 carry aLen i = generate_elems #uint64 #carry aLen i (bn_add1_f a) c_in in
   v c_out * pow2 (64 * i) + bn_v #i res == eval_ aLen a i + v c_in)

let rec bn_add1_lemma_loop #aLen a c_in i =
  let (c_out, res) : generate_elem_a uint64 carry aLen i = generate_elems #uint64 #carry aLen i (bn_add1_f a) c_in in
  if i = 0 then begin
    eq_generate_elems0 #uint64 #carry aLen i (bn_add1_f a) c_in;
    assert (c_out == c_in /\ res == Seq.empty);
    bn_eval0 #0 res;
    assert_norm (pow2 0 = 1);
    bn_eval0 a;
    () end
  else begin
    let (c1, res1) : generate_elem_a uint64 carry aLen (i - 1) = generate_elems #uint64 #carry aLen (i - 1) (bn_add1_f a) c_in in
    generate_elems_unfold #uint64 #carry aLen i (bn_add1_f a) c_in (i - 1);
    assert (generate_elems #uint64 #carry aLen i (bn_add1_f a) c_in ==
      generate_elem_f aLen (bn_add1_f a) (i - 1) (generate_elems #uint64 #carry aLen (i - 1) (bn_add1_f a) c_in));
    assert ((c_out, res) == generate_elem_f #uint64 #carry aLen (bn_add1_f a) (i - 1) (c1, res1));
    bn_add1_lemma_loop #aLen a c_in (i - 1);
    assert (v c1 * pow2 (64 * (i - 1)) + bn_v #(i - 1) res1 == eval_ aLen a (i - 1) + v c_in);
    bn_add1_lemma_loop_step #aLen a c_in i (c1, res1);
    assert (v c_out * pow2 (64 * i) + bn_v #i res == eval_ aLen a i + v c_in);
    () end


val bn_add1_lemma: #aLen:size_nat -> a:lbignum aLen -> c_in:carry ->
  Lemma
  (let (c_out, res) = bn_add1 #aLen a c_in in
   v c_out * pow2 (64 * aLen) + bn_v res == bn_v a + v c_in)

let bn_add1_lemma #aLen a c_in =
  let (c_out, res) = bn_add1 #aLen a c_in in
  bn_add1_lemma_loop #aLen a c_in aLen


val bn_add_lemma_loop_step:
    #aLen:size_nat
  -> a:lbignum aLen
  -> b:lbignum aLen
  -> i:pos{i <= aLen}
  -> c1_res1:generate_elem_a uint64 carry aLen (i - 1)
  -> Lemma
  (requires
   (let (c1, res1) = c1_res1 in
    v c1 * pow2 (64 * (i - 1)) + bn_v #(i - 1) res1 == eval_ aLen a (i - 1) + eval_ aLen b (i - 1)))
  (ensures
   (let (c1, res1) = c1_res1 in
    let (c, res) = generate_elem_f #uint64 #carry aLen (bn_add_f a b) (i - 1) (c1, res1) in
    v c * pow2 (64 * i) + bn_v #i res == eval_ aLen a i + eval_ aLen b i))

let bn_add_lemma_loop_step #aLen a b i (c1, res1) =
  let (c, res) = generate_elem_f #uint64 #carry aLen (bn_add_f a b) (i - 1) (c1, res1) in
  let c, e = bn_add_f a b (i - 1) c1 in
  assert (v e + v c * pow2 64 == v a.[i - 1] + v b.[i - 1] + v c1);

  calc (==) {
    v c * pow2 (64 * i) + bn_v #i res;
    (==) { bn_eval_snoc #(i - 1) res1 e }
    v c * pow2 (64 * i) + bn_v #(i - 1) res1 + v e * pow2 (64 * (i - 1));
    (==) { }
    v c * pow2 (64 * i) + eval_ aLen a (i - 1) + eval_ aLen b (i - 1) - (v e + v c * pow2 64 - v a.[i - 1] - v b.[i - 1]) * pow2 (64 * (i - 1)) + v e * pow2 (64 * (i - 1));
    (==) { Math.Lemmas.distributivity_sub_left (v e) (v e + v c * pow2 64 - v a.[i - 1] - v b.[i - 1]) (pow2 (64 * (i - 1))) }
    v c * pow2 (64 * i) + eval_ aLen a (i - 1) + eval_ aLen b (i - 1) + (v e - v e - v c * pow2 64 + v a.[i - 1] + v b.[i - 1]) * pow2 (64 * (i - 1));
    (==) { Math.Lemmas.distributivity_sub_left (v a.[i - 1] + v b.[i - 1]) (v c1 * pow2 64) (pow2 (64 * (i - 1))) }
    v c * pow2 (64 * i) + eval_ aLen a (i - 1) + eval_ aLen b (i - 1) + (v a.[i - 1] + v b.[i - 1]) * pow2 (64 * (i - 1)) - v c * pow2 64 * pow2 (64 * (i - 1));
    (==) { Math.Lemmas.paren_mul_right (v c) (pow2 64) (pow2 (64 * (i - 1))); Math.Lemmas.pow2_plus 64 (64 * (i - 1)) }
    eval_ aLen a (i - 1) + eval_ aLen b (i - 1) + (v a.[i - 1] + v b.[i - 1]) * pow2 (64 * (i - 1));
    (==) { Math.Lemmas.distributivity_add_left (v a.[i - 1]) (v b.[i - 1]) (pow2 (64 * (i - 1))) }
    eval_ aLen a (i - 1) + eval_ aLen b (i - 1) + v a.[i - 1] * pow2 (64 * (i - 1)) + v b.[i - 1] * pow2 (64 * (i - 1));
    (==) { bn_eval_unfold_i #aLen a i }
    eval_ aLen a i + eval_ aLen b (i - 1) + v b.[i - 1] * pow2 (64 * (i - 1));
    (==) { bn_eval_unfold_i #aLen b i }
    eval_ aLen a i + eval_ aLen b i;
  };
  assert (v c * pow2 (64 * i) + bn_v #i res == eval_ aLen a i + eval_ aLen b i)


val bn_add_lemma_loop:
    #aLen:size_nat
  -> a:lbignum aLen
  -> b:lbignum aLen
  -> i:nat{i <= aLen} -> Lemma
  (let (c, res) : generate_elem_a uint64 carry aLen i = generate_elems #uint64 #carry aLen i (bn_add_f a b) (u64 0) in
   v c * pow2 (64 * i) + bn_v #i res == eval_ aLen a i + eval_ aLen b i)

let rec bn_add_lemma_loop #aLen a b i =
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
    bn_add_lemma_loop #aLen a b (i - 1);
    assert (v c1 * pow2 (64 * (i - 1)) + bn_v #(i - 1) res1 == eval_ aLen a (i - 1) + eval_ aLen b (i - 1));
    bn_add_lemma_loop_step #aLen a b i (c1, res1);
    assert (v c * pow2 (64 * i) + bn_v #i res == eval_ aLen a i + eval_ aLen b i);
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
  if bLen = aLen then
    bn_add_lemma_loop #aLen a b aLen
  else begin
    let a0 = sub a 0 bLen in
    let a1 = sub a bLen (aLen - bLen) in

    let c0, res0 = generate_elems #uint64 #carry bLen bLen (bn_add_f a0 b) (u64 0) in
    bn_add_lemma_loop #bLen a0 b bLen;
    assert (v c0 * pow2 (64 * bLen) + bn_v #bLen res0 == eval_ bLen a0 bLen + eval_ bLen b bLen);
    let c1, res1 = bn_add1 a1 c0 in
    bn_add1_lemma a1 c0;
    assert (v c1 * pow2 (64 * (aLen - bLen)) + bn_v res1 == bn_v a1 + v c0);
    let res = concat #_ #bLen res0 res1 in
    eq_intro (slice res 0 bLen) res0;
    eq_intro (slice res bLen aLen) res1;
    bn_eval_split_i res bLen;
    assert (bn_v res == bn_v #bLen res0 + pow2 (64 * bLen) * bn_v res1);
    calc (==) {
      bn_v #bLen res0 + pow2 (64 * bLen) * bn_v res1;
      (==) { }
      eval_ bLen a0 bLen + eval_ bLen b bLen - v c0 * pow2 (64 * bLen) + pow2 (64 * bLen) * (bn_v a1 + v c0 - v c1 * pow2 (64 * (aLen - bLen)));
      (==) { Math.Lemmas.distributivity_sub_right (pow2 (64 * bLen)) (bn_v a1 + v c0) (v c1 * pow2 (64 * (aLen - bLen))) }
      eval_ bLen a0 bLen + eval_ bLen b bLen - v c0 * pow2 (64 * bLen) + pow2 (64 * bLen) * (bn_v a1 + v c0) - pow2 (64 * bLen) * v c1 * pow2 (64 * (aLen - bLen));
      (==) { Math.Lemmas.paren_mul_right (pow2 (64 * bLen)) (v c1) (pow2 (64 * (aLen - bLen))); Math.Lemmas.pow2_plus (64 * bLen) (64 * (aLen - bLen)) }
      eval_ bLen a0 bLen + eval_ bLen b bLen - v c0 * pow2 (64 * bLen) + pow2 (64 * bLen) * (bn_v a1 + v c0) - v c1 * pow2 (64 * aLen);
      (==) { Math.Lemmas.distributivity_sub_right (pow2 (64 * bLen)) (bn_v a1) (v c0) }
      eval_ bLen a0 bLen + eval_ bLen b bLen + pow2 (64 * bLen) * bn_v a1 - v c1 * pow2 (64 * aLen);
      (==) { bn_eval_split_i a bLen; bn_eval_extensionality_j a (sub a 0 bLen) bLen }
      eval_ aLen a aLen + eval_ bLen b bLen  - v c1 * pow2 (64 * aLen);
    }; () end


val bn_sub1_lemma_loop_step:
    #aLen:size_nat
  -> a:lbignum aLen
  -> c_in:carry
  -> i:pos{i <= aLen}
  -> c1_res1:generate_elem_a uint64 carry aLen (i - 1)
  -> Lemma
  (requires
   (let (c1, res1) = c1_res1 in
    bn_v #(i - 1) res1 - v c1 * pow2 (64 * (i - 1)) == eval_ aLen a (i - 1) - v c_in))
  (ensures
   (let (c_out, res) = generate_elem_f #uint64 #carry aLen (bn_sub1_f a) (i - 1) c1_res1 in
    bn_v #i res - v c_out * pow2 (64 * i) == eval_ aLen a i - v c_in))

let bn_sub1_lemma_loop_step #aLen a c_in i (c1, res1) =
  let (c_out, res) = generate_elem_f #uint64 #carry aLen (bn_sub1_f a) (i - 1) (c1, res1) in
  let c, e = bn_sub1_f a (i - 1) c1 in
  assert (v e - v c * pow2 64 == v a.[i - 1] - v c1);

  calc (==) {
    bn_v #i res - v c * pow2 (64 * i);
    (==) { bn_eval_snoc #(i - 1) res1 e }
    bn_v #(i - 1) res1 + v e * pow2 (64 * (i - 1)) - v c * pow2 (64 * i);
    (==) { }
    eval_ aLen a (i - 1) - v c_in + (v a.[i - 1] - v e + v c * pow2 64) * pow2 (64 * (i - 1)) + v e * pow2 (64 * (i - 1)) - v c * pow2 (64 * i);
    (==) { Math.Lemmas.distributivity_sub_left (v a.[i - 1] + v c * pow2 64) (v e) (pow2 (64 * (i - 1))) }
    eval_ aLen a (i - 1) - v c_in + (v a.[i - 1] + v c * pow2 64) * pow2 (64 * (i - 1)) - v c * pow2 (64 * i);
    (==) { Math.Lemmas.distributivity_add_left (v a.[i - 1]) (v c * pow2 64) (pow2 (64 * (i - 1))) }
    eval_ aLen a (i - 1) - v c_in + v a.[i - 1] * pow2 (64 * (i - 1)) + v c * pow2 64 * pow2 (64 * (i - 1)) - v c * pow2 (64 * i);
    (==) { Math.Lemmas.paren_mul_right (v c) (pow2 64) (pow2 (64 * (i - 1))); Math.Lemmas.pow2_plus 64 (64 * (i - 1)) }
    eval_ aLen a (i - 1) - v c_in + v a.[i - 1] * pow2 (64 * (i - 1));
    (==) { bn_eval_unfold_i #aLen a i }
    eval_ aLen a i - v c_in;
  };
  assert (bn_v #i res - v c * pow2 (64 * i) == eval_ aLen a i - v c_in)


val bn_sub1_lemma_loop:
    #aLen:size_nat
  -> a:lbignum aLen
  -> c_in:carry
  -> i:nat{i <= aLen} -> Lemma
  (let (c_out, res) : generate_elem_a uint64 carry aLen i = generate_elems #uint64 #carry aLen i (bn_sub1_f a) c_in in
   bn_v #i res - v c_out * pow2 (64 * i) == eval_ aLen a i - v c_in)

let rec bn_sub1_lemma_loop #aLen a c_in i =
  let (c_out, res) : generate_elem_a uint64 carry aLen i = generate_elems #uint64 #carry aLen i (bn_sub1_f a) c_in in
  if i = 0 then begin
    eq_generate_elems0 #uint64 #carry aLen i (bn_sub1_f a) c_in;
    assert (c_out == c_in /\ res == Seq.empty);
    bn_eval0 #0 res;
    assert_norm (pow2 0 = 1);
    bn_eval0 a;
    () end
  else begin
    let (c1, res1) : generate_elem_a uint64 carry aLen (i - 1) = generate_elems #uint64 #carry aLen (i - 1) (bn_sub1_f a) c_in in
    generate_elems_unfold #uint64 #carry aLen i (bn_sub1_f a) c_in (i - 1);
    assert (generate_elems #uint64 #carry aLen i (bn_sub1_f a) c_in ==
      generate_elem_f aLen (bn_sub1_f a) (i - 1) (generate_elems #uint64 #carry aLen (i - 1) (bn_sub1_f a) c_in));
    assert ((c_out, res) == generate_elem_f #uint64 #carry aLen (bn_sub1_f a) (i - 1) (c1, res1));
    bn_sub1_lemma_loop #aLen a c_in (i - 1);
    assert (bn_v #(i - 1) res1 - v c1 * pow2 (64 * (i - 1)) == eval_ aLen a (i - 1) - v c_in);
    bn_sub1_lemma_loop_step #aLen a c_in i (c1, res1);
    assert (bn_v #i res - v c_out * pow2 (64 * i) == eval_ aLen a i - v c_in);
    () end

val bn_sub1_lemma: #aLen:size_nat -> a:lbignum aLen -> c_in:carry ->
  Lemma
  (let (c_out, res) = bn_sub1 #aLen a c_in in
   bn_v res - v c_out * pow2 (64 * aLen) == bn_v a - v c_in)

let bn_sub1_lemma #aLen a c_in =
  let (c_out, res) = bn_sub1 #aLen a c_in in
  bn_sub1_lemma_loop #aLen a c_in aLen


val bn_sub_lemma_loop_step:
    #aLen:size_nat
  -> a:lbignum aLen
  -> b:lbignum aLen
  -> i:pos{i <= aLen}
  -> c1_res1:generate_elem_a uint64 carry aLen (i - 1)
  -> Lemma
  (requires
   (let (c1, res1) = c1_res1 in
    bn_v #(i - 1) res1 - v c1 * pow2 (64 * (i - 1)) == eval_ aLen a (i - 1) - eval_ aLen b (i - 1)))
  (ensures
   (let (c, res) = generate_elem_f #uint64 #carry aLen (bn_sub_f a b) (i - 1) c1_res1 in
    bn_v #i res - v c * pow2 (64 * i) == eval_ aLen a i - eval_ aLen b i))

let bn_sub_lemma_loop_step #aLen a b i (c1, res1) =
  let (c, res) = generate_elem_f #uint64 #carry aLen (bn_sub_f a b) (i - 1) (c1, res1) in
  let c, e = bn_sub_f a b (i - 1) c1 in
  assert (v e - v c * pow2 64 == v a.[i - 1] - v b.[i - 1] - v c1);

  calc (==) {
    bn_v #i res - v c * pow2 (64 * i);
    (==) { bn_eval_snoc #(i - 1) res1 e }
    bn_v #(i - 1) res1 + v e * pow2 (64 * (i - 1)) - v c * pow2 (64 * i);
    (==) { }
    eval_ aLen a (i - 1) - eval_ aLen b (i - 1) + (v a.[i - 1] - v b.[i - 1] + v c * pow2 64 - v e) * pow2 (64 * (i - 1)) + v e * pow2 (64 * (i - 1)) - v c * pow2 (64 * i);
    (==) { Math.Lemmas.distributivity_sub_left (v a.[i - 1] - v b.[i - 1] + v c * pow2 64) (v e) (pow2 (64 * (i - 1))) }
    eval_ aLen a (i - 1) - eval_ aLen b (i - 1) + (v a.[i - 1] - v b.[i - 1] + v c * pow2 64) * pow2 (64 * (i - 1)) - v c * pow2 (64 * i);
    (==) { Math.Lemmas.distributivity_add_left (v a.[i - 1] - v b.[i - 1]) (v c * pow2 64) (pow2 (64 * (i - 1))) }
    eval_ aLen a (i - 1) - eval_ aLen b (i - 1) + (v a.[i - 1] - v b.[i - 1]) * pow2 (64 * (i - 1)) + v c * pow2 64 * pow2 (64 * (i - 1)) - v c * pow2 (64 * i);
    (==) { Math.Lemmas.paren_mul_right (v c) (pow2 64) (pow2 (64 * (i - 1))); Math.Lemmas.pow2_plus 64 (64 * (i - 1)) }
    eval_ aLen a (i - 1) - eval_ aLen b (i - 1) + (v a.[i - 1] - v b.[i - 1]) * pow2 (64 * (i - 1));
    (==) { Math.Lemmas.distributivity_sub_left (v a.[i - 1]) (v b.[i - 1]) (pow2 (64 * (i - 1))) }
    eval_ aLen a (i - 1) - eval_ aLen b (i - 1) + v a.[i - 1] * pow2 (64 * (i - 1)) - v b.[i - 1] * pow2 (64 * (i - 1));
    (==) { bn_eval_unfold_i #aLen a i }
    eval_ aLen a i - eval_ aLen b (i - 1) - v b.[i - 1] * pow2 (64 * (i - 1));
    (==) { bn_eval_unfold_i #aLen b i }
    eval_ aLen a i - eval_ aLen b i;
  };
  assert (bn_v #i res - v c * pow2 (64 * i) == eval_ aLen a i - eval_ aLen b i)


val bn_sub_lemma_loop:
    #aLen:size_nat
  -> a:lbignum aLen
  -> b:lbignum aLen
  -> i:nat{i <= aLen} -> Lemma
  (let (c, res) : generate_elem_a uint64 carry aLen i = generate_elems #uint64 #carry aLen i (bn_sub_f a b) (u64 0) in
   bn_v #i res - v c * pow2 (64 * i) == eval_ aLen a i - eval_ aLen b i)

let rec bn_sub_lemma_loop #aLen a b i =
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
    bn_sub_lemma_loop #aLen a b (i - 1);
    assert (bn_v #(i - 1) res1 - v c1 * pow2 (64 * (i - 1)) == eval_ aLen a (i - 1) - eval_ aLen b (i - 1));
    bn_sub_lemma_loop_step #aLen a b i (c1, res1);
    assert (bn_v #i res - v c * pow2 (64 * i) == eval_ aLen a i - eval_ aLen b i);
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
  if bLen = aLen then
    bn_sub_lemma_loop #aLen a b aLen
  else begin
    let a0 = sub a 0 bLen in
    let a1 = sub a bLen (aLen - bLen) in

    let c0, res0 = generate_elems #uint64 #carry bLen bLen (bn_sub_f a0 b) (u64 0) in
    bn_sub_lemma_loop #bLen a0 b bLen;
    assert (bn_v #bLen res0 - v c0 * pow2 (64 * bLen) == eval_ bLen a0 bLen - eval_ bLen b bLen);
    let c1, res1 = bn_sub1 a1 c0 in
    bn_sub1_lemma a1 c0;
    assert (bn_v res1 - v c1 * pow2 (64 * (aLen - bLen)) == bn_v a1 - v c0);
    let res = concat #_ #bLen res0 res1 in
    eq_intro (slice res 0 bLen) res0;
    eq_intro (slice res bLen aLen) res1;
    bn_eval_split_i res bLen;
    assert (bn_v res == bn_v #bLen res0 + pow2 (64 * bLen) * bn_v res1);
    calc (==) {
      bn_v #bLen res0 + pow2 (64 * bLen) * bn_v res1;
      (==) { }
      eval_ bLen a0 bLen - eval_ bLen b bLen + v c0 * pow2 (64 * bLen) + pow2 (64 * bLen) * (bn_v a1 - v c0 + v c1 * pow2 (64 * (aLen - bLen)));
      (==) { Math.Lemmas.distributivity_sub_right (pow2 (64 * bLen)) (bn_v a1 + v c1 * pow2 (64 * (aLen - bLen))) (v c0) }
      eval_ bLen a0 bLen - eval_ bLen b bLen + v c0 * pow2 (64 * bLen) + pow2 (64 * bLen) * (bn_v a1 + v c1 * pow2 (64 * (aLen - bLen))) - pow2 (64 * bLen) * v c0;
      (==) { Math.Lemmas.distributivity_add_right (pow2 (64 * bLen)) (bn_v a1) (v c1 * pow2 (64 * (aLen - bLen))) }
      eval_ bLen a0 bLen - eval_ bLen b bLen + pow2 (64 * bLen) * bn_v a1 + pow2 (64 * bLen) * v c1 * pow2 (64 * (aLen - bLen));
      (==) { Math.Lemmas.paren_mul_right (pow2 (64 * bLen)) (v c1) (pow2 (64 * (aLen - bLen))); Math.Lemmas.pow2_plus (64 * bLen) (64 * (aLen - bLen)) }
      eval_ bLen a0 bLen - eval_ bLen b bLen + pow2 (64 * bLen) * bn_v a1 + v c1 * pow2 (64 * aLen);
      (==) { bn_eval_split_i a bLen; bn_eval_extensionality_j a (sub a 0 bLen) bLen }
      eval_ aLen a aLen - eval_ bLen b bLen + v c1 * pow2 (64 * aLen);
    }; () end
