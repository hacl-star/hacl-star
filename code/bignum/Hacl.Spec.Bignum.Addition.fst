module Hacl.Spec.Bignum.Addition

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Bignum.Definitions
open Hacl.Spec.Bignum.Base
open Hacl.Spec.Lib


#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val bn_sub1_f: #t:limb_t -> #aLen:size_nat -> a:lbignum t aLen -> i:size_nat{i < aLen} -> c_in:carry t -> carry t & limb t
let bn_sub1_f #t #aLen a i c_in = subborrow c_in a.[i] (uint #t 0)

val bn_sub1: #t:limb_t -> #aLen:size_nat -> a:lbignum t aLen -> c_in:carry t -> tuple2 (carry t) (lbignum t aLen)
let bn_sub1 #t #aLen a c_in = generate_elems aLen aLen (bn_sub1_f a) c_in

val bn_sub_f: #t:limb_t -> #aLen:size_nat -> a:lbignum t aLen -> b:lbignum t aLen -> i:size_nat{i < aLen} -> c:carry t -> carry t & limb t
let bn_sub_f #t #aLen a b i c = subborrow c a.[i] b.[i]

val bn_sub: #t:limb_t -> #aLen:size_nat -> #bLen:size_nat{bLen <= aLen} -> a:lbignum t aLen -> b:lbignum t bLen -> tuple2 (carry t) (lbignum t aLen)
let bn_sub #t #aLen #bLen a b =
  let c0, res0 = generate_elems bLen bLen (bn_sub_f (sub a 0 bLen) b) (uint #t 0) in

  if bLen < aLen then
    let c1, res1 = bn_sub1 (sub a bLen (aLen - bLen)) c0 in
    c1, concat #_ #bLen res0 res1
  else c0, res0


val bn_add1_f: #t:limb_t -> #aLen:size_nat -> a:lbignum t aLen -> i:size_nat{i < aLen} -> c_in:carry t -> carry t & limb t
let bn_add1_f #t #aLen a i c_in = addcarry c_in a.[i] (uint #t 0)

val bn_add1: #t:limb_t -> #aLen:size_nat -> a:lbignum t aLen -> c_in:carry t -> tuple2 (carry t) (lbignum t aLen)
let bn_add1 #t #aLen a c_in = generate_elems aLen aLen (bn_add1_f a) c_in

val bn_add_f: #t:limb_t -> #aLen:size_nat -> a:lbignum t aLen -> b:lbignum t aLen -> i:size_nat{i < aLen} -> c:carry t -> carry t & limb t
let bn_add_f #t #aLen a b i c = addcarry c a.[i] b.[i]

val bn_add: #t:limb_t -> #aLen:size_nat -> #bLen:size_nat{bLen <= aLen} -> a:lbignum t aLen -> b:lbignum t bLen -> carry t & lbignum t aLen
let bn_add #t #aLen #bLen a b =
  let c0, res0 = generate_elems bLen bLen (bn_add_f (sub a 0 bLen) b) (uint #t 0) in

  if bLen < aLen then
    let c1, res1 = bn_add1 (sub a bLen (aLen - bLen)) c0 in
    c1, concat #_ #bLen res0 res1
  else c0, res0


val bn_add1_lemma_loop_step:
    #t:limb_t
  -> #aLen:size_nat
  -> a:lbignum t aLen
  -> c_in:carry t
  -> i:pos{i <= aLen}
  -> c1_res1:generate_elem_a (limb t) (carry t) aLen (i - 1) -> Lemma
  (requires
   (let (c1, res1) = c1_res1 in
    v c1 * pow2 (bits t * (i - 1)) + bn_v #t #(i - 1) res1 == eval_ aLen a (i - 1) + v c_in))
  (ensures
   (let (c_out, res) = generate_elem_f aLen (bn_add1_f a) (i - 1) c1_res1 in
    v c_out * pow2 (bits t * i) + bn_v #t #i res == eval_ aLen a i + v c_in))

let bn_add1_lemma_loop_step #t #aLen a c_in i (c1, res1) =
  let (c_out, res) = generate_elem_f aLen (bn_add1_f a) (i - 1) (c1, res1) in
  let c, e = bn_add1_f a (i - 1) c1 in
  assert (v e + v c * pow2 (bits t) == v a.[i - 1] + v c1);
  let pbits = bits t in

  calc (==) {
    v c * pow2 (pbits * i) + bn_v #t #i res;
    (==) { bn_eval_snoc #t #(i - 1) res1 e }
    v c * pow2 (pbits * i) + bn_v #t #(i - 1) res1 + v e * pow2 (pbits * (i - 1));
    (==) { }
    v c * pow2 (pbits * i) + eval_ aLen a (i - 1) + v c_in - (v e + v c * pow2 pbits - v a.[i - 1]) * pow2 (pbits * (i - 1)) + v e * pow2 (pbits * (i - 1));
    (==) { Math.Lemmas.distributivity_sub_left (v e) (v e + v c * pow2 pbits - v a.[i - 1]) (pow2 (pbits * (i - 1))) }
    v c * pow2 (pbits * i) + eval_ aLen a (i - 1) + v c_in + (v e - v e - v c * pow2 pbits + v a.[i - 1]) * pow2 (pbits * (i - 1));
    (==) { Math.Lemmas.distributivity_sub_left (v a.[i - 1]) (v c * pow2 pbits) (pow2 (pbits * (i - 1))) }
    v c * pow2 (pbits * i) + eval_ aLen a (i - 1) + v c_in + v a.[i - 1] * pow2 (pbits * (i - 1)) - v c * pow2 pbits * pow2 (pbits * (i - 1));
    (==) { Math.Lemmas.paren_mul_right (v c) (pow2 pbits) (pow2 (pbits * (i - 1))); Math.Lemmas.pow2_plus pbits (pbits * (i - 1)) }
    eval_ aLen a (i - 1) + v c_in + v a.[i - 1] * pow2 (pbits * (i - 1));
    (==) { bn_eval_unfold_i #t #aLen a i }
    eval_ aLen a i + v c_in;
  };
  assert (v c * pow2 (pbits * i) + bn_v #t #i res == eval_ aLen a i + v c_in)


val bn_add1_lemma_loop:
    #t:limb_t
  -> #aLen:size_nat
  -> a:lbignum t aLen
  -> c_in:carry t
  -> i:nat{i <= aLen} ->
  Lemma (let (c_out, res) : generate_elem_a (limb t) (carry t) aLen i = generate_elems aLen i (bn_add1_f a) c_in in
   v c_out * pow2 (bits t * i) + bn_v #t #i res == eval_ aLen a i + v c_in)

let rec bn_add1_lemma_loop #t #aLen a c_in i =
  let pbits = bits t in
  let (c_out, res) : generate_elem_a (limb t) (carry t) aLen i = generate_elems aLen i (bn_add1_f a) c_in in
  if i = 0 then begin
    eq_generate_elems0 aLen i (bn_add1_f a) c_in;
    assert (c_out == c_in /\ res == Seq.empty);
    bn_eval0 #t #0 res;
    assert_norm (pow2 0 = 1);
    bn_eval0 a;
    () end
  else begin
    let (c1, res1) : generate_elem_a (limb t) (carry t) aLen (i - 1) = generate_elems aLen (i - 1) (bn_add1_f a) c_in in
    generate_elems_unfold aLen i (bn_add1_f a) c_in (i - 1);
    assert (generate_elems aLen i (bn_add1_f a) c_in ==
      generate_elem_f aLen (bn_add1_f a) (i - 1) (generate_elems aLen (i - 1) (bn_add1_f a) c_in));
    assert ((c_out, res) == generate_elem_f aLen (bn_add1_f a) (i - 1) (c1, res1));
    bn_add1_lemma_loop a c_in (i - 1);
    assert (v c1 * pow2 (pbits * (i - 1)) + bn_v #t #(i - 1) res1 == eval_ aLen a (i - 1) + v c_in);
    bn_add1_lemma_loop_step a c_in i (c1, res1);
    assert (v c_out * pow2 (pbits * i) + bn_v #t #i res == eval_ aLen a i + v c_in);
    () end


val bn_add1_lemma: #t:limb_t -> #aLen:size_nat -> a:lbignum t aLen -> c_in:carry t ->
  Lemma (let (c_out, res) = bn_add1 a c_in in
   v c_out * pow2 (bits t * aLen) + bn_v res == bn_v a + v c_in)

let bn_add1_lemma #t #aLen a c_in =
  let (c_out, res) = bn_add1 a c_in in
  bn_add1_lemma_loop a c_in aLen


val bn_add_lemma_loop_step:
    #t:limb_t
  -> #aLen:size_nat
  -> a:lbignum t aLen
  -> b:lbignum t aLen
  -> i:pos{i <= aLen}
  -> c1_res1:generate_elem_a (limb t) (carry t) aLen (i - 1) -> Lemma
  (requires
   (let (c1, res1) = c1_res1 in
    v c1 * pow2 (bits t * (i - 1)) + bn_v #t #(i - 1) res1 == eval_ aLen a (i - 1) + eval_ aLen b (i - 1)))
  (ensures
   (let (c1, res1) = c1_res1 in
    let (c, res) = generate_elem_f aLen (bn_add_f a b) (i - 1) (c1, res1) in
    v c * pow2 (bits t * i) + bn_v #t #i res == eval_ aLen a i + eval_ aLen b i))

let bn_add_lemma_loop_step #t #aLen a b i (c1, res1) =
  let pbits = bits t in
  let (c, res) = generate_elem_f aLen (bn_add_f a b) (i - 1) (c1, res1) in
  let c, e = bn_add_f a b (i - 1) c1 in
  assert (v e + v c * pow2 pbits == v a.[i - 1] + v b.[i - 1] + v c1);

  calc (==) {
    v c * pow2 (pbits * i) + bn_v #t #i res;
    (==) { bn_eval_snoc #t #(i - 1) res1 e }
    v c * pow2 (pbits * i) + bn_v #t #(i - 1) res1 + v e * pow2 (pbits * (i - 1));
    (==) { }
    v c * pow2 (pbits * i) + eval_ aLen a (i - 1) + eval_ aLen b (i - 1) - (v e + v c * pow2 pbits - v a.[i - 1] - v b.[i - 1]) * pow2 (pbits * (i - 1)) + v e * pow2 (pbits * (i - 1));
    (==) { Math.Lemmas.distributivity_sub_left (v e) (v e + v c * pow2 pbits - v a.[i - 1] - v b.[i - 1]) (pow2 (pbits * (i - 1))) }
    v c * pow2 (pbits * i) + eval_ aLen a (i - 1) + eval_ aLen b (i - 1) + (v e - v e - v c * pow2 pbits + v a.[i - 1] + v b.[i - 1]) * pow2 (pbits * (i - 1));
    (==) { Math.Lemmas.distributivity_sub_left (v a.[i - 1] + v b.[i - 1]) (v c1 * pow2 pbits) (pow2 (pbits * (i - 1))) }
    v c * pow2 (pbits * i) + eval_ aLen a (i - 1) + eval_ aLen b (i - 1) + (v a.[i - 1] + v b.[i - 1]) * pow2 (pbits * (i - 1)) - v c * pow2 pbits * pow2 (pbits * (i - 1));
    (==) { Math.Lemmas.paren_mul_right (v c) (pow2 pbits) (pow2 (pbits * (i - 1))); Math.Lemmas.pow2_plus pbits (pbits * (i - 1)) }
    eval_ aLen a (i - 1) + eval_ aLen b (i - 1) + (v a.[i - 1] + v b.[i - 1]) * pow2 (pbits * (i - 1));
    (==) { Math.Lemmas.distributivity_add_left (v a.[i - 1]) (v b.[i - 1]) (pow2 (pbits * (i - 1))) }
    eval_ aLen a (i - 1) + eval_ aLen b (i - 1) + v a.[i - 1] * pow2 (pbits * (i - 1)) + v b.[i - 1] * pow2 (pbits * (i - 1));
    (==) { bn_eval_unfold_i #t #aLen a i }
    eval_ aLen a i + eval_ aLen b (i - 1) + v b.[i - 1] * pow2 (pbits * (i - 1));
    (==) { bn_eval_unfold_i #t #aLen b i }
    eval_ aLen a i + eval_ aLen b i;
  };
  assert (v c * pow2 (pbits * i) + bn_v #t #i res == eval_ aLen a i + eval_ aLen b i)


val bn_add_lemma_loop:
    #t:limb_t
  -> #aLen:size_nat
  -> a:lbignum t aLen
  -> b:lbignum t aLen
  -> i:nat{i <= aLen} ->
  Lemma (let (c, res) : generate_elem_a (limb t) (carry t) aLen i = generate_elems aLen i (bn_add_f a b) (uint #t 0) in
   v c * pow2 (bits t * i) + bn_v #t #i res == eval_ aLen a i + eval_ aLen b i)

let rec bn_add_lemma_loop #t #aLen a b i =
  let pbits = bits t in
  let (c, res) : generate_elem_a (limb t) (carry t) aLen i = generate_elems aLen i (bn_add_f a b) (uint #t 0) in
  if i = 0 then begin
    eq_generate_elems0 aLen i (bn_add_f a b) (uint #t 0);
    assert (c == uint #t 0 /\ res == Seq.empty);
    bn_eval0 #t #0 res;
    assert_norm (pow2 0 = 1);
    bn_eval0 a;
    bn_eval0 b;
    () end
  else begin
    let (c1, res1) : generate_elem_a (limb t) (carry t) aLen (i - 1) = generate_elems aLen (i - 1) (bn_add_f a b) (uint #t 0) in
    generate_elems_unfold aLen i (bn_add_f a b) (uint #t 0) (i - 1);
    assert (generate_elems aLen i (bn_add_f a b) (uint #t 0) ==
      generate_elem_f aLen (bn_add_f a b) (i - 1) (generate_elems aLen (i - 1) (bn_add_f a b) (uint #t 0)));
    assert ((c, res) == generate_elem_f aLen (bn_add_f a b) (i - 1) (c1, res1));
    bn_add_lemma_loop a b (i - 1);
    assert (v c1 * pow2 (pbits * (i - 1)) + bn_v #t #(i - 1) res1 == eval_ aLen a (i - 1) + eval_ aLen b (i - 1));
    bn_add_lemma_loop_step a b i (c1, res1);
    assert (v c * pow2 (pbits * i) + bn_v #t #i res == eval_ aLen a i + eval_ aLen b i);
    () end


val bn_add_lemma:
    #t:limb_t
  -> #aLen:size_nat
  -> #bLen:size_nat{bLen <= aLen}
  -> a:lbignum t aLen
  -> b:lbignum t bLen ->
  Lemma (let (c, res) = bn_add a b in
   v c * pow2 (bits t * aLen) + bn_v res == bn_v a + bn_v b)

let bn_add_lemma #t #aLen #bLen a b =
  let pbits = bits t in
  let (c, res) = bn_add a b in
  if bLen = aLen then
    bn_add_lemma_loop a b aLen
  else begin
    let a0 = sub a 0 bLen in
    let a1 = sub a bLen (aLen - bLen) in

    let c0, res0 = generate_elems bLen bLen (bn_add_f a0 b) (uint #t 0) in
    bn_add_lemma_loop a0 b bLen;
    assert (v c0 * pow2 (pbits * bLen) + bn_v #t #bLen res0 == eval_ bLen a0 bLen + eval_ bLen b bLen);
    let c1, res1 = bn_add1 a1 c0 in
    bn_add1_lemma a1 c0;
    assert (v c1 * pow2 (pbits * (aLen - bLen)) + bn_v res1 == bn_v a1 + v c0);
    let res = concat #_ #bLen res0 res1 in
    eq_intro (slice res 0 bLen) res0;
    eq_intro (slice res bLen aLen) res1;
    bn_eval_split_i res bLen;
    assert (bn_v res == bn_v #t #bLen res0 + pow2 (pbits * bLen) * bn_v res1);
    calc (==) {
      bn_v #t #bLen res0 + pow2 (pbits * bLen) * bn_v res1;
      (==) { }
      eval_ bLen a0 bLen + eval_ bLen b bLen - v c0 * pow2 (pbits * bLen) + pow2 (pbits * bLen) * (bn_v a1 + v c0 - v c1 * pow2 (pbits * (aLen - bLen)));
      (==) { Math.Lemmas.distributivity_sub_right (pow2 (pbits * bLen)) (bn_v a1 + v c0) (v c1 * pow2 (pbits * (aLen - bLen))) }
      eval_ bLen a0 bLen + eval_ bLen b bLen - v c0 * pow2 (pbits * bLen) + pow2 (pbits * bLen) * (bn_v a1 + v c0) - pow2 (pbits * bLen) * v c1 * pow2 (pbits * (aLen - bLen));
      (==) { Math.Lemmas.paren_mul_right (pow2 (pbits * bLen)) (v c1) (pow2 (pbits * (aLen - bLen))); Math.Lemmas.pow2_plus (pbits * bLen) (pbits * (aLen - bLen)) }
      eval_ bLen a0 bLen + eval_ bLen b bLen - v c0 * pow2 (pbits * bLen) + pow2 (pbits * bLen) * (bn_v a1 + v c0) - v c1 * pow2 (pbits * aLen);
      (==) { Math.Lemmas.distributivity_sub_right (pow2 (pbits * bLen)) (bn_v a1) (v c0) }
      eval_ bLen a0 bLen + eval_ bLen b bLen + pow2 (pbits * bLen) * bn_v a1 - v c1 * pow2 (pbits * aLen);
      (==) { bn_eval_split_i a bLen; bn_eval_extensionality_j a (sub a 0 bLen) bLen }
      eval_ aLen a aLen + eval_ bLen b bLen  - v c1 * pow2 (pbits * aLen);
    }; () end


val bn_sub1_lemma_loop_step:
    #t:limb_t
  -> #aLen:size_nat
  -> a:lbignum t aLen
  -> c_in:carry t
  -> i:pos{i <= aLen}
  -> c1_res1:generate_elem_a (limb t) (carry t) aLen (i - 1) -> Lemma
  (requires
   (let (c1, res1) = c1_res1 in
    bn_v #t #(i - 1) res1 - v c1 * pow2 (bits t * (i - 1)) == eval_ aLen a (i - 1) - v c_in))
  (ensures
   (let (c_out, res) = generate_elem_f aLen (bn_sub1_f a) (i - 1) c1_res1 in
    bn_v #t #i res - v c_out * pow2 (bits t * i) == eval_ aLen a i - v c_in))

let bn_sub1_lemma_loop_step #t #aLen a c_in i (c1, res1) =
  let pbits = bits t in
  let (c_out, res) = generate_elem_f aLen (bn_sub1_f a) (i - 1) (c1, res1) in
  let c, e = bn_sub1_f a (i - 1) c1 in
  assert (v e - v c * pow2 pbits == v a.[i - 1] - v c1);

  calc (==) {
    bn_v #t #i res - v c * pow2 (pbits * i);
    (==) { bn_eval_snoc #t #(i - 1) res1 e }
    bn_v #t #(i - 1) res1 + v e * pow2 (pbits * (i - 1)) - v c * pow2 (pbits * i);
    (==) { }
    eval_ aLen a (i - 1) - v c_in + (v a.[i - 1] - v e + v c * pow2 pbits) * pow2 (pbits * (i - 1)) + v e * pow2 (pbits * (i - 1)) - v c * pow2 (pbits * i);
    (==) { Math.Lemmas.distributivity_sub_left (v a.[i - 1] + v c * pow2 pbits) (v e) (pow2 (pbits * (i - 1))) }
    eval_ aLen a (i - 1) - v c_in + (v a.[i - 1] + v c * pow2 pbits) * pow2 (pbits * (i - 1)) - v c * pow2 (pbits * i);
    (==) { Math.Lemmas.distributivity_add_left (v a.[i - 1]) (v c * pow2 pbits) (pow2 (pbits * (i - 1))) }
    eval_ aLen a (i - 1) - v c_in + v a.[i - 1] * pow2 (pbits * (i - 1)) + v c * pow2 pbits * pow2 (pbits * (i - 1)) - v c * pow2 (pbits * i);
    (==) { Math.Lemmas.paren_mul_right (v c) (pow2 pbits) (pow2 (pbits * (i - 1))); Math.Lemmas.pow2_plus pbits (pbits * (i - 1)) }
    eval_ aLen a (i - 1) - v c_in + v a.[i - 1] * pow2 (pbits * (i - 1));
    (==) { bn_eval_unfold_i a i }
    eval_ aLen a i - v c_in;
  };
  assert (bn_v #t #i res - v c * pow2 (pbits * i) == eval_ aLen a i - v c_in)


val bn_sub1_lemma_loop:
    #t:limb_t
  -> #aLen:size_nat
  -> a:lbignum t aLen
  -> c_in:carry t
  -> i:nat{i <= aLen} ->
  Lemma (let (c_out, res) : generate_elem_a (limb t) (carry t) aLen i = generate_elems aLen i (bn_sub1_f a) c_in in
   bn_v #t #i res - v c_out * pow2 (bits t * i) == eval_ aLen a i - v c_in)

let rec bn_sub1_lemma_loop #t #aLen a c_in i =
  let pbits = bits t in
  let (c_out, res) : generate_elem_a (limb t) (carry t) aLen i = generate_elems aLen i (bn_sub1_f a) c_in in
  if i = 0 then begin
    eq_generate_elems0  aLen i (bn_sub1_f a) c_in;
    assert (c_out == c_in /\ res == Seq.empty);
    bn_eval0 #t #0 res;
    assert_norm (pow2 0 = 1);
    bn_eval0 a;
    () end
  else begin
    let (c1, res1) : generate_elem_a (limb t) (carry t) aLen (i - 1) = generate_elems aLen (i - 1) (bn_sub1_f a) c_in in
    generate_elems_unfold aLen i (bn_sub1_f a) c_in (i - 1);
    assert (generate_elems aLen i (bn_sub1_f a) c_in ==
      generate_elem_f aLen (bn_sub1_f a) (i - 1) (generate_elems aLen (i - 1) (bn_sub1_f a) c_in));
    assert ((c_out, res) == generate_elem_f  aLen (bn_sub1_f a) (i - 1) (c1, res1));
    bn_sub1_lemma_loop a c_in (i - 1);
    assert (bn_v #t #(i - 1) res1 - v c1 * pow2 (pbits * (i - 1)) == eval_ aLen a (i - 1) - v c_in);
    bn_sub1_lemma_loop_step a c_in i (c1, res1);
    assert (bn_v #t #i res - v c_out * pow2 (pbits * i) == eval_ aLen a i - v c_in);
    () end


val bn_sub1_lemma: #t:limb_t -> #aLen:size_nat -> a:lbignum t aLen -> c_in:carry t ->
  Lemma (let (c_out, res) = bn_sub1 a c_in in
   bn_v res - v c_out * pow2 (bits t * aLen) == bn_v a - v c_in)

let bn_sub1_lemma #t #aLen a c_in =
  let (c_out, res) = bn_sub1 a c_in in
  bn_sub1_lemma_loop a c_in aLen


val bn_sub_lemma_loop_step:
   #t:limb_t
  -> #aLen:size_nat
  -> a:lbignum t aLen
  -> b:lbignum t aLen
  -> i:pos{i <= aLen}
  -> c1_res1:generate_elem_a (limb t) (carry t) aLen (i - 1) -> Lemma
  (requires
   (let (c1, res1) = c1_res1 in
    bn_v #t #(i - 1) res1 - v c1 * pow2 (bits t * (i - 1)) == eval_ aLen a (i - 1) - eval_ aLen b (i - 1)))
  (ensures
   (let (c, res) = generate_elem_f aLen (bn_sub_f a b) (i - 1) c1_res1 in
    bn_v #t #i res - v c * pow2 (bits t * i) == eval_ aLen a i - eval_ aLen b i))

let bn_sub_lemma_loop_step #t #aLen a b i (c1, res1) =
  let pbits = bits t in
  let (c, res) = generate_elem_f aLen (bn_sub_f a b) (i - 1) (c1, res1) in
  let c, e = bn_sub_f a b (i - 1) c1 in
  assert (v e - v c * pow2 pbits == v a.[i - 1] - v b.[i - 1] - v c1);

  calc (==) {
    bn_v #t #i res - v c * pow2 (pbits * i);
    (==) { bn_eval_snoc #t #(i - 1) res1 e }
    bn_v #t #(i - 1) res1 + v e * pow2 (pbits * (i - 1)) - v c * pow2 (pbits * i);
    (==) { }
    eval_ aLen a (i - 1) - eval_ aLen b (i - 1) + (v a.[i - 1] - v b.[i - 1] + v c * pow2 pbits - v e) * pow2 (pbits * (i - 1)) + v e * pow2 (pbits * (i - 1)) - v c * pow2 (pbits * i);
    (==) { Math.Lemmas.distributivity_sub_left (v a.[i - 1] - v b.[i - 1] + v c * pow2 pbits) (v e) (pow2 (pbits * (i - 1))) }
    eval_ aLen a (i - 1) - eval_ aLen b (i - 1) + (v a.[i - 1] - v b.[i - 1] + v c * pow2 pbits) * pow2 (pbits * (i - 1)) - v c * pow2 (pbits * i);
    (==) { Math.Lemmas.distributivity_add_left (v a.[i - 1] - v b.[i - 1]) (v c * pow2 pbits) (pow2 (pbits * (i - 1))) }
    eval_ aLen a (i - 1) - eval_ aLen b (i - 1) + (v a.[i - 1] - v b.[i - 1]) * pow2 (pbits * (i - 1)) + v c * pow2 pbits * pow2 (pbits * (i - 1)) - v c * pow2 (pbits * i);
    (==) { Math.Lemmas.paren_mul_right (v c) (pow2 pbits) (pow2 (pbits * (i - 1))); Math.Lemmas.pow2_plus pbits (pbits * (i - 1)) }
    eval_ aLen a (i - 1) - eval_ aLen b (i - 1) + (v a.[i - 1] - v b.[i - 1]) * pow2 (pbits * (i - 1));
    (==) { Math.Lemmas.distributivity_sub_left (v a.[i - 1]) (v b.[i - 1]) (pow2 (pbits * (i - 1))) }
    eval_ aLen a (i - 1) - eval_ aLen b (i - 1) + v a.[i - 1] * pow2 (pbits * (i - 1)) - v b.[i - 1] * pow2 (pbits * (i - 1));
    (==) { bn_eval_unfold_i a i }
    eval_ aLen a i - eval_ aLen b (i - 1) - v b.[i - 1] * pow2 (pbits * (i - 1));
    (==) { bn_eval_unfold_i b i }
    eval_ aLen a i - eval_ aLen b i;
  };
  assert (bn_v #t #i res - v c * pow2 (pbits * i) == eval_ aLen a i - eval_ aLen b i)


val bn_sub_lemma_loop:
    #t:limb_t
  -> #aLen:size_nat
  -> a:lbignum t aLen
  -> b:lbignum t aLen
  -> i:nat{i <= aLen} ->
  Lemma (let (c, res) : generate_elem_a (limb t) (carry t) aLen i = generate_elems aLen i (bn_sub_f a b) (uint #t 0) in
   bn_v #t #i res - v c * pow2 (bits t * i) == eval_ aLen a i - eval_ aLen b i)

let rec bn_sub_lemma_loop #t #aLen a b i =
  let (c, res) : generate_elem_a (limb t) (carry t) aLen i = generate_elems aLen i (bn_sub_f a b) (uint #t 0) in
  if i = 0 then begin
    eq_generate_elems0 aLen i (bn_sub_f a b) (uint #t 0);
    assert (c == uint #t 0 /\ res == Seq.empty);
    bn_eval0 #t #0 res;
    assert_norm (pow2 0 = 1);
    bn_eval0 a;
    bn_eval0 b;
    () end
  else begin
    let (c1, res1) : generate_elem_a (limb t) (carry t) aLen (i - 1) = generate_elems aLen (i - 1) (bn_sub_f a b) (uint #t 0) in
    generate_elems_unfold aLen i (bn_sub_f a b) (uint #t 0) (i - 1);
    assert (generate_elems aLen i (bn_sub_f a b) (uint #t 0) ==
      generate_elem_f aLen (bn_sub_f a b) (i - 1) (generate_elems aLen (i - 1) (bn_sub_f a b) (uint #t 0)));
    assert ((c, res) == generate_elem_f aLen (bn_sub_f a b) (i - 1) (c1, res1));
    bn_sub_lemma_loop a b (i - 1);
    assert (bn_v #t #(i - 1) res1 - v c1 * pow2 (bits t * (i - 1)) == eval_ aLen a (i - 1) - eval_ aLen b (i - 1));
    bn_sub_lemma_loop_step a b i (c1, res1);
    assert (bn_v #t #i res - v c * pow2 (bits t * i) == eval_ aLen a i - eval_ aLen b i);
    () end


val bn_sub_lemma:
    #t:limb_t
  -> #aLen:size_nat
  -> #bLen:size_nat{bLen <= aLen}
  -> a:lbignum t aLen
  -> b:lbignum t bLen ->
  Lemma (let (c, res) = bn_sub a b in
   bn_v res - v c * pow2 (bits t * aLen) == bn_v a - bn_v b)

let bn_sub_lemma #t #aLen #bLen a b =
  let pbits = bits t in
  let (c, res) = bn_sub a b in
  if bLen = aLen then
    bn_sub_lemma_loop a b aLen
  else begin
    let a0 = sub a 0 bLen in
    let a1 = sub a bLen (aLen - bLen) in

    let c0, res0 = generate_elems bLen bLen (bn_sub_f a0 b) (uint #t 0) in
    bn_sub_lemma_loop a0 b bLen;
    assert (bn_v #t #bLen res0 - v c0 * pow2 (pbits * bLen) == eval_ bLen a0 bLen - eval_ bLen b bLen);
    let c1, res1 = bn_sub1 a1 c0 in
    bn_sub1_lemma a1 c0;
    assert (bn_v res1 - v c1 * pow2 (pbits * (aLen - bLen)) == bn_v a1 - v c0);
    let res = concat #_ #bLen res0 res1 in
    eq_intro (slice res 0 bLen) res0;
    eq_intro (slice res bLen aLen) res1;
    bn_eval_split_i res bLen;
    assert (bn_v res == bn_v #t #bLen res0 + pow2 (pbits * bLen) * bn_v res1);
    calc (==) {
      bn_v #t #bLen res0 + pow2 (pbits * bLen) * bn_v res1;
      (==) { }
      eval_ bLen a0 bLen - eval_ bLen b bLen + v c0 * pow2 (pbits * bLen) + pow2 (pbits * bLen) * (bn_v a1 - v c0 + v c1 * pow2 (pbits * (aLen - bLen)));
      (==) { Math.Lemmas.distributivity_sub_right (pow2 (pbits * bLen)) (bn_v a1 + v c1 * pow2 (pbits * (aLen - bLen))) (v c0) }
      eval_ bLen a0 bLen - eval_ bLen b bLen + v c0 * pow2 (pbits * bLen) + pow2 (pbits * bLen) * (bn_v a1 + v c1 * pow2 (pbits * (aLen - bLen))) - pow2 (pbits * bLen) * v c0;
      (==) { Math.Lemmas.distributivity_add_right (pow2 (pbits * bLen)) (bn_v a1) (v c1 * pow2 (pbits * (aLen - bLen))) }
      eval_ bLen a0 bLen - eval_ bLen b bLen + pow2 (pbits * bLen) * bn_v a1 + pow2 (pbits * bLen) * v c1 * pow2 (pbits * (aLen - bLen));
      (==) { Math.Lemmas.paren_mul_right (pow2 (pbits * bLen)) (v c1) (pow2 (pbits * (aLen - bLen))); Math.Lemmas.pow2_plus (pbits * bLen) (pbits * (aLen - bLen)) }
      eval_ bLen a0 bLen - eval_ bLen b bLen + pow2 (pbits * bLen) * bn_v a1 + v c1 * pow2 (pbits * aLen);
      (==) { bn_eval_split_i a bLen; bn_eval_extensionality_j a (sub a 0 bLen) bLen }
      eval_ aLen a aLen - eval_ bLen b bLen + v c1 * pow2 (pbits * aLen);
    }; () end
