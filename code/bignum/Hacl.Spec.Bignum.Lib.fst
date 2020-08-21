module Hacl.Spec.Bignum.Lib

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Bignum.Definitions

module BSeq = Lib.ByteSequence
module Loops = Lib.LoopCombinators

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

///
///  Get and set i-th bit of a bignum
///

val bn_get_ith_bit: #len:size_nat -> b:lbignum len -> i:size_nat{i / 64 < len} -> uint64
let bn_get_ith_bit #len input ind =
  let i = ind / 64 in
  let j = ind % 64 in
  (input.[i] >>. size j) &. u64 1

#push-options "--z3rlimit 100"
val bn_get_ith_bit_lemma: #len:size_nat -> b:lbignum len -> i:size_nat{i / 64 < len} ->
  Lemma (v (bn_get_ith_bit b i) == (bn_v b / pow2 i % 2))
let bn_get_ith_bit_lemma #len b ind =
  let i = ind / 64 in
  let j = ind % 64 in
  let tmp1 = b.[i] >>. size j in
  let tmp2 = tmp1 &. u64 1 in
  mod_mask_lemma tmp1 1ul;
  assert (v (mod_mask #U64 #SEC 1ul) == v (u64 1));
  assert (v tmp2 == v b.[i] / pow2 j % 2);

  calc (==) {
    v b.[i] / pow2 j % 2;
    (==) { bn_eval_index b i }
    (bn_v b / pow2 (64 * i) % pow2 64) / pow2 j % 2;
    (==) { Math.Lemmas.pow2_modulo_division_lemma_1 (bn_v b / pow2 (64 * i)) j 64 }
    (bn_v b / pow2 (64 * i) / pow2 j) % pow2 (64 - j) % 2;
    (==) { Math.Lemmas.pow2_modulo_modulo_lemma_1 (bn_v b / pow2 (64 * i) / pow2 j) 1 (64 - j) }
    (bn_v b / pow2 (64 * i) / pow2 j) % 2;
    (==) { Math.Lemmas.division_multiplication_lemma (bn_v b) (pow2 (64 * i)) (pow2 j) }
    (bn_v b / (pow2 (64 * i) * pow2 j)) % 2;
    (==) { Math.Lemmas.pow2_plus (64 * i) j }
    bn_v b / pow2 (64 * i + j) % 2;
    (==) { Math.Lemmas.euclidean_div_axiom ind 64 }
    bn_v b / pow2 ind % 2;
  };
  assert (v tmp2 == bn_v b / pow2 ind % 2)
#pop-options

val bn_set_ith_bit: #len:size_nat -> b:lbignum len -> i:size_nat{i / 64 < len} -> lbignum len
let bn_set_ith_bit #len input ind =
  let i = ind / 64 in
  let j = ind % 64 in
  let inp = input.[i] <- input.[i] |. (u64 1 <<. size j) in
  inp


val bn_set_ith_bit_lemma_aux: a:nat -> b:nat -> c:nat -> d:nat -> Lemma
  (requires a + b * pow2 c < pow2 (c + d) /\ a < pow2 c)
  (ensures  b < pow2 d)
let bn_set_ith_bit_lemma_aux a b c d =
  Math.Lemmas.lemma_div_lt_nat (a + b * pow2 c) (c + d) c;
  assert ((a + b * pow2 c) / pow2 c < pow2 d);
  Math.Lemmas.lemma_div_plus a b (pow2 c);
  assert (a / pow2 c + b < pow2 d);
  Math.Lemmas.small_division_lemma_1 a (pow2 c)


val bn_lt_pow2_index_lemma: #len:size_nat -> b:lbignum len -> ind:size_nat{ind / 64 < len} -> Lemma
  (requires bn_v b < pow2 ind)
  (ensures (let i = ind / 64 in v b.[ind / 64] < pow2 (ind % 64) /\
    bn_v b == bn_v (slice b 0 i) + pow2 (i * 64) * v b.[i] /\
    bn_v (slice b (i + 1) len) = 0))

let bn_lt_pow2_index_lemma #len b ind =
  let i = ind / 64 in
  let j = ind % 64 in

  Math.Lemmas.euclidean_division_definition ind 64;
  assert (bn_v b < pow2 (i * 64 + j));
  Math.Lemmas.pow2_lt_compat (i * 64 + 64) (i * 64 + j);
  assert (bn_v b < pow2 (i * 64 + 64));

  bn_eval_split_i #len b (i + 1);
  //assert (bn_v b == bn_v (slice b 0 (i + 1)) + pow2 (64 * (i + 1)) * bn_v (slice b (i + 1) len));
  bn_eval_bound (slice b 0 (i + 1)) (i + 1);
  //assert (bn_v (slice b 0 (i + 1)) < pow2 (64 * i + 64));
  bn_set_ith_bit_lemma_aux (bn_v (slice b 0 (i + 1))) (bn_v (slice b (i + 1) len)) (64 * (i + 1)) 0;
  assert (bn_v b == bn_v (slice b 0 (i + 1)));

  bn_eval_split_i #(i + 1) (slice b 0 (i + 1)) i;
  //assert (bn_v b == bn_v (slice b 0 i) + pow2 (i * 64) * bn_v (slice b i (i + 1)));
  bn_eval1 (slice b i (i + 1));
  assert (bn_v b == bn_v (slice b 0 i) + pow2 (i * 64) * v b.[i]);
  bn_eval_bound #i (slice b 0 i) i;
  bn_set_ith_bit_lemma_aux (bn_v (slice b 0 i)) (v b.[i]) (i * 64) j;
  assert (v b.[i] < pow2 j)


val bn_set_ith_bit_lemma: #len:size_nat -> b:lbignum len -> i:size_nat{i / 64 < len} -> Lemma
  (requires bn_v b < pow2 i)
  (ensures  bn_v (bn_set_ith_bit b i) == bn_v b + pow2 i)
let bn_set_ith_bit_lemma #len input ind =
  let i = ind / 64 in
  let j = ind % 64 in
  bn_lt_pow2_index_lemma #len input ind;
  assert (v input.[i] < pow2 j);

  let b = u64 1 <<. size j in
  let inp = input.[i] <- input.[i] |. b in
  FStar.Math.Lemmas.pow2_lt_compat 64 j;
  FStar.Math.Lemmas.modulo_lemma (pow2 j) (pow2 64);
  assert (v b == pow2 j);
  logor_disjoint (input.[i]) b j;
  assert (v inp.[i] == v input.[i] + v b);

  calc (==) {
    bn_v inp;
    (==) { bn_eval_split_i #len inp (i + 1);
    bn_eval_extensionality_j (slice inp (i + 1) len) (slice input (i + 1) len) (len - i - 1) }
    bn_v (slice inp 0 (i + 1));
    (==) { bn_eval_split_i #(i + 1) (slice inp 0 (i + 1)) i }
    bn_v (slice inp 0 i) + pow2 (i * 64) * bn_v (slice inp i (i + 1));
    (==) { bn_eval1 (slice inp i (i + 1)) }
    bn_v (slice inp 0 i) + pow2 (i * 64) * v inp.[i];
    (==) { bn_eval_extensionality_j input inp i }
    bn_v (slice input 0 i) + pow2 (i * 64) * v inp.[i];
    (==) { }
    bn_v (slice input 0 i) + pow2 (i * 64) * (v input.[i] + v b);
    (==) { Math.Lemmas.distributivity_add_right (pow2 (i * 64)) (v input.[i]) (v b) }
    bn_v (slice input 0 i) + pow2 (i * 64) * v input.[i] + pow2 (i * 64) * v b;
    (==) { Math.Lemmas.pow2_plus (i * 64) j; Math.Lemmas.euclidean_division_definition ind 64 }
    bn_v (slice input 0 i) + pow2 (i * 64) * v input.[i] + pow2 ind;
    (==) { }
    bn_v input + pow2 ind;
  }


///
///  % pow2 and / pow2
///

val bn_div_pow2: #len:size_nat -> b:lbignum len -> i:size_nat{i <= len} -> lbignum (len - i)
let bn_div_pow2 #len b i =
  slice b i len

val bn_div_pow2_lemma: #len:size_nat -> b:lbignum len -> i:size_nat{i < len} ->
  Lemma (bn_v (bn_div_pow2 b i) == bn_v b / pow2 (64 * i))
let bn_div_pow2_lemma #len c i =
  calc (==) {
    bn_v c / pow2 (64 * i);
    (==) { bn_eval_split_i c i }
    (bn_v (slice c 0 i) + pow2 (64 * i) * bn_v (slice c i len)) / pow2 (64 * i);
    (==) { Math.Lemmas.division_addition_lemma (bn_v (slice c 0 i)) (pow2 (64 * i)) (bn_v (slice c i len)) }
    bn_v (slice c 0 i) / pow2 (64 * i) + bn_v (slice c i len);
    (==) { bn_eval_bound (slice c 0 i) i; Math.Lemmas.small_division_lemma_1 (bn_v (slice c 0 i)) (pow2 (64 * i)) }
    bn_v (slice c i len);
  };
  assert (bn_v (slice c i len) == bn_v c / pow2 (64 * i))


val bn_mod_pow2: #aLen:size_nat -> a:lbignum aLen -> i:nat{i <= aLen} -> lbignum i
let bn_mod_pow2 #aLen a i = sub a 0 i

val bn_mod_pow2_lemma: #aLen:size_nat -> a:lbignum aLen -> i:nat{i <= aLen} ->
  Lemma (bn_v (bn_mod_pow2 a i) == bn_v a % pow2 (64 * i))
let bn_mod_pow2_lemma #aLen a i =
  calc (==) {
    bn_v a % pow2 (64 * i);
    (==) { bn_eval_split_i a i }
    (bn_v (slice a 0 i) + pow2 (64 * i) * bn_v (slice a i aLen)) % pow2 (64 * i);
    (==) { Math.Lemmas.modulo_addition_lemma (bn_v (slice a 0 i)) (pow2 (64 * i)) (bn_v (slice a i aLen)) }
    (bn_v (slice a 0 i)) % pow2 (64 * i);
    (==) { bn_eval_bound (slice a 0 i) i; Math.Lemmas.small_mod (bn_v (slice a 0 i)) (pow2 (64 * i)) }
    bn_v (slice a 0 i);
    }
