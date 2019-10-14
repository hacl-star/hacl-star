module Hacl.Spec.Bignum

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence


#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

val blocks: x: size_pos -> m: size_pos -> Tot (r:size_pos{x <= m * r})
let blocks x m = (x - 1) / m + 1


let lbignum len = lseq uint64 len

val eval_: len:size_nat -> s:lbignum len -> i:nat{i <= len} -> nat
let rec eval_ len s i =
  if i = 0 then 0
  else eval_ len s (i - 1) + v s.[i - 1] * pow2 (64 * (i - 1))

let bn_v (#len:size_nat) (s:lbignum len) = eval_ len s len


#set-options "--max_fuel 2"
val bn_eval0: #len:size_nat -> b:lbignum len -> Lemma (eval_ len b 0 == 0)
let bn_eval0 #len b = ()


val bn_eval_unfold_i: #len:size_pos -> b:lbignum len -> i:pos{i <= len} -> Lemma
  (eval_ len b i == eval_ len b (i - 1) + v b.[i - 1] * pow2 (64 * (i - 1)))
let bn_eval_unfold_i #len b i = ()


val bval: #len:size_nat -> b:lbignum len -> i:size_nat -> uint64
let bval #len b i = if i < len then b.[i] else u64 0

val eval_bval: len:size_nat -> b:lbignum len -> i:nat -> nat
let eval_bval len b i =
  if i > len then eval_ len b len
  else eval_ len b i


val bn_eval_bval_unfold_i: #len:size_nat -> b:lbignum len -> i:pos -> Lemma
  (let bi1 = if i - 1 < len then b.[i - 1] else u64 0 in
   eval_bval len b i == eval_bval len b (i - 1) + v bi1 * pow2 (64 * (i - 1)))
let rec bn_eval_bval_unfold_i #len b i =
  if i = 1 then () else begin
    if i > len then bn_eval_bval_unfold_i #len b (i - 1)
    else bn_eval_unfold_i #len b i end


val bn_eval_sub1: #len:size_pos -> b:lbignum len -> i:nat{i < len} -> Lemma
  (eval_ len b i == eval_ (len - 1) (sub b 0 (len - 1)) i)
let rec bn_eval_sub1 #len b i =
  if i = 0 then () else bn_eval_sub1 #len b (i - 1)

val bn_eval_snoc: #len:size_nat{len + 1 <= max_size_t} -> b:lbignum len -> e:uint64 -> Lemma
  (bn_v #(len + 1) (Seq.snoc b e) == bn_v #len b + v e * pow2 (64 * len))
let bn_eval_snoc #len b e =
  let b1 = Seq.snoc b e in
  bn_eval_unfold_i #(len + 1) b1 (len + 1);
  bn_eval_sub1 #(len + 1) b1 len;
  eq_intro (sub #uint64 #(len + 1) b1 0 len) b


val bn_eval_zeroes: #len:size_nat -> b:lbignum len -> i:nat{i <= len} -> Lemma
  (requires b == create len (u64 0))
  (ensures eval_ len b i == 0)

let rec bn_eval_zeroes #len b i =
  if i = 0 then ()
  else bn_eval_zeroes #len b (i - 1)


val bn_eval_create1: c:uint64 -> Lemma (bn_v (create 1 c) == v c)
let bn_eval_create1 c =
  bn_eval_unfold_i (create 1 c) 1;
  bn_eval0 (create 1 c)


val bn_eval_extensionality_j:
    #len1:size_nat
  -> #len2:size_nat
  -> b1:lbignum len1
  -> b2:lbignum len2
  -> j:nat{j <= len1 /\ j <= len2} ->
  Lemma
    (requires sub b1 0 j == sub b2 0 j)
    (ensures  eval_ len1 b1 j == eval_ len2 b2 j)
    (decreases j)

let rec bn_eval_extensionality_j #len1 #len2 b1 b2 j =
  if j = 0 then ()
  else begin
    let b1j = slice b1 0 j in
    let b2j = slice b2 0 j in
    let c1 = slice b1j 0 (j - 1) in
    let c2 = slice b2j 0 (j - 1) in
    eq_intro c1 c2;
    bn_eval_extensionality_j #len1 #len2 b1 b2 (j - 1);
    Seq.lemma_index_slice b1 0 j (j - 1);
    Seq.lemma_index_slice b2 0 j (j - 1);
    assert (v b1.[j - 1] == v b2.[j - 1]);
    () end


// val bn_eval_sub: #len:size_nat -> b:lbignum len -> j:nat{j <= len} -> Lemma
//   (eval_ len b j == eval_ j (sub b 0 j) j)
// let bn_eval_sub #len b j =
//   bn_eval_extensionality_j #len #j b (sub b 0 j) j


val bn_eval_split_i_lemma_aux: a:nat -> b:nat -> c:nat -> i:nat -> Lemma
  (requires pow2 64 * c == a - b)
  (ensures pow2 (64 * (i + 1)) * c == pow2 (64 * i) * a - pow2 (64 * i) * b)

let bn_eval_split_i_lemma_aux a b c i =
  calc (==) {
    pow2 (64 * (i + 1)) * c;
    (==) { Math.Lemmas.pow2_plus (64 * i) 64 }
    pow2 (64 * i) * pow2 64 * c;
    (==) { Math.Lemmas.paren_mul_right (pow2 (64 * i)) (pow2 64) c }
    pow2 (64 * i) * (pow2 64 * c);
    (==) { }
    pow2 (64 * i) * (a - b);
    (==) { Math.Lemmas.distributivity_sub_right (pow2 (64 * i)) a b }
    pow2 (64 * i) * a - pow2 (64 * i) * b;
  }


val bn_eval_split_i: #len:size_nat -> b:lbignum len -> i:nat{i <= len} -> Lemma
  (ensures bn_v b == bn_v (slice b 0 i) + pow2 (64 * i) * bn_v (slice b i len))
  (decreases (len - i))

let rec bn_eval_split_i #len b i =
  if i = 0 then ()
  else begin
    if len = i then ()
    else begin
      let b1 = slice b i len in
      bn_eval_split_i b1 1;
      assert (bn_v b1 == v b1.[0] + pow2 64 * bn_v (slice b1 1 (len - i)));
      Seq.lemma_index_slice b i len 0;
      assert (bn_v b1 == v b.[i] + pow2 64 * bn_v (slice b (i + 1) len));
      calc (==) {
        bn_v b;
        (==) { bn_eval_split_i b (i + 1) }
        bn_v (slice b 0 (i + 1)) + pow2 (64 * (i + 1)) * bn_v (slice b (i + 1) len);
        (==) { bn_eval_split_i_lemma_aux (bn_v b1) (v b.[i]) (bn_v (slice b (i + 1) len)) i }
        bn_v (slice b 0 (i + 1)) + pow2 (64 * i) * bn_v b1 - pow2 (64 * i) * v b.[i];
        (==) { bn_eval_unfold_i b (i + 1) }
        eval_ (i + 1) (slice b 0 (i + 1)) i + pow2 (64 * i) * bn_v b1;
        (==) { bn_eval_extensionality_j (slice b 0 (i + 1)) (slice b 0 i) i }
        eval_ i (slice b 0 i) i + pow2 (64 * i) * bn_v b1;
      }; () end end


val bn_eval_bound: #len:size_nat -> b:lbignum len -> i:nat{i <= len} -> Lemma
  (eval_ len b i < pow2 (64 * i))
let rec bn_eval_bound #len b i =
  if i = 0 then ()
  else begin
    bn_eval_unfold_i b i;
    assert (eval_ len b i == eval_ len b (i - 1) + pow2 (64 * (i - 1)) * v b.[i - 1]);
    calc (<) {
      eval_ len b (i - 1) + pow2 (64 * (i - 1)) * v b.[i - 1];
      (<) { bn_eval_bound #len b (i - 1) }
      pow2 (64 * (i - 1)) + pow2 (64 * (i - 1)) * v b.[i - 1];
      (==) { Math.Lemmas.distributivity_add_right (pow2 (64 * (i - 1))) 1 (v b.[i - 1]) }
      pow2 (64 * (i - 1)) * (1 + v b.[i - 1]);
      (<=) { Math.Lemmas.lemma_mult_le_left (pow2 (64 * (i - 1))) (1 + v b.[i - 1]) (pow2 64) }
      pow2 (64 * (i - 1)) * pow2 64;
      (==) { Math.Lemmas.pow2_plus (64 * (i - 1)) 64 }
      pow2 (64 * i);
    };
    assert (eval_ len b i < pow2 (64 * i))
    end


val bn_eval_index: #len:size_nat -> b:lbignum len -> i:nat{i < len} -> Lemma
  (v b.[i] == bn_v b / pow2 (64 * i) % pow2 64)
let bn_eval_index #len b i =
  calc (==) {
    bn_v b / pow2 (64 * i) % pow2 64;
    (==) { bn_eval_split_i #len b i }
    (bn_v (slice b 0 i) + pow2 (64 * i) * bn_v (slice b i len)) / pow2 (64 * i) % pow2 64;
    (==) { Math.Lemmas.division_addition_lemma (bn_v (slice b 0 i)) (pow2 (64 * i)) (bn_v (slice b i len)) }
    (bn_v (slice b 0 i) / pow2 (64 * i) + bn_v (slice b i len)) % pow2 64;
    (==) { bn_eval_bound (slice b 0 i) i; Math.Lemmas.small_division_lemma_1 (bn_v (slice b 0 i)) (pow2 (64 * i)) }
    bn_v (slice b i len) % pow2 64;
    (==) { bn_eval_split_i (slice b i len) 1 }
    (bn_v (slice b i (i + 1)) + pow2 64 * bn_v (slice b (i + 1) len)) % pow2 64;
    (==) { Math.Lemmas.modulo_addition_lemma (bn_v (slice b i (i + 1))) (pow2 64) (bn_v (slice b (i + 1) len)) }
    bn_v (slice b i (i + 1)) % pow2 64;
    (==) { Seq.lemma_index_slice b i (i + 1) 0 }
    v b.[i] % pow2 64;
    (==) { Math.Lemmas.modulo_lemma (v b.[i]) (pow2 64) }
    v b.[i];
  };
  assert (bn_v b / pow2 (64 * i) % pow2 64 == v b.[i])
