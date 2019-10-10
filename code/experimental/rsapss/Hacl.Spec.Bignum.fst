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
