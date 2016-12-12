module Hacl.Bignum.Fproduct.Spec

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Bignum.Bigint
open Hacl.Bignum.Limb
open Hacl.Bignum.Modulo

module U32 = FStar.UInt32

#set-options "--initial_fuel 1 --max_fuel 1"

let copy_from_wide_pre (s:seqelem_wide) : GTot Type0 =
  (forall (i:nat). {:pattern w (Seq.index s i)} i < len ==> w (Seq.index s i) < pow2 n)


#set-options "--z3rlimit 20"

val copy_from_wide_spec_: s:seqelem_wide{copy_from_wide_pre s} ->
  i:nat{i <= len} ->
  tmp:seqelem{(forall (j:nat). (j >= i /\ j < len) ==> v (Seq.index tmp j) = w (Seq.index s j))} ->
  Tot (s':seqelem{(forall (j:nat). j < len ==> v (Seq.index s' j) = w (Seq.index s j))})
let rec copy_from_wide_spec_ s i tmp =
  if i = 0 then tmp
  else (
    let i = i - 1 in
    let si = Seq.index s i in
    let tmpi = wide_to_limb si in
    Math.Lemmas.modulo_lemma (w si) (pow2 n);
    let tmp' = Seq.upd tmp i tmpi in
    copy_from_wide_spec_ s i tmp'
  )


#set-options "--z3rlimit 5"

val copy_from_wide_spec: s:seqelem_wide{copy_from_wide_pre s} ->
  Tot (s':seqelem{(forall (j:nat). j < len ==> v (Seq.index s' j) = w (Seq.index s j))})
let rec copy_from_wide_spec s =
  let tmp = Seq.create len limb_zero in
  copy_from_wide_spec_ s len tmp


#set-options "--z3rlimit 5"

val shift_spec: seqelem -> Tot seqelem
let shift_spec s =
  let sfirst = Seq.slice s 0 (len - 1) in
  let slast = Seq.slice s (len-1) len in
  Seq.append slast sfirst

#set-options "--z3rlimit 20 --initial_fuel 1 --max_fuel 1"

open FStar.Mul

let sum_scalar_multiplication_pre_ (sw:seqelem_wide) (s:seqelem) (scalar:limb) (i:nat{i <= len}) : GTot Type0 =
  (forall (j:nat). j < i ==> w (Seq.index sw j) + (v (Seq.index s j) * v scalar) < pow2 wide_n)


val sum_scalar_multiplication_spec:
  sw:seqelem_wide ->
  s:seqelem ->
  scalar:limb ->
  i:nat{i <= len /\ sum_scalar_multiplication_pre_ sw s scalar i} ->
  Tot seqelem_wide
  (decreases i)
let rec sum_scalar_multiplication_spec sw s scalar i =
  if i = 0 then sw
  else (
    let j = i - 1 in
    let swi = Seq.index sw j in
    let si = Seq.index s j in
    let open Hacl.Bignum.Wide in
    let swi' = swi +^ (mul_wide si scalar) in
    let sw' = Seq.upd sw j swi' in
    sum_scalar_multiplication_spec sw' s scalar j
  )


let shift_reduce_pre (s:seqelem) : GTot Type0 = reduce_pre (shift_spec s)

val shift_reduce_spec: s:seqelem{shift_reduce_pre s} -> Tot (s':seqelem)
let shift_reduce_spec s =
  reduce_spec (shift_spec s)


let rec mul_shift_reduce_pre (output:seqelem_wide) (input:seqelem) (input2:seqelem) (ctr:nat{ctr <= len}) : GTot Type0 (decreases ctr) =
  if ctr > 0 then (
    sum_scalar_multiplication_pre_ output input (Seq.index input2 (len-ctr)) len
    /\ (let output' = sum_scalar_multiplication_spec output input (Seq.index input2 (len-ctr)) len in
       (ctr > 1 ==> shift_reduce_pre input) /\
         (let input'  = if ctr > 1 then shift_reduce_spec input else input in
          mul_shift_reduce_pre output' input' input2 (ctr-1))))
          else true


val mul_shift_reduce_spec:
  output:seqelem_wide ->
  input:seqelem -> input2:seqelem ->
  ctr:nat{ctr <= len /\ mul_shift_reduce_pre output input input2 ctr} ->
  Tot seqelem_wide
  (decreases ctr)
let rec mul_shift_reduce_spec output input input2 ctr =
  if ctr = 0 then output
  else (
    let i = ctr - 1 in
    let j = len - i - 1 in
    let input2j = Seq.index input2 j in
    let output' = sum_scalar_multiplication_spec output input input2j len in
    let input'  = if ctr > 1 then shift_reduce_spec input else input in
    mul_shift_reduce_spec output' input' input2 i
  )


#set-options "--z3rlimit 10"

let carry_wide_pre (s:seqelem_wide) (i:nat{i < len}) : GTot Type0 =
  (forall (j:nat). {:pattern (w (Seq.index s j))} (j > i /\ j < len) ==> w (Seq.index s j) < pow2 (wide_n - 1))
  /\ (forall (j:nat). {:pattern (w (Seq.index s j))} (j < i) ==> w (Seq.index s j) < pow2 limb_size)


#set-options "--z3rlimit 100 --initial_fuel 1 --max_fuel 1"

val carry_wide_spec: s:seqelem_wide -> i:nat{i < len /\ carry_wide_pre s i} -> Tot (s':seqelem_wide)
  (decreases (len - 1 - i))
let rec carry_wide_spec s i =
  if i = len - 1 then s
  else (
    let si = Seq.index s i in
    let sip1 = Seq.index s (i+1) in
    cut (w sip1 < pow2 (wide_n - 1));
    assert_norm(pow2 0 = 1);
    Math.Lemmas.pow2_lt_compat limb_size 0;
    Math.Lemmas.pow2_lt_compat limb_n limb_size;
    Math.Lemmas.modulo_lemma (pow2 limb_size) (pow2 limb_n);
    let mask = (limb_one <<^ climb_size) -^ limb_one in
    UInt.logand_mask #limb_n (v (wide_to_limb si)) limb_size;
    let r0 = wide_to_limb si &^ mask in
    Math.Lemmas.pow2_plus (limb_n - limb_size) (limb_size);
    Math.Lemmas.modulo_modulo_lemma (w si) (pow2 limb_size) (pow2 (limb_n - limb_size));
    assert(v r0 = w si % pow2 limb_size);
    assert(v r0 < pow2 limb_size);
    let open Hacl.Bignum.Wide in
    let c = si >>^ climb_size in
    Math.Lemmas.pow2_lt_compat (wide_n - 1) (limb_n);
    Math.Lemmas.pow2_double_sum (wide_n - 1);
    Math.Lemmas.lemma_div_lt (w si) (wide_n) (limb_size);
    Math.Lemmas.pow2_le_compat (wide_n - 1) (wide_n - limb_size);
    cut (w c < pow2 (wide_n - 1));
    let s' = Seq.upd s i (limb_to_wide r0) in
    assert(forall (j:nat). {:pattern (Seq.index s' j)} j < i + 1 ==> w (Seq.index s' j) < pow2 limb_size);
    assert(forall (j:nat). {:pattern (Seq.index s' j)} (j > i /\ j < len) ==> w (Seq.index s' j) < pow2 (wide_n - 1));
    let s'' = Seq.upd s' (i+1) (sip1 +^ c) in
    assert(forall (j:nat). {:pattern (Seq.index s'' j)} j < i + 1 ==> w (Seq.index s'' j) < pow2 limb_size);
    assert(forall (j:nat). {:pattern (Seq.index s'' j)} (j > i + 1 /\ j < len) ==> w (Seq.index s'' j) < pow2 (wide_n - 1));
    carry_wide_spec s'' (i+1)
  )


#set-options "--z3rlimit 5"


let carry_0_to_1_pre (input:seqelem) : GTot Type0 =
  (forall (i:nat). (i > 0 /\ i < len) ==> v (Seq.index input i) < pow2 limb_size)


val carry_0_to_1_spec: input:seqelem{carry_0_to_1_pre input} -> Tot (output:seqelem)
let carry_0_to_1_spec input =
  assume (Seq.length input > 1);
  let i0 = Seq.index input 0 in
  let i1 = Seq.index input 1 in
  assert_norm(pow2 0 = 1);
  Math.Lemmas.pow2_lt_compat limb_size 0;
  Math.Lemmas.pow2_lt_compat limb_n limb_size;
  Math.Lemmas.modulo_lemma (pow2 limb_size) (pow2 limb_n);
  let i0' = i0 &^ ((limb_one <<^ climb_size) -^ limb_one) in
  UInt.logand_mask #limb_n (v i0) limb_size;
  Math.Lemmas.pow2_plus (limb_n - limb_size) (limb_size);
  Math.Lemmas.modulo_modulo_lemma (v i0) (pow2 limb_size) (pow2 (limb_n - limb_size));
  let c = i0 >>^ climb_size in
  Math.Lemmas.pow2_double_sum (limb_n - 1);
  Math.Lemmas.pow2_le_compat (limb_n - 1) limb_size;
  Math.Lemmas.lemma_div_lt (v i0) (limb_n) (limb_size);
  Math.Lemmas.pow2_le_compat (limb_n - 1) (limb_n - limb_size);
  let i1' = i1 +^ c in
  let output = Seq.upd input 0 i0' in
  Seq.upd output 1 i1'

#set-options "--z3rlimit 5"

let fmul_pre (input:seqelem) (input2:seqelem) : GTot Type0 =
  mul_shift_reduce_pre (Seq.create len wide_zero) input input2 len

assume val lemma_mul_to_red: input:seqelem -> input2:seqelem -> Lemma
  (requires (fmul_pre input input2))
  (ensures  (fmul_pre input input2
    /\ carry_wide_pre (mul_shift_reduce_spec (Seq.create len wide_zero) input input2 len) 0
    /\ carry_top_wide_pre (carry_wide_spec (mul_shift_reduce_spec (Seq.create len wide_zero) input input2 len) 0)
    /\ copy_from_wide_pre (carry_top_wide_spec (carry_wide_spec (mul_shift_reduce_spec (Seq.create len wide_zero) input input2 len) 0))
    /\ carry_0_to_1_pre (copy_from_wide_spec (carry_top_wide_spec (carry_wide_spec (mul_shift_reduce_spec (Seq.create len wide_zero) input input2 len) 0)))))


val fmul_spec: input:seqelem -> input2:seqelem{fmul_pre input input2} -> Tot (output:seqelem)
let fmul_spec input input2 =
  lemma_mul_to_red input input2;
  let tmp = Seq.create len wide_zero in
  let output1 = mul_shift_reduce_spec tmp input input2 len in
  let output2 = carry_wide_spec output1 0 in
  let output3 = carry_top_wide_spec output2 in
  let output4 = copy_from_wide_spec output3 in
  carry_0_to_1_spec output4

#set-options "--z3rlimit 40"


val lemma_whole_slice: #a:Type -> s:Seq.seq a -> Lemma
  (Seq.slice s 0 (Seq.length s) == s)
let lemma_whole_slice #a s = Seq.lemma_eq_intro (Seq.slice s 0 (Seq.length s)) s
