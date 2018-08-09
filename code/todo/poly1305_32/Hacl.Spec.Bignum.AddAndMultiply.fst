module Hacl.Spec.Bignum.AddAndMultiply

open FStar.Mul

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Fsum
open Hacl.Spec.Bignum.Fproduct
open Hacl.Spec.Bignum.Fmul
open Hacl.Spec.Bignum.Modulo


#reset-options "--max_fuel 0"

inline_for_extraction let p26 : p:pos{p = 0x4000000} = assert_norm (pow2 26 = 0x4000000);
  pow2 26
inline_for_extraction let p27 : p:pos{p = 0x8000000} = assert_norm (pow2 27 = 0x8000000);
  pow2 27
inline_for_extraction let p28 : p:pos{p = 0x10000000} = assert_norm (pow2 28 = 0x10000000);
  pow2 28
inline_for_extraction let p29 : p:pos{p = 0x20000000} = assert_norm (pow2 29 = 0x20000000);
  pow2 29
inline_for_extraction let px : p:pos{p = 134217792} = assert_norm(pow2 27 + pow2 6 = 134217792);
  134217792
inline_for_extraction let py : p:pos{p = 67108928} = assert_norm(pow2 26 + pow2 6 = 67108928);
  67108928

let red_26 (s:seqelem) =
  v (Seq.index s 0) < p26 /\ v (Seq.index s 1) < p26 /\ v (Seq.index s 2) < p26 /\ v (Seq.index s 3) < p26 /\ v (Seq.index s 4) < p26

let red_27 (s:seqelem) =
  v (Seq.index s 0) < p27 /\ v (Seq.index s 1) < p27 /\ v (Seq.index s 2) < p27 /\ v (Seq.index s 3) < p27 /\ v (Seq.index s 4) < p27

let red_28 (s:seqelem) =
  v (Seq.index s 0) < p28 /\ v (Seq.index s 1) < p28 /\ v (Seq.index s 2) < p28 /\ v (Seq.index s 3) < p28 /\ v (Seq.index s 4) < p28

let red_x (s:seqelem) =
  v (Seq.index s 0) < px /\ v (Seq.index s 1) < px /\ v (Seq.index s 2) < px /\ v (Seq.index s 3) < px /\ v (Seq.index s 4) < px

let red_y (s:seqelem) =
  v (Seq.index s 0) < py /\ v (Seq.index s 1) < py /\ v (Seq.index s 2) < py /\ v (Seq.index s 3) < py /\ v (Seq.index s 4) < py

#reset-options "--z3rlimit 10 --max_fuel 0"

val fsum_unrolled: s1:seqelem{red s1 len} -> s2:seqelem{red s2 len} -> Tot (s:seqelem{
  v (Seq.index s 0) = v (Seq.index s1 0) + v (Seq.index s2 0)
  /\ v (Seq.index s 1) = v (Seq.index s1 1) + v (Seq.index s2 1)
  /\ v (Seq.index s 2) = v (Seq.index s1 2) + v (Seq.index s2 2)
  /\ v (Seq.index s 3) = v (Seq.index s1 3) + v (Seq.index s2 3)
  /\ v (Seq.index s 4) = v (Seq.index s1 4) + v (Seq.index s2 4)
  })
let fsum_unrolled a b =
  Math.Lemmas.pow2_double_sum (limb_n-1);
  let open Hacl.Bignum.Limb in
  let c = Seq.upd a 4 ((Seq.index a 4) +^ (Seq.index b 4)) in
  let c = Seq.upd c 3 ((Seq.index a 3) +^ (Seq.index b 3)) in
  let c = Seq.upd c 2 ((Seq.index a 2) +^ (Seq.index b 2)) in
  let c = Seq.upd c 1 ((Seq.index a 1) +^ (Seq.index b 1)) in
  let c = Seq.upd c 0 ((Seq.index a 0) +^ (Seq.index b 0)) in
  c

#reset-options "--z3rlimit 20 --max_fuel 0"

val lemma_fsum_unrolled: s1:seqelem{red s1 len} -> s2:seqelem{red s2 len} -> Lemma
  (fsum_unrolled s1 s2 == fsum_spec s1 s2)
let lemma_fsum_unrolled s1 s2 =
  Seq.lemma_eq_intro (fsum_unrolled s1 s2) (fsum_spec s1 s2)


val lemma_fsum_def:
  s1:seqelem{red s1 len} -> s2:seqelem{red s2 len} ->
  Lemma (let s = fsum_spec s1 s2 in
    v (Seq.index s 0) = v (Seq.index s1 0) + v (Seq.index s2 0)
    /\ v (Seq.index s 1) = v (Seq.index s1 1) + v (Seq.index s2 1)
    /\ v (Seq.index s 2) = v (Seq.index s1 2) + v (Seq.index s2 2)
    /\ v (Seq.index s 3) = v (Seq.index s1 3) + v (Seq.index s2 3)
    /\ v (Seq.index s 4) = v (Seq.index s1 4) + v (Seq.index s2 4))
let lemma_fsum_def s1 s2 =
  lemma_fsum_unrolled s1 s2


#set-options "--z3rlimit 10 --max_fuel 0"

let mul_shift_reduce_pre' (input:seqelem) (input2:seqelem) : GTot Type0 =
  sum_scalar_multiplication_pre_ (Seq.create len wide_zero) input (Seq.index input2 0) len
  /\ shift_reduce_pre input
  /\ (let output1 = sum_scalar_multiplication_spec (Seq.create len wide_zero) input (Seq.index input2 0) in
     let input1 = shift_reduce_spec input in
     sum_scalar_multiplication_pre_ output1 input1 (Seq.index input2 1) len
     /\ shift_reduce_pre input1
     /\ (let output2 = sum_scalar_multiplication_spec output1 input1 (Seq.index input2 1) in
        let input2' = shift_reduce_spec input1 in
        sum_scalar_multiplication_pre_ output2 input2' (Seq.index input2 2) len
        /\ shift_reduce_pre input2'
        /\ (let output3 = sum_scalar_multiplication_spec output2 input2' (Seq.index input2 2) in
          let input3 = shift_reduce_spec input2' in
          sum_scalar_multiplication_pre_ output3 input3 (Seq.index input2 3) len
          /\ shift_reduce_pre input3
          /\ (let output4 = sum_scalar_multiplication_spec output3 input3 (Seq.index input2 3) in
            let input4 = shift_reduce_spec input3 in
            sum_scalar_multiplication_pre_ output4 input4 (Seq.index input2 4) len
            /\ shift_reduce_pre input4))))


#set-options "--z3rlimit 100 --initial_fuel 1 --max_fuel 1"

private let lemma_mul_shift_reduce_pre_00 (output:seqelem_wide) (input:seqelem) (input2:seqelem) : Lemma
  (mul_shift_reduce_pre_ output input input2 0 <==> true) = ()

#set-options "--z3rlimit 100 --initial_fuel 2 --max_fuel 2"

private let lemma_mul_shift_reduce_pre_0 (output:seqelem_wide) (input:seqelem) (input2:seqelem) : Lemma
  (mul_shift_reduce_pre_ output input input2 1 <==> sum_scalar_multiplication_pre_ output input (Seq.index input2 (len-1)) len) = ()

#set-options "--z3rlimit 100 --initial_fuel 1 --max_fuel 1"

private let lemma_mul_shift_reduce_pre_1 (output:seqelem_wide) (input:seqelem) (input2:seqelem) : Lemma
  (mul_shift_reduce_pre_ output input input2 2 <==> (sum_scalar_multiplication_pre_ output input (Seq.index input2 3) len /\ shift_reduce_pre input /\ mul_shift_reduce_pre_ (sum_scalar_multiplication_spec output input (Seq.index input2 3)) (shift_reduce_spec input) input2 1)) = ()

#set-options "--z3rlimit 100 --initial_fuel 1 --max_fuel 1"

private let lemma_mul_shift_reduce_pre_2 (output:seqelem_wide) (input:seqelem) (input2:seqelem) : Lemma
  (mul_shift_reduce_pre_ output input input2 3 <==> (sum_scalar_multiplication_pre_ output input (Seq.index input2 2) len /\ shift_reduce_pre input /\ mul_shift_reduce_pre_ (sum_scalar_multiplication_spec output input (Seq.index input2 2)) (shift_reduce_spec input) input2 2)) = ()

#set-options "--z3rlimit 100 --initial_fuel 1 --max_fuel 1"

private let lemma_mul_shift_reduce_pre_3 (output:seqelem_wide) (input:seqelem) (input2:seqelem) : Lemma
  (mul_shift_reduce_pre_ output input input2 4 <==> (sum_scalar_multiplication_pre_ output input (Seq.index input2 1) len /\ shift_reduce_pre input /\ mul_shift_reduce_pre_ (sum_scalar_multiplication_spec output input (Seq.index input2 1)) (shift_reduce_spec input) input2 3)) = ()

#set-options "--z3rlimit 100 --initial_fuel 1 --max_fuel 1"

private let lemma_mul_shift_reduce_pre_4 (output:seqelem_wide) (input:seqelem) (input2:seqelem) : Lemma
  (mul_shift_reduce_pre_ output input input2 5 <==> (sum_scalar_multiplication_pre_ output input (Seq.index input2 0) len /\ shift_reduce_pre input /\ mul_shift_reduce_pre_ (sum_scalar_multiplication_spec output input (Seq.index input2 0)) (shift_reduce_spec input) input2 4)) = ()

#reset-options "--z3rlimit 10 --max_fuel 0"

let lemma_mul_shift_reduce_pre (input:seqelem) (input2:seqelem) : Lemma
  (requires (mul_shift_reduce_pre' input input2))
  (ensures (mul_shift_reduce_pre_ (Seq.create len wide_zero) input input2 len))
  = lemma_mul_shift_reduce_pre_4 (Seq.create len wide_zero) input input2;
    let output3 = sum_scalar_multiplication_spec (Seq.create len wide_zero) input (Seq.index input2 0) in
    let input3 = shift_reduce_spec input in
    lemma_mul_shift_reduce_pre_3 output3 input3 input2;
    let output4 = sum_scalar_multiplication_spec output3 input3 (Seq.index input2 1) in
    let input4 = shift_reduce_spec input3 in
    lemma_mul_shift_reduce_pre_2 output4 input4 input2;
    let output5 = sum_scalar_multiplication_spec output4 input4 (Seq.index input2 2) in
    let input5 = shift_reduce_spec input4 in
    lemma_mul_shift_reduce_pre_1 output5 input5 input2;
    let output6 = sum_scalar_multiplication_spec output5 input5 (Seq.index input2 3) in
    let input6 = shift_reduce_spec input5 in
    lemma_mul_shift_reduce_pre_0 output6 input6 input2;
    let output7 = sum_scalar_multiplication_spec output6 input6 (Seq.index input2 4) in
    ()


#set-options "--z3rlimit 10 --initial_fuel 1 --max_fuel 1"

let lemma_zero_mod (a:int{a = 0}) (b:pos) : Lemma (a % b = 0) = ()
let lemma_zero_mul (a:int{a = 0}) (b:int) : Lemma (a * b = 0 /\ b * a = 0) = ()

#reset-options "--z3rlimit 20 --initial_fuel 1 --max_fuel 1"

let lemma_mul_shift_reduce_pre2 (input:seqelem) (input2:seqelem) : Lemma
  (requires (mul_shift_reduce_pre' input input2))
  (ensures (mul_shift_reduce_pre (Seq.create len wide_zero) input input input2 len))
  = lemma_mul_shift_reduce_pre input input2;
    assert_norm(pow2 0 = 1);
    lemma_seval_wide_null (Seq.create len wide_zero) len;
    lemma_zero_mod (Hacl.Spec.Bignum.Bigint.seval_wide (Seq.create len wide_zero)) prime;
    lemma_zero_mul (Hacl.Spec.Bignum.Bigint.seval_ input2 0) (Hacl.Spec.Bignum.Bigint.seval input);
    lemma_zero_mod (Hacl.Spec.Bignum.Bigint.seval input * Hacl.Spec.Bignum.Bigint.seval_ input2 0) prime;
    assert (Hacl.Spec.Bignum.Bigint.seval_wide (Seq.create len wide_zero) % prime = (Hacl.Spec.Bignum.Bigint.seval input * Hacl.Spec.Bignum.Bigint.seval_ input2 0) % prime);
    lemma_zero_mul (len-len) limb_size


private val mul_shift_reduce_unrolled__:
  input:seqelem{shift_reduce_pre input} -> input2:seqelem{
    sum_scalar_multiplication_pre_ (Seq.create len wide_zero) input (Seq.index input2 0) len
  /\ (let output1 = sum_scalar_multiplication_spec (Seq.create len wide_zero) input (Seq.index input2 0) in
     let input1 = shift_reduce_spec input in
     sum_scalar_multiplication_pre_ output1 input1 (Seq.index input2 1) len
     /\ shift_reduce_pre input1
     /\ (let output2 = sum_scalar_multiplication_spec output1 input1 (Seq.index input2 1) in
        let input2' = shift_reduce_spec input1 in
        sum_scalar_multiplication_pre_ output2 input2' (Seq.index input2 2) len
        /\ shift_reduce_pre input2'
        /\ (let output3 = sum_scalar_multiplication_spec output2 input2' (Seq.index input2 2) in
          let input3 = shift_reduce_spec input2' in
          sum_scalar_multiplication_pre_ output3 input3 (Seq.index input2 3) len
          /\ shift_reduce_pre input3
          /\ (let output4 = sum_scalar_multiplication_spec output3 input3 (Seq.index input2 3) in
            let input4 = shift_reduce_spec input3 in
            sum_scalar_multiplication_pre_ output4 input4 (Seq.index input2 4) len
            /\ shift_reduce_pre input4))))} ->
  Tot (s:seqelem_wide)
private let mul_shift_reduce_unrolled__ input input2 =
  let input_init = input in
  let output = Seq.create len wide_zero in
  let output1   = sum_scalar_multiplication_spec output input (Seq.index input2 0) in
  let input1    = shift_reduce_spec input in
  let output2   = sum_scalar_multiplication_spec output1 input1 (Seq.index input2 1) in
  let input2'   = shift_reduce_spec input1 in
  let output3   = sum_scalar_multiplication_spec output2 input2' (Seq.index input2 2) in
  let input3   = shift_reduce_spec input2' in
  let output4   = sum_scalar_multiplication_spec output3 input3 (Seq.index input2 3) in
  let input4   = shift_reduce_spec input3 in
  sum_scalar_multiplication_spec output4 input4 (Seq.index input2 4)


let bounds (s:seqelem) (s0:nat) (s1:nat) (s2:nat) (s3:nat) (s4:nat) : GTot Type0 =
  v (Seq.index s 0) < s0 /\ v (Seq.index s 1) < s1 /\ v (Seq.index s 2) < s2
  /\ v (Seq.index s 3) < s3 /\ v (Seq.index s 4) < s4

let bounds' (s:seqelem_wide) (s0:nat) (s1:nat) (s2:nat) (s3:nat) (s4:nat) : GTot Type0 =
  w (Seq.index s 0) < s0 /\ w (Seq.index s 1) < s1 /\ w (Seq.index s 2) < s2
  /\ w (Seq.index s 3) < s3 /\ w (Seq.index s 4) < s4

#reset-options "--max_fuel 0 --z3rlimit 20"

private let sum_scalar_multiplication_pre_' (sw:seqelem_wide) (s:seqelem) (scalar:limb) =
  w (Seq.index sw 0) + (v (Seq.index s 0) * v scalar) < pow2 wide_n
  /\ w (Seq.index sw 1) + (v (Seq.index s 1) * v scalar) < pow2 wide_n
  /\ w (Seq.index sw 2) + (v (Seq.index s 2) * v scalar) < pow2 wide_n
  /\ w (Seq.index sw 3) + (v (Seq.index s 3) * v scalar) < pow2 wide_n
  /\ w (Seq.index sw 4) + (v (Seq.index s 4) * v scalar) < pow2 wide_n


val lemma_sum_scalar_muitiplication_pre_:
  sw:seqelem_wide -> s:seqelem -> scalar:limb ->
  Lemma (sum_scalar_multiplication_pre_ sw s scalar len <==>
    (sum_scalar_multiplication_pre_' sw s scalar))
let lemma_sum_scalar_muitiplication_pre_ sw s scalar = ()


val lemma_mul_ineq: a:nat -> b:nat -> c:nat -> d:nat -> Lemma
  (requires (a < c /\ b < d))
  (ensures (a * b < c * d))
let lemma_mul_ineq a b c d = ()

#set-options "--z3rlimit 10 --max_fuel 0"

val lemma_reduce_spec_: s:seqelem{reduce_pre s} -> Lemma
  (let s' = reduce_spec s in
    v (Seq.index s' 0) = 5 * v (Seq.index s 0)
    /\ v (Seq.index s' 1) = v (Seq.index s 1)
    /\ v (Seq.index s' 2) = v (Seq.index s 2)
    /\ v (Seq.index s' 3) = v (Seq.index s 3)
    /\ v (Seq.index s' 4) = v (Seq.index s 4) )
let lemma_reduce_spec_ s =
  assert_norm(pow2 2 = 4);
  let open Hacl.Bignum.Limb in
  let s0 = Seq.index s 0 in
  let s0_4 = s0 <<^ 2ul in
  Math.Lemmas.modulo_lemma (v s0 * 4) (pow2 32);
  let s0_5 = s0_4 +^ s0 in
  let s' = Seq.upd s 0 s0_5 in
  assert (s' == reduce_spec s);
  assert (Seq.index s 1 == Seq.index s' 1);
  assert (Seq.index s 2 == Seq.index s' 2);
  assert (Seq.index s 3 == Seq.index s' 3);
  assert (Seq.index s 4 == Seq.index s' 4)

val lemma_shift_reduce_spec_: s:seqelem{shift_reduce_pre s} -> Lemma
  (let s' = shift_reduce_spec s in
    v (Seq.index s' 0) = 5 * v (Seq.index s 4)
    /\ v (Seq.index s' 1) = v (Seq.index s 0)
    /\ v (Seq.index s' 2) = v (Seq.index s 1)
    /\ v (Seq.index s' 3) = v (Seq.index s 2)
    /\ v (Seq.index s' 4) = v (Seq.index s 3) )
let lemma_shift_reduce_spec_ s =
  let s0 = Seq.index s 4 in
  let s' = shift_spec s in
  let s'' = reduce_spec s' in
  assert (v (Seq.index s 4) = v (Seq.index s' 0));
  assert (v (Seq.index s 3) = v (Seq.index s' 4));
  assert (v (Seq.index s 2) = v (Seq.index s' 3));
  assert (v (Seq.index s 1) = v (Seq.index s' 2));
  assert (v (Seq.index s 0) = v (Seq.index s' 1));
  lemma_reduce_spec_ s'


val lemma_sum_scalar_muitiplication_spec_: sw:seqelem_wide -> s:seqelem -> sc:limb ->
  Lemma (requires (sum_scalar_multiplication_pre_ sw s sc len))
        (ensures (sum_scalar_multiplication_pre_ sw s sc len
          /\ (let sw' = sum_scalar_multiplication_spec sw s sc in
             w (Seq.index sw' 0) = w (Seq.index sw 0) + (v (Seq.index s 0) * v sc)
             /\ w (Seq.index sw' 1) = w (Seq.index sw 1) + (v (Seq.index s 1) * v sc)
             /\ w (Seq.index sw' 2) = w (Seq.index sw 2) + (v (Seq.index s 2) * v sc)
             /\ w (Seq.index sw' 3) = w (Seq.index sw 3) + (v (Seq.index s 3) * v sc)
             /\ w (Seq.index sw' 4) = w (Seq.index sw 4) + (v (Seq.index s 4) * v sc)) ))
let lemma_sum_scalar_muitiplication_spec_ sw s sc = ()

inline_for_extraction let p54 : p:pos{p = 0x40000000000000} = assert_norm(pow2 54 = 0x40000000000000); pow2 54

inline_for_extraction let p55 : p:pos{p = 0x80000000000000} = assert_norm(pow2 55 = 0x80000000000000); pow2 55

inline_for_extraction let pxx : p:pos{p = 9007203549708288} = assert_norm(px * pow2 26 = 9007203549708288); px * pow2 26


val lemma_shift_reduce_then_carry_wide_0:
  s1:seqelem{red_x s1} ->
  s2:seqelem{red_26 s2} ->
  Lemma (sum_scalar_multiplication_pre_ (Seq.create len wide_zero) s1 (Seq.index s2 0) len
    /\ shift_reduce_pre s1
    /\ bounds (shift_reduce_spec s1) (5 * px) px px px px
    /\ bounds' (sum_scalar_multiplication_spec (Seq.create len wide_zero) s1 (Seq.index s2 0))
              pxx pxx pxx pxx pxx)
let lemma_shift_reduce_then_carry_wide_0 s1 s2 =
  assert_norm (pow2 32 = 0x100000000);
  assert_norm (pow2 64 = 0x10000000000000000);
  let bla = Seq.create len wide_zero in
  assert (w (Seq.index bla 0) = 0); assert (w (Seq.index bla 1) = 0); assert (w (Seq.index bla 2) = 0);
  assert (w (Seq.index bla 3) = 0); assert (w (Seq.index bla 4) = 0);
  lemma_mul_ineq (v (Seq.index s1 0)) (v (Seq.index s2 0)) px p26;
  lemma_mul_ineq (v (Seq.index s1 1)) (v (Seq.index s2 0)) px p26;
  lemma_mul_ineq (v (Seq.index s1 2)) (v (Seq.index s2 0)) px p26;
  lemma_mul_ineq (v (Seq.index s1 3)) (v (Seq.index s2 0)) px p26;
  lemma_mul_ineq (v (Seq.index s1 4)) (v (Seq.index s2 0)) px p26;
  assert (sum_scalar_multiplication_pre_' bla s1 (Seq.index s2 0));
  lemma_sum_scalar_muitiplication_pre_ bla s1 (Seq.index s2 0);
  lemma_shift_reduce_spec_ s1


val lemma_shift_reduce_then_carry_wide_1:
  o:seqelem_wide{bounds' o pxx pxx pxx pxx pxx} ->
  s1:seqelem{bounds s1 (5*px) px px px px} ->
  s2:seqelem{red_26 s2} ->
  Lemma (sum_scalar_multiplication_pre_ o s1 (Seq.index s2 1) len
    /\ shift_reduce_pre s1
    /\ bounds (shift_reduce_spec s1) (5 * px) (5 * px) px px px
    /\ bounds' (sum_scalar_multiplication_spec o s1 (Seq.index s2 1))
              (6 * pxx) (2*pxx) (2*pxx) (2*pxx) (2*pxx))
let lemma_shift_reduce_then_carry_wide_1 o s1 s2 =
  assert_norm (pow2 64 = 0x10000000000000000);
  assert_norm (pow2 32 = 0x100000000);
  lemma_mul_ineq (v (Seq.index s1 0)) (v (Seq.index s2 1)) (5 * px) p26;
  lemma_mul_ineq (v (Seq.index s1 1)) (v (Seq.index s2 1)) px p26;
  lemma_mul_ineq (v (Seq.index s1 2)) (v (Seq.index s2 1)) px p26;
  lemma_mul_ineq (v (Seq.index s1 3)) (v (Seq.index s2 1)) px p26;
  lemma_mul_ineq (v (Seq.index s1 4)) (v (Seq.index s2 1)) px p26;
  assert (sum_scalar_multiplication_pre_' o s1 (Seq.index s2 1));
  lemma_sum_scalar_muitiplication_pre_ o s1 (Seq.index s2 1);
  lemma_shift_reduce_spec_ s1

#reset-options "--z3rlimit 20 --max_fuel 0"

val lemma_shift_reduce_then_carry_wide_2:
  o:seqelem_wide{bounds' o (6*pxx) (2*pxx) (2*pxx) (2*pxx) (2*pxx)} ->
  s1:seqelem{bounds s1 (5*px) (5*px) px px px} ->
  s2:seqelem{red_26 s2} ->
  Lemma (sum_scalar_multiplication_pre_ o s1 (Seq.index s2 2) len
    /\ shift_reduce_pre s1
    /\ bounds (shift_reduce_spec s1) (5 * px) (5 *px) (5*px) px px
    /\ bounds' (sum_scalar_multiplication_spec o s1 (Seq.index s2 2))
              (11 * pxx) (7*pxx) (3*pxx) (3*pxx) (3*pxx))
let lemma_shift_reduce_then_carry_wide_2 o s1 s2 =
  assert_norm (pow2 64 = 0x10000000000000000);
  assert_norm (pow2 32 = 0x100000000);
  lemma_mul_ineq (v (Seq.index s1 0)) (v (Seq.index s2 2)) (5*px) p26;
  lemma_mul_ineq (v (Seq.index s1 1)) (v (Seq.index s2 2)) (5*px) p26;
  lemma_mul_ineq (v (Seq.index s1 2)) (v (Seq.index s2 2)) px p26;
  lemma_mul_ineq (v (Seq.index s1 3)) (v (Seq.index s2 2)) px p26;
  lemma_mul_ineq (v (Seq.index s1 4)) (v (Seq.index s2 2)) px p26;
  assert (sum_scalar_multiplication_pre_' o s1 (Seq.index s2 2));
  lemma_sum_scalar_muitiplication_pre_ o s1 (Seq.index s2 2);
  lemma_shift_reduce_spec_ s1


#reset-options "--z3rlimit 20 --max_fuel 0"

val lemma_shift_reduce_then_carry_wide_3:
  o:seqelem_wide{bounds' o (11*pxx) (7*pxx) (3*pxx) (3*pxx) (3*pxx)} ->
  s1:seqelem{bounds s1 (5*px) (5*px) (5*px) px px} ->
  s2:seqelem{red_26 s2} ->
  Lemma (sum_scalar_multiplication_pre_ o s1 (Seq.index s2 3) len
    /\ shift_reduce_pre s1
    /\ bounds (shift_reduce_spec s1) (5 * px) (5 *px) (5*px) (5*px) px
    /\ bounds' (sum_scalar_multiplication_spec o s1 (Seq.index s2 3))
              (16 * pxx) (12*pxx) (8*pxx) (4*pxx) (4*pxx))
let lemma_shift_reduce_then_carry_wide_3 o s1 s2 =
  assert_norm (pow2 64 = 0x10000000000000000);
  assert_norm (pow2 32 = 0x100000000);
  lemma_mul_ineq (v (Seq.index s1 0)) (v (Seq.index s2 3)) (5*px) p26;
  lemma_mul_ineq (v (Seq.index s1 1)) (v (Seq.index s2 3)) (5*px) p26;
  lemma_mul_ineq (v (Seq.index s1 2)) (v (Seq.index s2 3)) (5*px) p26;
  lemma_mul_ineq (v (Seq.index s1 3)) (v (Seq.index s2 3)) px p26;
  lemma_mul_ineq (v (Seq.index s1 4)) (v (Seq.index s2 3)) px p26;
  assert (sum_scalar_multiplication_pre_' o s1 (Seq.index s2 3));
  lemma_sum_scalar_muitiplication_pre_ o s1 (Seq.index s2 3);
  lemma_shift_reduce_spec_ s1


#reset-options "--z3rlimit 20 --max_fuel 0"

val lemma_shift_reduce_then_carry_wide_4:
  o:seqelem_wide{bounds' o (16*pxx) (12*pxx) (8*pxx) (4*pxx) (4*pxx)} ->
  s1:seqelem{bounds s1 (5*px) (5*px) (5*px) (5*px) px} ->
  s2:seqelem{red_26 s2} ->
  Lemma (sum_scalar_multiplication_pre_ o s1 (Seq.index s2 4) len
    /\ shift_reduce_pre s1
    /\ bounds (shift_reduce_spec s1) (5 * px) (5 *px) (5*px) (5*px) (5*px)
    /\ bounds' (sum_scalar_multiplication_spec o s1 (Seq.index s2 4))
              (21 * pxx) (17*pxx) (13*pxx) (9*pxx) (5*pxx))
let lemma_shift_reduce_then_carry_wide_4 o s1 s2 =
  assert_norm (pow2 64 = 0x10000000000000000);
  assert_norm (pow2 32 = 0x100000000);
  lemma_mul_ineq (v (Seq.index s1 0)) (v (Seq.index s2 4)) (5*px) p26;
  lemma_mul_ineq (v (Seq.index s1 1)) (v (Seq.index s2 4)) (5*px) p26;
  lemma_mul_ineq (v (Seq.index s1 2)) (v (Seq.index s2 4)) (5*px) p26;
  lemma_mul_ineq (v (Seq.index s1 3)) (v (Seq.index s2 4)) (5*px) p26;
  lemma_mul_ineq (v (Seq.index s1 4)) (v (Seq.index s2 4)) px p26;
  assert (sum_scalar_multiplication_pre_' o s1 (Seq.index s2 4));
  lemma_sum_scalar_muitiplication_pre_ o s1 (Seq.index s2 4);
  lemma_shift_reduce_spec_ s1


#reset-options "--z3rlimit 10 --max_fuel 0"

private 
val mul_shift_reduce_unrolled_0:
  output:seqelem_wide ->
  input_init:seqelem ->
  input:seqelem ->
  input2:seqelem{mul_shift_reduce_pre output input_init input input2 len} ->
  Tot (t:tuple2 seqelem_wide seqelem{t == mul_shift_reduce_spec_ output input_init input input2 4})
#reset-options "--z3rlimit 25 --initial_fuel 1 --max_fuel 1"
let mul_shift_reduce_unrolled_0 output input_init input input2 =
  lemma_mul_shift_reduce_spec_def_0 output input_init input input2;
  lemma_mul_shift_reduce_spec_def output input_init input input2 2;
  let ctr = 4 in
  let i = ctr in
  let j = len - i - 1 in
  let input2j = Seq.index input2 j in
  let output' = sum_scalar_multiplication_spec output input input2j in
  lemma_sum_scalar_multiplication_ output input input2j len;
  let input'  = shift_reduce_spec input in
  output', input'

private val mul_shift_reduce_unrolled_1:
  output:seqelem_wide ->
  input_init:seqelem ->
  input:seqelem ->
  input2:seqelem{mul_shift_reduce_pre output input_init input input2 len} ->
  Tot (t:tuple2 seqelem_wide seqelem{t == mul_shift_reduce_spec_ output input_init input input2 3})
let mul_shift_reduce_unrolled_1 output0 input_init input0 input2 =
  let output, input = mul_shift_reduce_unrolled_0 output0 input_init input0 input2 in
  let ctr = 3 in
  lemma_mul_shift_reduce_spec_def output0 input_init input0 input2 ctr;
  let i = ctr in
  let j = len - i - 1 in
  let input2j = Seq.index input2 j in
  let output' = sum_scalar_multiplication_spec output input input2j in
  lemma_sum_scalar_multiplication_ output input input2j len;
  let input'  = shift_reduce_spec input in
  output', input'


private val mul_shift_reduce_unrolled_2:
  output:seqelem_wide ->
  input_init:seqelem ->
  input:seqelem ->
  input2:seqelem{mul_shift_reduce_pre output input_init input input2 len} ->
  Tot (t:tuple2 seqelem_wide seqelem{t == mul_shift_reduce_spec_ output input_init input input2 2})
let mul_shift_reduce_unrolled_2 output0 input_init input0 input2 =
  let output, input = mul_shift_reduce_unrolled_1 output0 input_init input0 input2 in
  let ctr = 2 in
  lemma_mul_shift_reduce_spec_def output0 input_init input0 input2 ctr;
  let i = ctr in
  let j = len - i - 1 in
  let input2j = Seq.index input2 j in
  let output' = sum_scalar_multiplication_spec output input input2j in
  lemma_sum_scalar_multiplication_ output input input2j len;
  let input'  = shift_reduce_spec input in
  output', input'


private val mul_shift_reduce_unrolled_3:
  output:seqelem_wide ->
  input_init:seqelem ->
  input:seqelem ->
  input2:seqelem{mul_shift_reduce_pre output input_init input input2 len} ->
  Tot (t:tuple2 seqelem_wide seqelem{t == mul_shift_reduce_spec_ output input_init input input2 1})
let mul_shift_reduce_unrolled_3 output0 input_init input0 input2 =
  let output, input = mul_shift_reduce_unrolled_2 output0 input_init input0 input2 in
  let ctr = 1 in
  lemma_mul_shift_reduce_spec_def output0 input_init input0 input2 ctr;
  let i = ctr in
  let j = len - i - 1 in
  let input2j = Seq.index input2 j in
  let output' = sum_scalar_multiplication_spec output input input2j in
  lemma_sum_scalar_multiplication_ output input input2j len;
  let input'  = shift_reduce_spec input in
  output', input'


private
val mul_shift_reduce_unrolled_:
  output:seqelem_wide ->
  input_init:seqelem ->
  input:seqelem ->
  input2:seqelem{mul_shift_reduce_pre output input_init input input2 len} ->
  Tot (t:seqelem_wide{let x, _ = mul_shift_reduce_spec_ output input_init input input2 0 in
    t == x})
let mul_shift_reduce_unrolled_ output0 input_init input0 input2 =
  let output, input = mul_shift_reduce_unrolled_3 output0 input_init input0 input2 in
  let ctr = 0 in
  lemma_mul_shift_reduce_spec_def output0 input_init input0 input2 ctr;
  let i = ctr in
  let j = len - i - 1 in
  let input2j = Seq.index input2 j in
  let output' = sum_scalar_multiplication_spec output input input2j in
  lemma_sum_scalar_multiplication_ output input input2j len;
  output'


private val shift_reduce_unrolled:
  input:seqelem ->
  input2:seqelem{mul_shift_reduce_pre (Seq.create len wide_zero) input input input2 len} ->
  Tot (s:seqelem_wide{s == mul_shift_reduce_spec input input2})
private let shift_reduce_unrolled input input2 =
  mul_shift_reduce_unrolled_ (Seq.create len wide_zero) input input input2

#reset-options "--z3rlimit 50 --max_fuel 0"

val lemma_mul_shift_reduce_unrolled: input:seqelem -> input2:seqelem -> Lemma
  (requires (mul_shift_reduce_pre' input input2))
  (ensures (mul_shift_reduce_pre (Seq.create len wide_zero) input input input2 len
  /\ mul_shift_reduce_pre' input input2
  /\ mul_shift_reduce_unrolled__ input input2 == mul_shift_reduce_spec input input2))
let lemma_mul_shift_reduce_unrolled input input2 =
  lemma_mul_shift_reduce_pre2 input input2;
  let s = shift_reduce_unrolled input input2 in
  assert (s == mul_shift_reduce_unrolled__ input input2)


#reset-options "--z3rlimit 20 --max_fuel 0"

val lemma_shift_reduce_then_carry_wide:
  s1:seqelem{red_x s1} -> s2:seqelem{red_26 s2} ->
  Lemma (mul_shift_reduce_pre' s1 s2 /\
    bounds' (mul_shift_reduce_unrolled__ s1 s2) (21 * pxx) (17*pxx) (13*pxx) (9*pxx) (5*pxx))
let lemma_shift_reduce_then_carry_wide s1 s2 =
  lemma_shift_reduce_then_carry_wide_0 s1 s2;
  let o1 = sum_scalar_multiplication_spec (Seq.create len wide_zero) s1 (Seq.index s2 0) in
  let s11 = shift_reduce_spec s1 in
  lemma_shift_reduce_then_carry_wide_1 o1 s11 s2;
  let o2 = sum_scalar_multiplication_spec o1 s11 (Seq.index s2 1) in
  let s12 = shift_reduce_spec s11 in
  lemma_shift_reduce_then_carry_wide_2 o2 s12 s2;
  let o3 = sum_scalar_multiplication_spec o2 s12 (Seq.index s2 2) in
  let s13 = shift_reduce_spec s12 in
  lemma_shift_reduce_then_carry_wide_3 o3 s13 s2;
  let o4 = sum_scalar_multiplication_spec o3 s13 (Seq.index s2 3) in
  let s14 = shift_reduce_spec s13 in
  lemma_shift_reduce_then_carry_wide_4 o4 s14 s2;
  let o5 = sum_scalar_multiplication_spec o4 s14 (Seq.index s2 4) in ()


private val carry_wide_spec_unrolled:
  s:seqelem_wide{carry_wide_pre s 0} ->
  Tot (s':seqelem_wide{w (Seq.index s' 4) < w (Seq.index s 4) + pow2 (2*word_size-limb_size)})
private let carry_wide_spec_unrolled s =
  let s1 = carry_wide_step s 0 in
  lemma_carry_wide_step s 0;
  let s2 = carry_wide_step s1 1 in
  lemma_carry_wide_step s1 1;
  let s3 = carry_wide_step s2 2 in
  lemma_carry_wide_step s2 2;
  let s4 = carry_wide_step s3 3 in
  lemma_carry_wide_step s3 3;
  Math.Lemmas.lemma_div_lt (w (Seq.index s3 3)) (2*word_size) limb_size;
  assert (w (Seq.index s4 4) < w (Seq.index s 4) + pow2 (2*word_size - limb_size));
  s4


#reset-options "--z3rlimit 100 --initial_fuel 5 --max_fuel 5"

private val lemma_carry_wide_spec_unrolled:
  s:seqelem_wide{carry_wide_pre s 0} -> Lemma (carry_wide_spec_unrolled s == carry_wide_spec s)
let lemma_carry_wide_spec_unrolled s = ()

#set-options "--z3rlimit 20 --max_fuel 0"

inline_for_extraction let p38 : p:pos{p = 0x4000000000} = assert_norm (pow2 38 = 0x4000000000); pow2 38

#reset-options "--z3rlimit 20 --max_fuel 0"

val lemma_x_26_is_fine_to_carry:
  s:seqelem_wide{bounds' s (21*pxx) (17*pxx) (13*pxx) (9*pxx) (5*pxx)} ->
  Lemma (carry_wide_pre s 0 /\ bounds' (carry_wide_spec s) p26 p26 p26 p26 (5*pxx+p38))
let lemma_x_26_is_fine_to_carry s =
  assert_norm (pow2 64 = 0x10000000000000000);
  assert_norm (pow2 32 = 0x100000000);
  lemma_carry_wide_spec_unrolled s


#set-options "--z3rlimit 20 --max_fuel 0"

val lemma_copy_then_carry: s:seqelem_wide -> Lemma
  ((copy_from_wide_pre s /\ (w (Seq.index s 0) < pow2 word_size /\ w (Seq.index s 1) < pow2 limb_size
    /\ w (Seq.index s 2) < pow2 limb_size /\ w (Seq.index s 3) < pow2 limb_size /\ w (Seq.index s 4) < pow2 limb_size)) ==>
     (carry_0_to_1_pre (copy_from_wide_spec s) ))
let lemma_copy_then_carry s = ()


val lemma_carry_top_wide_then_copy: s:seqelem_wide{carry_top_wide_pre s} -> Lemma
  ((w (Seq.index s 0) + 5 * (w (Seq.index s 4) / p26) < pow2 word_size /\ w (Seq.index s 1) < pow2 word_size /\ w (Seq.index s 2) < pow2 word_size /\ w (Seq.index s 3) < pow2 word_size) ==> copy_from_wide_pre (carry_top_wide_spec s))
let lemma_carry_top_wide_then_copy s =
  lemma_carry_top_wide_spec_ s;
  assert_norm(pow2 32 > pow2 26);
  assert_norm(pow2 32 > pow2 26);
  assert_norm(pow2 32 > px)

#reset-options "--z3rlimit 200 --max_fuel 0 --smtencoding.nl_arith_repr native --smtencoding.l_arith_repr native "

val lemma_carry_wide_then_carry_top: s:seqelem_wide{carry_wide_pre s 0} -> Lemma
  (((w (Seq.index s 4) + pow2 (2*word_size - limb_size))/ pow2 26 < pow2 word_size
    /\ 5 * (w (Seq.index s 4) + pow2 (2*word_size - limb_size) / pow2 26) + pow2 limb_size < pow2 word_size)
    ==> carry_top_wide_pre (carry_wide_spec s) )
let lemma_carry_wide_then_carry_top s =
  let s' = carry_wide_spec_unrolled s in
  lemma_carry_wide_spec_unrolled s;
  assert (w (Seq.index s' 4) < w (Seq.index s 4) + pow2 (2*word_size-limb_size));
  Math.Lemmas.nat_times_nat_is_nat 5 (w (Seq.index s 4) + pow2 (2*word_size-limb_size));
  if ((w (Seq.index s 4) + pow2 (2*word_size - limb_size))/ pow2 26 < pow2 word_size
    && 5 * (w (Seq.index s 4) + pow2 (2*word_size - limb_size) / pow2 26) + pow2 limb_size < pow2 word_size) then (
    Math.Lemmas.lemma_div_le (w (Seq.index s' 4)) (w (Seq.index s 4) + pow2 (2*word_size-limb_size)) (pow2 26);
    assert (w (Seq.index s' 4) / pow2 26 <= (w (Seq.index s 4) + pow2 (2*word_size-limb_size)) / pow2 26);
    Math.Lemmas.nat_over_pos_is_nat (w (Seq.index s' 4)) (pow2 26);
    Math.Lemmas.nat_over_pos_is_nat (((w (Seq.index s 4)+(pow2 (2*word_size-limb_size)))/pow2 26)) (pow2 26);
    Math.Lemmas.multiplication_order_lemma (w (Seq.index s' 4) / pow2 26)
                                           ((w (Seq.index s 4)+(pow2 (2*word_size-limb_size)))/pow2 26) 5;
    assert (5 * (w (Seq.index s' 4) / pow2 26) <= 5 * ((w (Seq.index s 4) + pow2 (2*word_size-limb_size)) / pow2 26));
    assert (w (Seq.index s' 0) < pow2 limb_size);
    assert (5 * (w (Seq.index s' 4) / pow2 26) + w (Seq.index s' 0) < pow2 word_size);
    Math.Lemmas.pow2_lt_compat (2*word_size) word_size
  )
  else ()


val lemma_x_26_is_fine_to_carry_top:
  s:seqelem_wide{bounds' s p26 p26 p26 p26 (5*pxx+p38)} ->
  Lemma (carry_top_wide_pre s /\ bounds' (carry_top_wide_spec s) (p26+5*((5*pxx+p38)/p26)) p26 p26 p26 p26)
let lemma_x_26_is_fine_to_carry_top s =
  assert_norm (pow2 64 = 0x10000000000000000);
  assert_norm (pow2 32 = 0x100000000);
  lemma_carry_wide_then_carry_top s;
  let s0 = w (Seq.index s 0) in
  let s1 = w (Seq.index s 1) in
  let s2 = w (Seq.index s 2) in
  let s3 = w (Seq.index s 3) in
  let s4 = w (Seq.index s 4) in
  assert(s0 < pow2 32);
  Math.Lemmas.lemma_div_le s4 (5*pxx+p38-1) (pow2 26);
  assert_norm(5 * ((5*pxx+p38-1) / pow2 26) + pow2 26 < pow2 32);
  lemma_carry_top_wide_spec_ s


val lemma_46_44_is_fine_to_copy:
  s:seqelem_wide{bounds' (s) (p26+5*((5*pxx+p38)/p26)) p26 p26 p26 p26} ->
  Lemma (copy_from_wide_pre s /\ bounds (copy_from_wide_spec s) (p26+5*((5*pxx+p38)/p26)) p26 p26 p26 p26)
let lemma_46_44_is_fine_to_copy s =
  assert_norm (pow2 32 = 0x100000000)

inline_for_extraction let p6 : p:pos{p = 0x40} = assert_norm(pow2 6 = 0x40); pow2 6

val lemma_46_44_is_fine_to_carry_last:
  s:seqelem{bounds (s) (p26+5*((5*pxx+p38)/p26)) p26 p26 p26 p26} ->
  Lemma (carry_0_to_1_pre s /\ bounds (carry_0_to_1_spec s) p26 (p26+p6) p26 p26 p26)
let lemma_46_44_is_fine_to_carry_last s =
  ()


#reset-options "--max_fuel 0 --z3rlimit 100"

val fmul_x_26_is_fine:
  s1:seqelem{red_x s1} -> s2:seqelem{red_26 s2} ->
  Lemma (fmul_pre s1 s2 /\ red_y (fmul_spec s1 s2))
let fmul_x_26_is_fine s1 s2 =
  lemma_shift_reduce_then_carry_wide s1 s2;
  lemma_mul_shift_reduce_unrolled s1 s2;
  let o = mul_shift_reduce_spec s1 s2 in
  lemma_x_26_is_fine_to_carry o;
  let o' = carry_wide_spec o in
  lemma_x_26_is_fine_to_carry_top o';
  let o'' = carry_top_wide_spec o' in
  lemma_46_44_is_fine_to_copy o'';
  let o''' = copy_from_wide_spec o'' in
  lemma_46_44_is_fine_to_carry_last o''';
  let o'''' = carry_0_to_1_spec o''' in
  assert (bounds o'''' p26 (p26+p6) p26 p26 p26);
  assert (o'''' == fmul_spec s1 s2)
  
  // ;
  // assert_norm(p+p20 < p45);
  // assert_norm(p44 < p45);
  // assert_norm(p42 < p45)

// val fmul_46_44_is_fine:
//   s1:seqelem{red_46 s1} -> s2:seqelem{red_44 s2} ->
//   Lemma (fmul_pre s1 s2 /\ red_45 (fmul_spec s1 s2))
// let fmul_46_44_is_fine s1 s2 =
//   lemma_shift_reduce_then_carry_wide s1 s2;
//   lemma_mul_shift_reduce_unrolled s1 s2;
//   let o = mul_shift_reduce_spec s1 s2 in
//   lemma_46_44_is_fine_to_carry o;
//   let o' = carry_wide_spec o in
//   lemma_46_44_is_fine_to_carry_top o';
//   let o'' = carry_top_wide_spec o' in
//   lemma_46_44_is_fine_to_copy o'';
//   let o''' = copy_from_wide_spec o'' in
//   lemma_46_44_is_fine_to_carry_last o''';
//   let o'''' = carry_0_to_1_spec o''' in
//   assert (bounds o'''' p44 (p44+p20) p42);
//   assert (o'''' == fmul_spec s1 s2);
//   assert_norm(p44+p20 < p45);
//   assert_norm(p44 < p45);
//   assert_norm(p42 < p45)

open Hacl.Spec.Bignum.Bigint

val add_and_multiply_tot:
  acc:seqelem{red_y acc} -> block:seqelem{red_26 block} -> r:seqelem{red_26 r} ->
  Tot (acc':seqelem{red_y acc'
    /\ seval acc' % prime = ((seval acc + seval block) * seval r) % prime})
let add_and_multiply_tot acc block r =
  let acc_p_block = fsum_spec acc block in
  lemma_fsum_def acc block;
  lemma_fsum_eval acc block;
  fmul_x_26_is_fine acc_p_block r;
  fmul_spec acc_p_block r


#set-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

private val carry_spec_unrolled:
  s:seqelem{carry_limb_pre s 0} ->
  Tot (s':seqelem{v (Seq.index s' 4) < v (Seq.index s 4) + pow2 (word_size-limb_size)})
private let carry_spec_unrolled s =
  let s1 = carry_limb_step s 0 in
  lemma_carry_limb_step s 0;
  let s2 = carry_limb_step s1 1 in
  lemma_carry_limb_step s1 1;
  let s3 = carry_limb_step s2 2 in
  lemma_carry_limb_step s2 2;
  let s4 = carry_limb_step s3 3 in
  lemma_carry_limb_step s3 3;
  Math.Lemmas.lemma_div_lt (v (Seq.index s3 3)) (word_size) limb_size;
  assert (v (Seq.index s4 4) < v (Seq.index s 4) + pow2 (word_size - limb_size));
  s4

#reset-options "--z3rlimit 100 --initial_fuel 5 --max_fuel 5"

private val lemma_carry_spec_unrolled:
  s:seqelem{carry_limb_pre s 0} -> Lemma (carry_spec_unrolled s == carry_limb_spec s)
let lemma_carry_spec_unrolled s = ()


#set-options "--z3rlimit 20 --max_fuel 0"

val lemma_carried_is_fine_to_carry:
  s:seqelem{bounds s py py py py py} ->
  Lemma (carry_limb_pre s 0 /\ bounds (carry_limb_spec s) p26 p26 p26 p26 (py+p6))
let lemma_carried_is_fine_to_carry s =
  lemma_carry_spec_unrolled s


#set-options "--z3rlimit 50 --max_fuel 0"

val lemma_carry_then_carry_top: s:seqelem{carry_limb_pre s 0} -> Lemma
  (((v (Seq.index s 2) + pow2 (word_size - limb_size))/ pow2 26 < pow2 word_size
    /\ 5 * (v (Seq.index s 2) + pow2 (word_size - limb_size) / pow2 26) + pow2 limb_size < pow2 word_size)
    ==> carry_top_pre (carry_limb_spec s) )
let lemma_carry_then_carry_top s =
  let s' = carry_spec_unrolled s in
  lemma_carry_spec_unrolled s;
  assert (v (Seq.index s' 4) < v (Seq.index s 4) + pow2 (word_size-limb_size));
  Math.Lemmas.nat_times_nat_is_nat 5 (v (Seq.index s 4) + pow2 (word_size-limb_size));
  if ((v (Seq.index s 4) + pow2 (word_size - limb_size))/ pow2 26 < pow2 word_size
    && 5 * (v (Seq.index s 4) + pow2 (word_size - limb_size) / pow2 26) + pow2 limb_size < pow2 word_size) then (
    Math.Lemmas.lemma_div_le (v (Seq.index s' 4)) (v (Seq.index s 4) + pow2 (word_size-limb_size)) (pow2 26);
    assert (v (Seq.index s' 4) / pow2 26 <= (v (Seq.index s 4) + pow2 (word_size-limb_size)) / pow2 26);
    Math.Lemmas.nat_over_pos_is_nat (v (Seq.index s' 4)) (pow2 26);
    Math.Lemmas.nat_over_pos_is_nat (((v (Seq.index s 4)+(pow2 (word_size-limb_size)))/pow2 26)) (pow2 26);
    Math.Lemmas.multiplication_order_lemma (v (Seq.index s' 4) / pow2 26)
                                           ((v (Seq.index s 4)+(pow2 (word_size-limb_size)))/pow2 26) 5;
    assert (5 * (v (Seq.index s' 4) / pow2 26) <= 5 * ((v (Seq.index s 4) + pow2 (word_size-limb_size)) / pow2 26));
    assert (v (Seq.index s' 0) < pow2 limb_size);
    assert (5 * (v (Seq.index s' 4) / pow2 26) + v (Seq.index s' 0) < pow2 word_size)
  )
  else ()



val lemma_carried_is_fine_to_carry_top:
  s:seqelem{bounds s p26 p26 p26 p26 (px + p6)} ->
  Lemma (carry_top_pre s /\ bounds (carry_top_spec s) (p26+5*((px+p6)/p26)) p26 p26 p26 p26)
let lemma_carried_is_fine_to_carry_top s =
  lemma_carry_then_carry_top s;
  lemma_carry_top_spec_ s


val lemma_carried_is_fine_to_carry_last:
  s:seqelem{bounds (s) (p26+5*((px+p6)/p26)) p26 p26 p26 p26} ->
  Lemma (carry_0_to_1_pre s /\ bounds (carry_0_to_1_spec s) p26 (p26+p6) p26 p26 p26)
let lemma_carried_is_fine_to_carry_last s = ()

#reset-options "--initial_fuel 0 --z3rlimit 20"

val last_pass_is_fine:
  s:seqelem{red_y s} ->
  Lemma (carry_limb_pre s 0
    /\ carry_top_pre (carry_limb_spec s)
    /\ carry_0_to_1_pre (carry_top_spec (carry_limb_spec s)))
let last_pass_is_fine s =
  lemma_carried_is_fine_to_carry s;
  let o' = carry_limb_spec s in
  lemma_carried_is_fine_to_carry_top o';
  let o'' = carry_top_spec o' in
  lemma_carried_is_fine_to_carry_last o''
