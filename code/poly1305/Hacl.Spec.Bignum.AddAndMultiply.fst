module Hacl.Spec.Bignum.AddAndMultiply

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Fsum
open Hacl.Spec.Bignum.Fproduct
open Hacl.Spec.Bignum.Fmul
open Hacl.Spec.Bignum.Modulo


#reset-options "--max_fuel 0"

inline_for_extraction let p42 : p:pos{p = 0x40000000000} = assert_norm (pow2 42 = 0x40000000000);
  pow2 42
inline_for_extraction let p43 : p:pos{p = 0x80000000000} = assert_norm (pow2 43 = 0x80000000000);
  pow2 43
inline_for_extraction let p44 : p:pos{p = 0x100000000000} = assert_norm (pow2 44 = 0x100000000000);
  pow2 44
inline_for_extraction let p45 : p:pos{p = 0x200000000000} = assert_norm (pow2 45 = 0x200000000000);
  pow2 45
inline_for_extraction let p46 : p:pos{p = 0x400000000000} = assert_norm (pow2 46 = 0x400000000000);
  pow2 46

let red_44 (s:seqelem) =
  v (Seq.index s 0) < p44 /\ v (Seq.index s 1) < p44 /\ v (Seq.index s 2) < p44
let red_45 (s:seqelem) =
  v (Seq.index s 0) < p45 /\ v (Seq.index s 1) < p45 /\ v (Seq.index s 2) < p45
let red_46 (s:seqelem) =
  v (Seq.index s 0) < p46 /\ v (Seq.index s 1) < p46 /\ v (Seq.index s 2) < p46


#reset-options "--z3rlimit 10 --max_fuel 0"

val fsum_unrolled: s1:seqelem{red s1 len} -> s2:seqelem{red s2 len} -> Tot (s:seqelem{
  v (Seq.index s 0) = v (Seq.index s1 0) + v (Seq.index s2 0)
  /\ v (Seq.index s 1) = v (Seq.index s1 1) + v (Seq.index s2 1)
  /\ v (Seq.index s 2) = v (Seq.index s1 2) + v (Seq.index s2 2)})
let fsum_unrolled a b =
    Math.Lemmas.pow2_double_sum (limb_n-1);
    let open Hacl.Bignum.Limb in
    let c = Seq.upd a 2 ((Seq.index a 2) +^ (Seq.index b 2)) in
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
    /\ v (Seq.index s 2) = v (Seq.index s1 2) + v (Seq.index s2 2))
let lemma_fsum_def s1 s2 =
  lemma_fsum_unrolled s1 s2


#set-options "--z3rlimit 10 --initial_fuel 0 --max_fuel 0"

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
        /\ shift_reduce_pre input2'))


#set-options "--z3rlimit 100 --initial_fuel 1 --max_fuel 1"

private let lemma_mul_shift_reduce_pre_00 (output:seqelem_wide) (input:seqelem) (input2:seqelem) : Lemma
  (mul_shift_reduce_pre_ output input input2 0 <==> true) = ()

#set-options "--z3rlimit 100 --initial_fuel 2 --max_fuel 2"

private let lemma_mul_shift_reduce_pre_0 (output:seqelem_wide) (input:seqelem) (input2:seqelem) : Lemma
  (mul_shift_reduce_pre_ output input input2 1 <==> sum_scalar_multiplication_pre_ output input (Seq.index input2 (len-1)) len) = ()

#set-options "--z3rlimit 100 --initial_fuel 1 --max_fuel 1"

private let lemma_mul_shift_reduce_pre_1 (output:seqelem_wide) (input:seqelem) (input2:seqelem) : Lemma
  (mul_shift_reduce_pre_ output input input2 2 <==> (sum_scalar_multiplication_pre_ output input (Seq.index input2 1) len /\ shift_reduce_pre input /\ mul_shift_reduce_pre_ (sum_scalar_multiplication_spec output input (Seq.index input2 1)) (shift_reduce_spec input) input2 1)) = ()

#set-options "--z3rlimit 100 --initial_fuel 1 --max_fuel 1"

private let lemma_mul_shift_reduce_pre_2 (output:seqelem_wide) (input:seqelem) (input2:seqelem) : Lemma
  (mul_shift_reduce_pre_ output input input2 3 <==> (sum_scalar_multiplication_pre_ output input (Seq.index input2 0) len /\ shift_reduce_pre input /\ mul_shift_reduce_pre_ (sum_scalar_multiplication_spec output input (Seq.index input2 0)) (shift_reduce_spec input) input2 2)) = ()

#set-options "--z3rlimit 10 --initial_fuel 0 --max_fuel 0"

let lemma_mul_shift_reduce_pre (input:seqelem) (input2:seqelem) : Lemma
  (requires (mul_shift_reduce_pre' input input2))
  (ensures (mul_shift_reduce_pre_ (Seq.create len wide_zero) input input2 len))
  = lemma_mul_shift_reduce_pre_2 (Seq.create len wide_zero) input input2;
    let output3 = sum_scalar_multiplication_spec (Seq.create len wide_zero) input (Seq.index input2 0) in
    let input3 = shift_reduce_spec input in
    lemma_mul_shift_reduce_pre_1 output3 input3 input2;
    let output4 = sum_scalar_multiplication_spec output3 input3 (Seq.index input2 1) in
    let input4 = shift_reduce_spec input3 in
    lemma_mul_shift_reduce_pre_0 output4 input4 input2;
    let output5 = sum_scalar_multiplication_spec output4 input4 (Seq.index input2 2) in
    ()


#set-options "--z3rlimit 10 --initial_fuel 1 --max_fuel 1"

let lemma_zero_mod (a:int{a = 0}) (b:pos) : Lemma (a % b = 0) = ()
let lemma_zero_mul (a:int{a = 0}) (b:int) : Lemma (a * b = 0 /\ b * a = 0) = ()

let lemma_mul_shift_reduce_pre2 (input:seqelem) (input2:seqelem) : Lemma
  (requires (mul_shift_reduce_pre' input input2))
  (ensures (mul_shift_reduce_pre (Seq.create len wide_zero) input input input2 len))
  = lemma_mul_shift_reduce_pre input input2;
    assert_norm(pow2 0 = 1);
    lemma_seval_wide_null (Seq.create len wide_zero) len;
    lemma_zero_mod (Hacl.Spec.Bignum.Bigint.seval_wide (Seq.create len wide_zero)) prime;
    lemma_zero_mul (Hacl.Spec.Bignum.Bigint.seval_ input2 0) (Hacl.Spec.Bignum.Bigint.seval input);
    lemma_zero_mod (Hacl.Spec.Bignum.Bigint.seval input * Hacl.Spec.Bignum.Bigint.seval_ input2 0) prime;
    cut (Hacl.Spec.Bignum.Bigint.seval_wide (Seq.create len wide_zero) % prime = (Hacl.Spec.Bignum.Bigint.seval input * Hacl.Spec.Bignum.Bigint.seval_ input2 0) % prime);
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
          /\ shift_reduce_pre input2'))} ->
  Tot (s:seqelem_wide)
private let mul_shift_reduce_unrolled__ input input2 =
  let input_init = input in
  let output = Seq.create len wide_zero in
  let output1   = sum_scalar_multiplication_spec output input (Seq.index input2 0) in
  let input1    = shift_reduce_spec input in
  let output2   = sum_scalar_multiplication_spec output1 input1 (Seq.index input2 1) in
  let input2'   = shift_reduce_spec input1 in
  sum_scalar_multiplication_spec output2 input2' (Seq.index input2 2)


let bounds (s:seqelem) (s0:nat) (s1:nat) (s2:nat) : GTot Type0 =
  v (Seq.index s 0) < s0 /\ v (Seq.index s 1) < s1 /\ v (Seq.index s 2) < s2

let bounds' (s:seqelem_wide) (s0:nat) (s1:nat) (s2:nat) : GTot Type0 =
  w (Seq.index s 0) < s0 /\ w (Seq.index s 1) < s1 /\ w (Seq.index s 2) < s2


private let sum_scalar_multiplication_pre_' (sw:seqelem_wide) (s:seqelem) (scalar:limb) =
  w (Seq.index sw 0) + (v (Seq.index s 0) * v scalar) < pow2 wide_n
  /\ w (Seq.index sw 1) + (v (Seq.index s 1) * v scalar) < pow2 wide_n
  /\ w (Seq.index sw 2) + (v (Seq.index s 2) * v scalar) < pow2 wide_n


val lemma_sum_scalar_muitiplication_pre_:
  sw:seqelem_wide -> s:seqelem -> scalar:limb ->
  Lemma (sum_scalar_multiplication_pre_ sw s scalar len <==>
    (sum_scalar_multiplication_pre_' sw s scalar))
let lemma_sum_scalar_muitiplication_pre_ sw s scalar = ()


val lemma_mul_ineq: a:nat -> b:nat -> c:nat -> d:nat -> Lemma
  (requires (a < c /\ b < d))
  (ensures (a * b < c * d))
let lemma_mul_ineq a b c d = ()

#set-options "--z3rlimit 10 --initial_fuel 0 --max_fuel 0"

val lemma_reduce_spec_: s:seqelem{reduce_pre s} -> Lemma
  (let s' = reduce_spec s in
    v (Seq.index s' 0) = 20 * v (Seq.index s 0)
    /\ v (Seq.index s' 1) = v (Seq.index s 1)
    /\ v (Seq.index s' 2) = v (Seq.index s 2) )
let lemma_reduce_spec_ s =
  assert_norm(pow2 4 = 16);
  assert_norm(pow2 2 = 4);
  let open Hacl.Bignum.Limb in
  let s0 = Seq.index s 0 in
  let s0_16 = s0 <<^ 4ul in
  Math.Lemmas.modulo_lemma (v s0 * 16) (pow2 64);
  let s0_4 = s0 <<^ 2ul in
  Math.Lemmas.modulo_lemma (v s0 * 4) (pow2 64);
  let s0_20 = s0_16 +^ s0_4 in
  let s' = Seq.upd s 0 s0_20 in
  cut (s' == reduce_spec s);
  cut (Seq.index s 1 == Seq.index s' 1);
  cut (Seq.index s 2 == Seq.index s' 2);
  Math.Lemmas.modulo_lemma (v s0 * 16) (pow2 64);
  Math.Lemmas.modulo_lemma (v s0 * 4) (pow2 64)


val lemma_shift_reduce_spec_: s:seqelem{shift_reduce_pre s} -> Lemma
  (let s' = shift_reduce_spec s in
    v (Seq.index s' 0) = 20 * v (Seq.index s 2)
    /\ v (Seq.index s' 1) = v (Seq.index s 0)
    /\ v (Seq.index s' 2) = v (Seq.index s 1) )
let lemma_shift_reduce_spec_ s =
  let s0 = Seq.index s 2 in
  let s' = shift_spec s in
  let s'' = reduce_spec s' in
  cut (v (Seq.index s 2) = v (Seq.index s' 0));
  cut (v (Seq.index s 1) = v (Seq.index s' 2));
  cut (v (Seq.index s 0) = v (Seq.index s' 1));
  lemma_reduce_spec_ s'


val lemma_sum_scalar_muitiplication_spec_: sw:seqelem_wide -> s:seqelem -> sc:limb ->
  Lemma (requires (sum_scalar_multiplication_pre_ sw s sc len))
        (ensures (sum_scalar_multiplication_pre_ sw s sc len
          /\ (let sw' = sum_scalar_multiplication_spec sw s sc in
             w (Seq.index sw' 0) = w (Seq.index sw 0) + (v (Seq.index s 0) * v sc)
             /\ w (Seq.index sw' 1) = w (Seq.index sw 1) + (v (Seq.index s 1) * v sc)
             /\ w (Seq.index sw' 2) = w (Seq.index sw 2) + (v (Seq.index s 2) * v sc)) ))
let lemma_sum_scalar_muitiplication_spec_ sw s sc = ()

inline_for_extraction let p90 : p:pos{p = 0x40000000000000000000000} = assert_norm(pow2 90 = 0x40000000000000000000000); pow2 90

val lemma_shift_reduce_then_carry_wide_0:
  s1:seqelem{red_46 s1} ->
  s2:seqelem{red_44 s2} ->
  Lemma (sum_scalar_multiplication_pre_ (Seq.create len wide_zero) s1 (Seq.index s2 0) len
    /\ shift_reduce_pre s1
    /\ bounds (shift_reduce_spec s1) (20 * p46) p46 p46
    /\ bounds' (sum_scalar_multiplication_spec (Seq.create len wide_zero) s1 (Seq.index s2 0))
              p90 p90 p90)
let lemma_shift_reduce_then_carry_wide_0 s1 s2 =
  assert_norm (pow2 64 = 0x10000000000000000);
  assert_norm (pow2 wide_n = 0x100000000000000000000000000000000);
  let bla = Seq.create len wide_zero in
  cut (w (Seq.index bla 0) = 0); cut (w (Seq.index bla 1) = 0); cut (w (Seq.index bla 2) = 0);
  lemma_mul_ineq (v (Seq.index s1 0)) (v (Seq.index s2 0)) p46 p44;
  lemma_mul_ineq (v (Seq.index s1 1)) (v (Seq.index s2 0)) p46 p44;
  lemma_mul_ineq (v (Seq.index s1 2)) (v (Seq.index s2 0)) p46 p44;
  assert_norm(p90 = p46 * p44);
  cut (sum_scalar_multiplication_pre_' bla s1 (Seq.index s2 0));
  lemma_sum_scalar_muitiplication_pre_ bla s1 (Seq.index s2 0);
  lemma_shift_reduce_spec_ s1;
  let s1' = shift_reduce_spec s1 in
  Math.Lemmas.pow2_plus 46 44


val lemma_shift_reduce_then_carry_wide_1:
  o:seqelem_wide{bounds' o p90 p90 p90} ->
  s1:seqelem{bounds s1 (20*p46) p46 p46} ->
  s2:seqelem{red_44 s2} ->
  Lemma (sum_scalar_multiplication_pre_ o s1 (Seq.index s2 1) len
    /\ shift_reduce_pre s1
    /\ bounds (shift_reduce_spec s1) (20 * p46) (20 * p46) p46
    /\ bounds' (sum_scalar_multiplication_spec o s1 (Seq.index s2 1))
              (21 * p90) (2*p90) (2*p90) )
let lemma_shift_reduce_then_carry_wide_1 o s1 s2 =
  assert_norm (pow2 64 = 0x10000000000000000);
  assert_norm (pow2 wide_n = 0x100000000000000000000000000000000);
  lemma_mul_ineq (v (Seq.index s1 0)) (v (Seq.index s2 1)) (20 * p46) p44;
  lemma_mul_ineq (v (Seq.index s1 1)) (v (Seq.index s2 1)) p46 p44;
  lemma_mul_ineq (v (Seq.index s1 2)) (v (Seq.index s2 1)) p46 p44;
  cut (sum_scalar_multiplication_pre_' o s1 (Seq.index s2 1));
  lemma_sum_scalar_muitiplication_pre_ o s1 (Seq.index s2 1);
  lemma_shift_reduce_spec_ s1;
  let s1' = shift_reduce_spec s1 in
  Math.Lemmas.pow2_plus 46 44

#set-options "--z3rlimit 20"

val lemma_shift_reduce_then_carry_wide_2:
  o:seqelem_wide{bounds' o (21*p90) (2*p90) (2*p90)} ->
  s1:seqelem{bounds s1 (20*p46) (20*p46) p46} ->
  s2:seqelem{red_44 s2} ->
  Lemma (sum_scalar_multiplication_pre_ o s1 (Seq.index s2 2) len
    /\ shift_reduce_pre s1
    /\ bounds (shift_reduce_spec s1) (20 * p46) (20 *p46) (20*p46)
    /\ bounds' (sum_scalar_multiplication_spec o s1 (Seq.index s2 2))
              (41 * p90) (22*p90) (3*p90) )
let lemma_shift_reduce_then_carry_wide_2 o s1 s2 =
  assert_norm (pow2 64 = 0x10000000000000000);
  assert_norm (pow2 wide_n = 0x100000000000000000000000000000000);
  lemma_mul_ineq (v (Seq.index s1 0)) (v (Seq.index s2 2)) (20*p46) p44;
  lemma_mul_ineq (v (Seq.index s1 1)) (v (Seq.index s2 2)) (20*p46) p44;
  lemma_mul_ineq (v (Seq.index s1 2)) (v (Seq.index s2 2)) p46 p44;
  cut (sum_scalar_multiplication_pre_' o s1 (Seq.index s2 2));
  lemma_sum_scalar_muitiplication_pre_ o s1 (Seq.index s2 2);
  lemma_shift_reduce_spec_ s1;
  let s1' = shift_reduce_spec s1 in
  Math.Lemmas.pow2_plus 46 44


#set-options "--z3rlimit 10 --initial_fuel 2 --max_fuel 2"

private 
val mul_shift_reduce_unrolled_0:
  output:seqelem_wide ->
  input_init:seqelem ->
  input:seqelem ->
  input2:seqelem{mul_shift_reduce_pre output input_init input input2 len} ->
  (* Tot (s:seqelem_wide{s == mul_shift_reduce_spec_ output input_init input input2 1}) *)
  Tot (t:tuple2 seqelem_wide seqelem{t == mul_shift_reduce_spec_ output input_init input input2 2})
#reset-options "--z3rlimit 25 --initial_fuel 1 --max_fuel 1"
let mul_shift_reduce_unrolled_0 output input_init input input2 =
  lemma_mul_shift_reduce_spec_def_0 output input_init input input2;
  lemma_mul_shift_reduce_spec_def output input_init input input2 2;
  let ctr = 2 in
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
  Tot (t:tuple2 seqelem_wide seqelem{t == mul_shift_reduce_spec_ output input_init input input2 1})
let mul_shift_reduce_unrolled_1 output0 input_init input0 input2 =
  let output, input = mul_shift_reduce_unrolled_0 output0 input_init input0 input2 in
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
  let output, input = mul_shift_reduce_unrolled_1 output0 input_init input0 input2 in
  let ctr = 0 in
  lemma_mul_shift_reduce_spec_def output0 input_init input0 input2 ctr;
  let i = ctr in
  let j = len - i - 1 in
  let input2j = Seq.index input2 j in
  let output' = sum_scalar_multiplication_spec output input input2j in
  lemma_sum_scalar_multiplication_ output input input2j len;
  output'


(* #set-options "--z3rlimit 10 --initial_fuel 2 --max_fuel 2" *)

(* private val mul_shift_reduce_unrolled_: *)
(*   output:seqelem_wide -> *)
(*   input_init:seqelem -> *)
(*   input:seqelem -> *)
(*   input2:seqelem{mul_shift_reduce_pre output input_init input input2 3} -> *)
(*   Tot (s:seqelem_wide{s == mul_shift_reduce_spec_ output input_init input input2 3}) *)
(* private let mul_shift_reduce_unrolled_ output input_init input input2 = *)
(*   let output1   = sum_scalar_multiplication_spec output input (Seq.index input2 0) in *)
(*   lemma_sum_scalar_multiplication_ output input (Seq.index input2 0) len; *)
(*   let input1    = shift_reduce_spec input in *)
(*   lemma_shift_reduce_spec input; *)
(*   lemma_mul_shift_reduce_spec_1 output1 output input_init input input1 input2 (v (Seq.index input2 0)) 3; *)
(*   mul_shift_reduce_unrolled_1 output1 input_init input1 input2 *)


private val shift_reduce_unrolled:
  input:seqelem ->
  input2:seqelem{mul_shift_reduce_pre (Seq.create len wide_zero) input input input2 len} ->
  Tot (s:seqelem_wide{s == mul_shift_reduce_spec input input2})
private let shift_reduce_unrolled input input2 =
  mul_shift_reduce_unrolled_ (Seq.create len wide_zero) input input input2

#reset-options "--z3rlimit 50 --initial_fuel 0 --max_fuel 0"

val lemma_mul_shift_reduce_unrolled: input:seqelem -> input2:seqelem -> Lemma
  (requires (mul_shift_reduce_pre' input input2))
  (ensures (mul_shift_reduce_pre (Seq.create len wide_zero) input input input2 len
  /\ mul_shift_reduce_pre' input input2
  /\ mul_shift_reduce_unrolled__ input input2 == mul_shift_reduce_spec input input2))
let lemma_mul_shift_reduce_unrolled input input2 =
  lemma_mul_shift_reduce_pre2 input input2;
  let s = shift_reduce_unrolled input input2 in
  cut (s == mul_shift_reduce_unrolled__ input input2)

val lemma_shift_reduce_then_carry_wide:
  s1:seqelem{red_46 s1} -> s2:seqelem{red_44 s2} ->
  Lemma (mul_shift_reduce_pre' s1 s2 /\
    bounds' (mul_shift_reduce_unrolled__ s1 s2) (41 * p90) (22*p90) (3*p90) )
let lemma_shift_reduce_then_carry_wide s1 s2 =
  lemma_shift_reduce_then_carry_wide_0 s1 s2;
  let o1 = sum_scalar_multiplication_spec (Seq.create len wide_zero) s1 (Seq.index s2 0) in
  let s11 = shift_reduce_spec s1 in
  lemma_shift_reduce_then_carry_wide_1 o1 s11 s2;

  let o2 = sum_scalar_multiplication_spec o1 s11 (Seq.index s2 1) in
  let s12 = shift_reduce_spec s11 in
  lemma_shift_reduce_then_carry_wide_2 o2 s12 s2


private val carry_wide_spec_unrolled:
  s:seqelem_wide{carry_wide_pre s 0} ->
  Tot (s':seqelem_wide{w (Seq.index s' 2) < w (Seq.index s 2) + pow2 (2*word_size-limb_size)})
private let carry_wide_spec_unrolled s =
  let s1 = carry_wide_step s 0 in
  lemma_carry_wide_step s 0;
  let s2 = carry_wide_step s1 1 in
  lemma_carry_wide_step s1 1;
  Math.Lemmas.lemma_div_lt (w (Seq.index s1 1)) (2*word_size) limb_size;
  cut (w (Seq.index s2 2) < w (Seq.index s 2) + pow2 (2*word_size - limb_size));
  s2


#set-options "--z3rlimit 20 --initial_fuel 5 --max_fuel 5"

private val lemma_carry_wide_spec_unrolled:
  s:seqelem_wide{carry_wide_pre s 0} -> Lemma (carry_wide_spec_unrolled s == carry_wide_spec s)
let lemma_carry_wide_spec_unrolled s = ()

#set-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

inline_for_extraction let p84 : p:pos{p = 0x1000000000000000000000} = assert_norm (pow2 84 = 0x1000000000000000000000); pow2 84

#set-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

val lemma_46_44_is_fine_to_carry:
  s:seqelem_wide{bounds' s (41*p90) (22*p90) (3*p90)} ->
  Lemma (carry_wide_pre s 0 /\ bounds' (carry_wide_spec s) p44 p44 (3*p90+p84))
let lemma_46_44_is_fine_to_carry s =
  assert_norm (pow2 64 = 0x10000000000000000);
  assert_norm (pow2 wide_n = 0x100000000000000000000000000000000);
  assert_norm (pow2 (wide_n-1) = 0x80000000000000000000000000000000);
  lemma_carry_wide_spec_unrolled s


#set-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

val lemma_copy_then_carry: s:seqelem_wide -> Lemma
  ((copy_from_wide_pre s /\ (w (Seq.index s 0) < pow2 word_size /\ w (Seq.index s 1) < pow2 limb_size
    /\ w (Seq.index s 2) < pow2 limb_size)) ==>
     (carry_0_to_1_pre (copy_from_wide_spec s) ))
let lemma_copy_then_carry s = ()


val lemma_carry_top_wide_then_copy: s:seqelem_wide{carry_top_wide_pre s} -> Lemma
  ((w (Seq.index s 0) + 5 * (w (Seq.index s 2) / p42) < pow2 word_size /\ w (Seq.index s 1) < pow2 word_size) ==> copy_from_wide_pre (carry_top_wide_spec s))
let lemma_carry_top_wide_then_copy s =
  lemma_carry_top_wide_spec_ s;
  assert_norm(pow2 64 > pow2 44);
  assert_norm(pow2 64 > pow2 42)


#set-options "--z3rlimit 50 --initial_fuel 0 --max_fuel 0"

val lemma_carry_wide_then_carry_top: s:seqelem_wide{carry_wide_pre s 0} -> Lemma
  (((w (Seq.index s 2) + pow2 (2*word_size - limb_size))/ pow2 42 < pow2 word_size
    /\ 5 * (w (Seq.index s 2) + pow2 (2*word_size - limb_size) / pow2 42) + pow2 limb_size < pow2 word_size)
    ==> carry_top_wide_pre (carry_wide_spec s) )
let lemma_carry_wide_then_carry_top s =
  let s' = carry_wide_spec_unrolled s in
  lemma_carry_wide_spec_unrolled s;
  cut (w (Seq.index s' 2) < w (Seq.index s 2) + pow2 (2*word_size-limb_size));
  Math.Lemmas.nat_times_nat_is_nat 5 (w (Seq.index s 2) + pow2 (2*word_size-limb_size));
  if ((w (Seq.index s 2) + pow2 (2*word_size - limb_size))/ pow2 42 < pow2 word_size
    && 5 * (w (Seq.index s 2) + pow2 (2*word_size - limb_size) / pow2 42) + pow2 limb_size < pow2 word_size) then (
    Math.Lemmas.lemma_div_le (w (Seq.index s' 2)) (w (Seq.index s 2) + pow2 (2*word_size-limb_size)) (pow2 42);
    cut (w (Seq.index s' 2) / pow2 42 <= (w (Seq.index s 2) + pow2 (2*word_size-limb_size)) / pow2 42);
    Math.Lemmas.nat_over_pos_is_nat (w (Seq.index s' 2)) (pow2 42);
    Math.Lemmas.nat_over_pos_is_nat (((w (Seq.index s 2)+(pow2 (2*word_size-limb_size)))/pow2 42)) (pow2 42);
    Math.Lemmas.multiplication_order_lemma (w (Seq.index s' 2) / pow2 42)
                                           ((w (Seq.index s 2)+(pow2 (2*word_size-limb_size)))/pow2 42) 5;
    cut (5 * (w (Seq.index s' 2) / pow2 42) <= 5 * ((w (Seq.index s 2) + pow2 (2*word_size-limb_size)) / pow2 42));
    cut (w (Seq.index s' 0) < pow2 limb_size);
    cut (5 * (w (Seq.index s' 2) / pow2 42) + w (Seq.index s' 0) < pow2 word_size);
    Math.Lemmas.pow2_lt_compat (2*word_size) word_size
  )
  else ()



val lemma_46_44_is_fine_to_carry_top:
  s:seqelem_wide{bounds' s p44 p44 (3*p90+p84)} ->
  Lemma (carry_top_wide_pre s /\ bounds' (carry_top_wide_spec s) (p44+5*((3*p90+p84)/p42)) p44 p42)
let lemma_46_44_is_fine_to_carry_top s =
  assert_norm (pow2 64 = 0x10000000000000000);
  assert_norm (pow2 wide_n = 0x100000000000000000000000000000000);
  assert_norm (pow2 (wide_n-1) = 0x80000000000000000000000000000000);
  lemma_carry_wide_then_carry_top s;
  lemma_carry_top_wide_spec_ s


val lemma_46_44_is_fine_to_copy:
  s:seqelem_wide{bounds' (s) (p44+5*((3*p90+p84)/p42)) p44 p42} ->
  Lemma (copy_from_wide_pre s /\ bounds (copy_from_wide_spec s) (p44+5*((3*p90+p84)/p42)) p44 p42)
let lemma_46_44_is_fine_to_copy s =
  assert_norm (pow2 64 = 0x10000000000000000);
  assert_norm (pow2 wide_n = 0x100000000000000000000000000000000);
  assert_norm (pow2 (wide_n-1) = 0x80000000000000000000000000000000)


inline_for_extraction let p20 : p:pos{p = 0x100000} = assert_norm(pow2 20 = 0x100000); pow2 20

val lemma_46_44_is_fine_to_carry_last:
  s:seqelem{bounds (s) (p44+5*((3*p90+p84)/p42)) p44 p42} ->
  Lemma (carry_0_to_1_pre s /\ bounds (carry_0_to_1_spec s) p44 (p44+p20) p42)
let lemma_46_44_is_fine_to_carry_last s =
  assert_norm (pow2 64 = 0x10000000000000000);
  assert_norm (pow2 wide_n = 0x100000000000000000000000000000000);
  assert_norm (pow2 (wide_n-1) = 0x80000000000000000000000000000000)


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val fmul_46_44_is_fine:
  s1:seqelem{red_46 s1} -> s2:seqelem{red_44 s2} ->
  Lemma (fmul_pre s1 s2 /\ red_45 (fmul_spec s1 s2))
let fmul_46_44_is_fine s1 s2 =
  lemma_shift_reduce_then_carry_wide s1 s2;
  lemma_mul_shift_reduce_unrolled s1 s2;
  let o = mul_shift_reduce_spec s1 s2 in
  lemma_46_44_is_fine_to_carry o;
  let o' = carry_wide_spec o in
  lemma_46_44_is_fine_to_carry_top o';
  let o'' = carry_top_wide_spec o' in
  lemma_46_44_is_fine_to_copy o'';
  let o''' = copy_from_wide_spec o'' in
  lemma_46_44_is_fine_to_carry_last o''';
  let o'''' = carry_0_to_1_spec o''' in
  cut (bounds o'''' p44 (p44+p20) p42);
  cut (o'''' == fmul_spec s1 s2);
  assert_norm(p44+p20 < p45);
  assert_norm(p44 < p45);
  assert_norm(p42 < p45)

open Hacl.Spec.Bignum.Bigint

val add_and_multiply_tot:
  acc:seqelem{red_45 acc} -> block:seqelem{red_44 block} -> r:seqelem{red_44 r} ->
  Tot (acc':seqelem{red_45 acc'
    /\ seval acc' % prime = ((seval acc + seval block) * seval r) % prime})
let add_and_multiply_tot acc block r =
  assert_norm(pow2 63 = 0x8000000000000000);
  let acc_p_block = fsum_spec acc block in
  lemma_fsum_def acc block;
  lemma_fsum_eval acc block;
  fmul_46_44_is_fine acc_p_block r;
  fmul_spec acc_p_block r


#set-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

private val carry_spec_unrolled:
  s:seqelem{carry_limb_pre s 0} ->
  Tot (s':seqelem{v (Seq.index s' 2) < v (Seq.index s 2) + pow2 (word_size-limb_size)})
private let carry_spec_unrolled s =
  let s1 = carry_limb_step s 0 in
  lemma_carry_limb_step s 0;
  let s2 = carry_limb_step s1 1 in
  lemma_carry_limb_step s1 1;
  Math.Lemmas.lemma_div_lt (v (Seq.index s1 1)) (word_size) limb_size;
  cut (v (Seq.index s2 2) < v (Seq.index s 2) + pow2 (word_size - limb_size));
  s2


#reset-options "--z3rlimit 50 --initial_fuel 5 --max_fuel 5"

private val lemma_carry_spec_unrolled:
  s:seqelem{carry_limb_pre s 0} -> Lemma (carry_spec_unrolled s == carry_limb_spec s)
let lemma_carry_spec_unrolled s = ()


#set-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

val lemma_carried_is_fine_to_carry:
  s:seqelem{bounds s p45 p45 p45} ->
  Lemma (carry_limb_pre s 0 /\ bounds (carry_limb_spec s) p44 p44 (p45+p20))
let lemma_carried_is_fine_to_carry s =
  assert_norm (pow2 64 = 0x10000000000000000);
  assert_norm (pow2 (limb_n-1) = 0x8000000000000000);
  lemma_carry_spec_unrolled s


#set-options "--z3rlimit 50 --initial_fuel 0 --max_fuel 0"

val lemma_carry_then_carry_top: s:seqelem{carry_limb_pre s 0} -> Lemma
  (((v (Seq.index s 2) + pow2 (word_size - limb_size))/ pow2 42 < pow2 word_size
    /\ 5 * (v (Seq.index s 2) + pow2 (word_size - limb_size) / pow2 42) + pow2 limb_size < pow2 word_size)
    ==> carry_top_pre (carry_limb_spec s) )
let lemma_carry_then_carry_top s =
  let s' = carry_spec_unrolled s in
  lemma_carry_spec_unrolled s;
  cut (v (Seq.index s' 2) < v (Seq.index s 2) + pow2 (word_size-limb_size));
  Math.Lemmas.nat_times_nat_is_nat 5 (v (Seq.index s 2) + pow2 (word_size-limb_size));
  if ((v (Seq.index s 2) + pow2 (word_size - limb_size))/ pow2 42 < pow2 word_size
    && 5 * (v (Seq.index s 2) + pow2 (word_size - limb_size) / pow2 42) + pow2 limb_size < pow2 word_size) then (
    Math.Lemmas.lemma_div_le (v (Seq.index s' 2)) (v (Seq.index s 2) + pow2 (word_size-limb_size)) (pow2 42);
    cut (v (Seq.index s' 2) / pow2 42 <= (v (Seq.index s 2) + pow2 (word_size-limb_size)) / pow2 42);
    Math.Lemmas.nat_over_pos_is_nat (v (Seq.index s' 2)) (pow2 42);
    Math.Lemmas.nat_over_pos_is_nat (((v (Seq.index s 2)+(pow2 (word_size-limb_size)))/pow2 42)) (pow2 42);
    Math.Lemmas.multiplication_order_lemma (v (Seq.index s' 2) / pow2 42)
                                           ((v (Seq.index s 2)+(pow2 (word_size-limb_size)))/pow2 42) 5;
    cut (5 * (v (Seq.index s' 2) / pow2 42) <= 5 * ((v (Seq.index s 2) + pow2 (word_size-limb_size)) / pow2 42));
    cut (v (Seq.index s' 0) < pow2 limb_size);
    cut (5 * (v (Seq.index s' 2) / pow2 42) + v (Seq.index s' 0) < pow2 word_size)
  )
  else ()



val lemma_carried_is_fine_to_carry_top:
  s:seqelem{bounds s p44 p44 (p45 + p20)} ->
  Lemma (carry_top_pre s /\ bounds (carry_top_spec s) (p44+5*((p45+p20)/p42)) p44 p42)
let lemma_carried_is_fine_to_carry_top s =
  assert_norm (pow2 64 = 0x10000000000000000);
  assert_norm (pow2 wide_n = 0x100000000000000000000000000000000);
  assert_norm (pow2 (63) = 0x8000000000000000);
  lemma_carry_then_carry_top s;
  lemma_carry_top_spec_ s


val lemma_carried_is_fine_to_carry_last:
  s:seqelem{bounds (s) (p44+5*((p45+p20)/p42)) p44 p42} ->
  Lemma (carry_0_to_1_pre s /\ bounds (carry_0_to_1_spec s) p44 (p44+p20) p42)
let lemma_carried_is_fine_to_carry_last s =
  assert_norm (pow2 64 = 0x10000000000000000)


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val last_pass_is_fine:
  s:seqelem{red_45 s} ->
  Lemma (carry_limb_pre s 0
    /\ carry_top_pre (carry_limb_spec s)
    /\ carry_0_to_1_pre (carry_top_spec (carry_limb_spec s)))
let last_pass_is_fine s =
  lemma_carried_is_fine_to_carry s;
  let o' = carry_limb_spec s in
  lemma_carried_is_fine_to_carry_top o';
  let o'' = carry_top_spec o' in
  lemma_carried_is_fine_to_carry_last o''
