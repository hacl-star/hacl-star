module Hacl.Spec.EC.AddAndDouble

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul
open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Fsum
open Hacl.Spec.Bignum.Fdifference
open Hacl.Spec.Bignum.Fproduct
open Hacl.Spec.Bignum.Modulo
open Hacl.Spec.Bignum.Fmul
open Hacl.Spec.Bignum


val bound_by: seqelem -> nat -> Type0
let bound_by s x =
  let _ = () in
  (forall (i:nat). {:pattern (v (Seq.index s i))} i < len ==> v (Seq.index s i) < x)


val smax: seqelem -> nat -> Type0
let smax s x =
  let _ = () in
  v (Seq.index s 0) < x /\ v (Seq.index s 1) < x /\ v (Seq.index s 2) < x
  /\ v (Seq.index s 3) < x /\ v (Seq.index s 4) < x


inline_for_extraction let p52 : p:pos{p = 0x10000000000000} =
  assert_norm(pow2 52 = 0x10000000000000); pow2 52
inline_for_extraction let p53 : p:pos{p = 0x20000000000000} =
  assert_norm(pow2 53 = 0x20000000000000); pow2 53
inline_for_extraction let p55 : p:pos{p = 0x80000000000000} =
  assert_norm(pow2 55 = 0x80000000000000); pow2 55


inline_for_extraction let p513 : p:pos{p = pow2 51 + pow2 13} = assert_norm(2251799813693440 = pow2 51 + pow2 13); 2251799813693440
inline_for_extraction let p5413 : p:pos{p = pow2 54 + pow2 51 + pow2 13} =
  assert_norm(20266198323175424 = pow2 54 + pow2 51 + pow2 13); 20266198323175424


let red_52 s = smax s p52
let red_53 s = smax s p53
let red_55 s = smax s p55

let bounds (s:seqelem) (s0:nat) (s1:nat) (s2:nat) (s3:nat) (s4:nat) : GTot Type0 =
  v (Seq.index s 0) < s0 /\ v (Seq.index s 1) < s1 /\ v (Seq.index s 2) < s2
  /\ v (Seq.index s 3) < s3 /\ v (Seq.index s 4) < s4

let bounds' (s:seqelem_wide) (s0:nat) (s1:nat) (s2:nat) (s3:nat) (s4:nat) : GTot Type0 =
  w (Seq.index s 0) < s0 /\ w (Seq.index s 1) < s1 /\ w (Seq.index s 2) < s2
  /\ w (Seq.index s 3) < s3 /\ w (Seq.index s 4) < s4

let red_513 (s:seqelem) : GTot Type0 =
  bounds s p513 p513 p513 p513 p513
let red_5413 (s:seqelem) : GTot Type0 =
  bounds s p5413 p5413 p5413 p5413 p5413


#set-options "--z3rlimit 10 --initial_fuel 0 --max_fuel 0"

val fsum_unrolled: s1:seqelem{red s1 len} -> s2:seqelem{red s2 len} -> Tot (s:seqelem{
  v (Seq.index s 0) = v (Seq.index s1 0) + v (Seq.index s2 0)
  /\ v (Seq.index s 1) = v (Seq.index s1 1) + v (Seq.index s2 1)
  /\ v (Seq.index s 2) = v (Seq.index s1 2) + v (Seq.index s2 2)
  /\ v (Seq.index s 3) = v (Seq.index s1 3) + v (Seq.index s2 3)
  /\ v (Seq.index s 4) = v (Seq.index s1 4) + v (Seq.index s2 4)})
let fsum_unrolled a b =
    Math.Lemmas.pow2_double_sum (limb_n-1);
    let open Hacl.Bignum.Limb in
    let c = Seq.upd a 4 ((Seq.index a 4) +^ (Seq.index b 4)) in
    let c = Seq.upd c 3 ((Seq.index a 3) +^ (Seq.index b 3)) in
    let c = Seq.upd c 2 ((Seq.index a 2) +^ (Seq.index b 2)) in
    let c = Seq.upd c 1 ((Seq.index a 1) +^ (Seq.index b 1)) in
    let c = Seq.upd c 0 ((Seq.index a 0) +^ (Seq.index b 0)) in
    c


#reset-options "--z3rlimit 40 --initial_fuel 0 --max_fuel 0"

val lemma_fsum_unrolled: s1:seqelem{red s1 len} -> s2:seqelem{red s2 len} -> Lemma
  (fsum_unrolled s1 s2 == fsum_spec s1 s2)
let lemma_fsum_unrolled s1 s2 =
  Seq.lemma_eq_intro (fsum_unrolled s1 s2) (fsum_spec s1 s2)


#set-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

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


#set-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

val fdifference_unrolled: s1:seqelem -> s2:seqelem{gte_limbs s1 s2 len} -> Tot (s:seqelem{
  v (Seq.index s 0) = v (Seq.index s2 0) - v (Seq.index s1 0)
  /\ v (Seq.index s 1) = v (Seq.index s2 1) - v (Seq.index s1 1)
  /\ v (Seq.index s 2) = v (Seq.index s2 2) - v (Seq.index s1 2)
  /\ v (Seq.index s 3) = v (Seq.index s2 3) - v (Seq.index s1 3)
  /\ v (Seq.index s 4) = v (Seq.index s2 4) - v (Seq.index s1 4)})
let fdifference_unrolled a b =
    let open Hacl.Bignum.Limb in
    let c = Seq.upd a 4 ((Seq.index b 4) -^ (Seq.index a 4)) in
    let c = Seq.upd c 3 ((Seq.index b 3) -^ (Seq.index a 3)) in
    let c = Seq.upd c 2 ((Seq.index b 2) -^ (Seq.index a 2)) in
    let c = Seq.upd c 1 ((Seq.index b 1) -^ (Seq.index a 1)) in
    let c = Seq.upd c 0 ((Seq.index b 0) -^ (Seq.index a 0)) in
    c


#set-options "--z3rlimit 40 --initial_fuel 0 --max_fuel 0"

val lemma_fdifference_unrolled: s1:seqelem -> s2:seqelem{gte_limbs s1 s2 len} -> Lemma
  (fdifference_unrolled s1 s2 == fdifference_spec s1 s2)
let lemma_fdifference_unrolled s1 s2 =
  Seq.lemma_eq_intro (fdifference_unrolled s1 s2) (fdifference_spec s1 s2)


#set-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

val lemma_fdifference_def:
  s1:seqelem -> s2:seqelem{gte_limbs s1 s2 len} ->
  Lemma (let s = fdifference_spec s1 s2 in
    v (Seq.index s 0) = v (Seq.index s2 0) - v (Seq.index s1 0)
    /\ v (Seq.index s 1) = v (Seq.index s2 1) - v (Seq.index s1 1)
    /\ v (Seq.index s 2) = v (Seq.index s2 2) - v (Seq.index s1 2)
    /\ v (Seq.index s 3) = v (Seq.index s2 3) - v (Seq.index s1 3)
    /\ v (Seq.index s 4) = v (Seq.index s2 4) - v (Seq.index s1 4))
let lemma_fdifference_def s1 s2 =
  lemma_fdifference_unrolled s1 s2


val fdifference_unrolled': s1:seqelem{red_52 s1}-> s2:seqelem{red_52 s2} -> Tot (s:seqelem{
  red_55 s
  /\ v (Seq.index s 0) = 0x3fffffffffff68 + v (Seq.index s2 0) - v (Seq.index s1 0)
  /\ v (Seq.index s 1) = 0x3ffffffffffff8 + v (Seq.index s2 1) - v (Seq.index s1 1)
  /\ v (Seq.index s 2) = 0x3ffffffffffff8 + v (Seq.index s2 2) - v (Seq.index s1 2)
  /\ v (Seq.index s 3) = 0x3ffffffffffff8 + v (Seq.index s2 3) - v (Seq.index s1 3)
  /\ v (Seq.index s 4) = 0x3ffffffffffff8 + v (Seq.index s2 4) - v (Seq.index s1 4)})
let fdifference_unrolled' a b =
  assert_norm(pow2 52 = 0x10000000000000);
  assert_norm(pow2 63 = 0x8000000000000000);
  let b' = add_zero_spec b in
  lemma_add_zero_spec_ b;
  let b'' = fdifference_unrolled a b' in
  b''


val fdifference_unrolled'': s1:seqelem{red_513 s1}-> s2:seqelem{red_513 s2} -> Tot (s:seqelem{
  red_5413 s
  /\ v (Seq.index s 0) = 0x3fffffffffff68 + v (Seq.index s2 0) - v (Seq.index s1 0)
  /\ v (Seq.index s 1) = 0x3ffffffffffff8 + v (Seq.index s2 1) - v (Seq.index s1 1)
  /\ v (Seq.index s 2) = 0x3ffffffffffff8 + v (Seq.index s2 2) - v (Seq.index s1 2)
  /\ v (Seq.index s 3) = 0x3ffffffffffff8 + v (Seq.index s2 3) - v (Seq.index s1 3)
  /\ v (Seq.index s 4) = 0x3ffffffffffff8 + v (Seq.index s2 4) - v (Seq.index s1 4)})
let fdifference_unrolled'' a b =
  assert_norm(pow2 63 = 0x8000000000000000);
  let b' = add_zero_spec b in
  lemma_add_zero_spec_ b;
  let b'' = fdifference_unrolled a b' in
  b''


#set-options "--z3rlimit 10 --initial_fuel 0 --max_fuel 0"

val lemma_fdifference_unrolled': s1:seqelem{red_52 s1} -> s2:seqelem{red_52 s2} -> Lemma
  (add_zero_pre s2 /\ gte_limbs s1 (add_zero_spec s2) len
    /\ fdifference_unrolled' s1 s2 == fdifference_tot s1 s2)
let lemma_fdifference_unrolled' s1 s2 =
  assert_norm(pow2 63 = 0x8000000000000000);
  lemma_add_zero_spec_ s2;
  let s' = add_zero_spec s2 in
  lemma_fdifference_unrolled s1 s'


val lemma_fdifference_unrolled'': s1:seqelem{red_513 s1} -> s2:seqelem{red_513 s2} -> Lemma
  (add_zero_pre s2 /\ gte_limbs s1 (add_zero_spec s2) len
    (* /\ fdifference_unrolled'' s1 s2 == fdifference_tot s1 s2 *)
    /\ red_55 (fdifference_tot s1 s2) )
let lemma_fdifference_unrolled'' s1 s2 =
  assert_norm(pow2 63 = 0x8000000000000000);
  lemma_add_zero_spec_ s2;
  let s' = add_zero_spec s2 in
  lemma_fdifference_unrolled s1 s'


val lemma_fdifference_unrolled''': s1:seqelem{red_513 s1} -> s2:seqelem{red_513 s2} -> Lemma
  (add_zero_pre s2 /\ gte_limbs s1 (add_zero_spec s2) len
    (* /\ fdifference_unrolled'' s1 s2 == fdifference_tot s1 s2 *)
    /\ red_5413 (fdifference_tot s1 s2) )
let lemma_fdifference_unrolled''' s1 s2 =
  assert_norm(pow2 63 = 0x8000000000000000);
  lemma_add_zero_spec_ s2;
  let s' = add_zero_spec s2 in
  lemma_fdifference_unrolled s1 s'


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
  (mul_shift_reduce_pre_ output input input2 len <==> (sum_scalar_multiplication_pre_ output input (Seq.index input2 0) len /\ shift_reduce_pre input /\ mul_shift_reduce_pre_ (sum_scalar_multiplication_spec output input (Seq.index input2 0)) (shift_reduce_spec input) input2 4)) = ()

#set-options "--z3rlimit 10 --initial_fuel 0 --max_fuel 0"

let lemma_mul_shift_reduce_pre (input:seqelem) (input2:seqelem) : Lemma
  (requires (mul_shift_reduce_pre' input input2))
  (ensures (mul_shift_reduce_pre_ (Seq.create len wide_zero) input input2 len))
  = lemma_mul_shift_reduce_pre_4 (Seq.create len wide_zero) input input2;
    let output1 = sum_scalar_multiplication_spec (Seq.create len wide_zero) input (Seq.index input2 0) in
    let input1 = shift_reduce_spec input in
    lemma_mul_shift_reduce_pre_3 output1 input1 input2;
    let output2 = sum_scalar_multiplication_spec output1 input1 (Seq.index input2 1) in
    let input2' = shift_reduce_spec input1 in
    lemma_mul_shift_reduce_pre_2 output2 input2' input2;
    let output3 = sum_scalar_multiplication_spec output2 input2' (Seq.index input2 2) in
    let input3 = shift_reduce_spec input2' in
    lemma_mul_shift_reduce_pre_1 output3 input3 input2;
    let output4 = sum_scalar_multiplication_spec output3 input3 (Seq.index input2 3) in
    let input4 = shift_reduce_spec input3 in
    lemma_mul_shift_reduce_pre_0 output4 input4 input2;
    let output5 = sum_scalar_multiplication_spec output4 input4 (Seq.index input2 4) in
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
  let input3    = shift_reduce_spec input2' in
  let output4   = sum_scalar_multiplication_spec output3 input3 (Seq.index input2 3) in
  let input4    = shift_reduce_spec input3 in
  sum_scalar_multiplication_spec output4 input4 (Seq.index input2 4)

inline_for_extraction let p108 : p:pos{p = 0x1000000000000000000000000000} =
  assert_norm(pow2 108 = 0x1000000000000000000000000000); pow2 108



#set-options "--z3rlimit 10 --initial_fuel 0 --max_fuel 0"

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

#set-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0"


val lemma_shift_reduce_spec_: s:seqelem{shift_reduce_pre s} -> Lemma
  (let s' = shift_reduce_spec s in
    v (Seq.index s' 0) = 19 * v (Seq.index s 4)
    /\ v (Seq.index s' 1) = v (Seq.index s 0)
    /\ v (Seq.index s' 2) = v (Seq.index s 1)
    /\ v (Seq.index s' 3) = v (Seq.index s 2)
    /\ v (Seq.index s' 4) = v (Seq.index s 3) )
let lemma_shift_reduce_spec_ s = ()


val lemma_sum_scalar_muitiplication_spec_: sw:seqelem_wide -> s:seqelem -> sc:limb ->
  Lemma (requires (sum_scalar_multiplication_pre_ sw s sc len))
        (ensures (sum_scalar_multiplication_pre_ sw s sc len
          /\ (let sw' = sum_scalar_multiplication_spec sw s sc in
             w (Seq.index sw' 0) = w (Seq.index sw 0) + (v (Seq.index s 0) * v sc)
             /\ w (Seq.index sw' 1) = w (Seq.index sw 1) + (v (Seq.index s 1) * v sc)
             /\ w (Seq.index sw' 2) = w (Seq.index sw 2) + (v (Seq.index s 2) * v sc)
             /\ w (Seq.index sw' 3) = w (Seq.index sw 3) + (v (Seq.index s 3) * v sc)
             /\ w (Seq.index sw' 4) = w (Seq.index sw 4) + (v (Seq.index s 4) * v sc))))
let lemma_sum_scalar_muitiplication_spec_ sw s sc = ()


val lemma_shift_reduce_then_carry_wide_0:
  s1:seqelem{red_53 s1} ->
  s2:seqelem{red_55 s2} ->
  Lemma (sum_scalar_multiplication_pre_ (Seq.create len wide_zero) s1 (Seq.index s2 0) len
    /\ shift_reduce_pre s1
    /\ bounds (shift_reduce_spec s1) (19 * p53) p53 p53 p53 p53
    /\ bounds' (sum_scalar_multiplication_spec (Seq.create len wide_zero) s1 (Seq.index s2 0))
              p108 p108 p108 p108 p108)
let lemma_shift_reduce_then_carry_wide_0 s1 s2 =
  assert_norm (pow2 53 = 0x20000000000000);
  assert_norm (pow2 55 = 0x80000000000000);
  assert_norm (pow2 64 = 0x10000000000000000);
  assert_norm (pow2 wide_n = 0x100000000000000000000000000000000);
  let bla = Seq.create len wide_zero in
  cut (w (Seq.index bla 0) = 0); cut (w (Seq.index bla 1) = 0); cut (w (Seq.index bla 2) = 0);
  cut (w (Seq.index bla 3) = 0); cut (w (Seq.index bla 4) = 0);
  cut (v (Seq.index s1 0) < 0x20000000000000); cut (v (Seq.index s1 1) < 0x20000000000000);
  cut (v (Seq.index s1 2) < 0x20000000000000); cut (v (Seq.index s1 3) < 0x20000000000000);
  cut (v (Seq.index s1 4) < 0x20000000000000);
  cut (v (Seq.index s2 0) < 0x80000000000000);
  lemma_mul_ineq (v (Seq.index s1 0)) (v (Seq.index s2 0)) 0x20000000000000 0x80000000000000;
  lemma_mul_ineq (v (Seq.index s1 1)) (v (Seq.index s2 0)) 0x20000000000000 0x80000000000000;
  lemma_mul_ineq (v (Seq.index s1 2)) (v (Seq.index s2 0)) 0x20000000000000 0x80000000000000;
  lemma_mul_ineq (v (Seq.index s1 3)) (v (Seq.index s2 0)) 0x20000000000000 0x80000000000000;
  lemma_mul_ineq (v (Seq.index s1 4)) (v (Seq.index s2 0)) 0x20000000000000 0x80000000000000;
  assert_norm(p108 = 0x20000000000000 * 0x80000000000000);
  cut (sum_scalar_multiplication_pre_' bla s1 (Seq.index s2 0));
  lemma_sum_scalar_muitiplication_pre_ bla s1 (Seq.index s2 0);
  lemma_shift_reduce_spec_ s1;
  let s1' = shift_reduce_spec s1 in
  Math.Lemmas.pow2_plus 53 55


val lemma_shift_reduce_then_carry_wide_1:
  o:seqelem_wide{bounds' o p108 p108 p108 p108 p108} ->
  s1:seqelem{bounds s1 (19*p53) p53 p53 p53 p53} ->
  s2:seqelem{red_55 s2} ->
  Lemma (sum_scalar_multiplication_pre_ o s1 (Seq.index s2 1) len
    /\ shift_reduce_pre s1
    /\ bounds (shift_reduce_spec s1) (19 * p53) (19*p53) p53 p53 p53
    /\ bounds' (sum_scalar_multiplication_spec o s1 (Seq.index s2 1))
              (20 * p108) (2*p108) (2*p108) (2*p108) (2*p108))
let lemma_shift_reduce_then_carry_wide_1 o s1 s2 =
  assert_norm (pow2 53 = 0x20000000000000);
  assert_norm (pow2 55 = 0x80000000000000);
  assert_norm (pow2 64 = 0x10000000000000000);
  assert_norm (pow2 wide_n = 0x100000000000000000000000000000000);
  lemma_mul_ineq (v (Seq.index s1 0)) (v (Seq.index s2 1)) (19 * p53) 0x80000000000000;
  lemma_mul_ineq (v (Seq.index s1 1)) (v (Seq.index s2 1)) 0x20000000000000 0x80000000000000;
  lemma_mul_ineq (v (Seq.index s1 2)) (v (Seq.index s2 1)) 0x20000000000000 0x80000000000000;
  lemma_mul_ineq (v (Seq.index s1 3)) (v (Seq.index s2 1)) 0x20000000000000 0x80000000000000;
  lemma_mul_ineq (v (Seq.index s1 4)) (v (Seq.index s2 1)) 0x20000000000000 0x80000000000000;
  assert_norm(p108 = 0x20000000000000 * 0x80000000000000);
  cut (sum_scalar_multiplication_pre_' o s1 (Seq.index s2 1));
  lemma_sum_scalar_muitiplication_pre_ o s1 (Seq.index s2 1);
  lemma_shift_reduce_spec_ s1;
  let s1' = shift_reduce_spec s1 in
  Math.Lemmas.pow2_plus 53 55


val lemma_shift_reduce_then_carry_wide_2:
  o:seqelem_wide{bounds' o (20 * p108) (2*p108) (2*p108) (2*p108) (2*p108)} ->
  s1:seqelem{bounds s1 (19*p53) (19*p53) p53 p53 p53} ->
  s2:seqelem{red_55 s2} ->
  Lemma (sum_scalar_multiplication_pre_ o s1 (Seq.index s2 2) len
    /\ shift_reduce_pre s1
    /\ bounds (shift_reduce_spec s1) (19 * p53) (19*p53) (19*p53) p53 p53
    /\ bounds' (sum_scalar_multiplication_spec o s1 (Seq.index s2 2))
              (39 * p108) (21*p108) (3*p108) (3*p108) (3*p108))
let lemma_shift_reduce_then_carry_wide_2 o s1 s2 =
  assert_norm (pow2 53 = 0x20000000000000);
  assert_norm (pow2 55 = 0x80000000000000);
  assert_norm (pow2 64 = 0x10000000000000000);
  assert_norm (pow2 wide_n = 0x100000000000000000000000000000000);
  lemma_mul_ineq (v (Seq.index s1 0)) (v (Seq.index s2 2)) (19 * p53) 0x80000000000000;
  lemma_mul_ineq (v (Seq.index s1 1)) (v (Seq.index s2 2)) (19 * p53) 0x80000000000000;
  lemma_mul_ineq (v (Seq.index s1 2)) (v (Seq.index s2 2)) 0x20000000000000 0x80000000000000;
  lemma_mul_ineq (v (Seq.index s1 3)) (v (Seq.index s2 2)) 0x20000000000000 0x80000000000000;
  lemma_mul_ineq (v (Seq.index s1 4)) (v (Seq.index s2 2)) 0x20000000000000 0x80000000000000;
  assert_norm(p108 = 0x20000000000000 * 0x80000000000000);
  cut (sum_scalar_multiplication_pre_' o s1 (Seq.index s2 2));
  lemma_sum_scalar_muitiplication_pre_ o s1 (Seq.index s2 2);
  lemma_shift_reduce_spec_ s1;
  let s1' = shift_reduce_spec s1 in
  Math.Lemmas.pow2_plus 53 55


val lemma_shift_reduce_then_carry_wide_3:
  o:seqelem_wide{bounds' o (39* p108) (21*p108) (3*p108) (3*p108) (3*p108)} ->
  s1:seqelem{bounds s1 (19*p53) (19*p53) (19*p53) p53 p53} ->
  s2:seqelem{red_55 s2} ->
  Lemma (sum_scalar_multiplication_pre_ o s1 (Seq.index s2 3) len
    /\ shift_reduce_pre s1
    /\ bounds (shift_reduce_spec s1) (19*p53) (19*p53) (19*p53) (19*p53) p53
    /\ bounds' (sum_scalar_multiplication_spec o s1 (Seq.index s2 3))
              (58 * p108) (40*p108) (22*p108) (4*p108) (4*p108))
let lemma_shift_reduce_then_carry_wide_3 o s1 s2 =
  assert_norm (pow2 53 = 0x20000000000000);
  assert_norm (pow2 55 = 0x80000000000000);
  assert_norm (pow2 64 = 0x10000000000000000);
  assert_norm (pow2 wide_n = 0x100000000000000000000000000000000);
  lemma_mul_ineq (v (Seq.index s1 0)) (v (Seq.index s2 3)) (19 * p53) 0x80000000000000;
  lemma_mul_ineq (v (Seq.index s1 1)) (v (Seq.index s2 3)) (19 * p53) 0x80000000000000;
  lemma_mul_ineq (v (Seq.index s1 2)) (v (Seq.index s2 3)) (19 * p53) 0x80000000000000;
  lemma_mul_ineq (v (Seq.index s1 3)) (v (Seq.index s2 3)) 0x20000000000000 0x80000000000000;
  lemma_mul_ineq (v (Seq.index s1 4)) (v (Seq.index s2 3)) 0x20000000000000 0x80000000000000;
  assert_norm(p108 = 0x20000000000000 * 0x80000000000000);
  cut (sum_scalar_multiplication_pre_' o s1 (Seq.index s2 3));
  lemma_sum_scalar_muitiplication_pre_ o s1 (Seq.index s2 3);
  lemma_shift_reduce_spec_ s1;
  let s1' = shift_reduce_spec s1 in
  Math.Lemmas.pow2_plus 53 55


val lemma_shift_reduce_then_carry_wide_4:
  o:seqelem_wide{bounds' o (58* p108) (40*p108) (22*p108) (4*p108) (4*p108)} ->
  s1:seqelem{bounds s1 (19*p53) (19*p53) (19*p53) (19*p53) p53} ->
  s2:seqelem{red_55 s2} ->
  Lemma (sum_scalar_multiplication_pre_ o s1 (Seq.index s2 4) len
    /\ shift_reduce_pre s1
    /\ bounds (shift_reduce_spec s1) (19*p53) (19*p53) (19*p53) (19*p53) (19*p53)
    /\ bounds' (sum_scalar_multiplication_spec o s1 (Seq.index s2 4))
              (77 * p108) (59*p108) (41*p108) (23*p108) (5*p108))
let lemma_shift_reduce_then_carry_wide_4 o s1 s2 =
  assert_norm (pow2 53 = 0x20000000000000);
  assert_norm (pow2 55 = 0x80000000000000);
  assert_norm (pow2 64 = 0x10000000000000000);
  assert_norm (pow2 wide_n = 0x100000000000000000000000000000000);
  lemma_mul_ineq (v (Seq.index s1 0)) (v (Seq.index s2 4)) (19 * p53) 0x80000000000000;
  lemma_mul_ineq (v (Seq.index s1 1)) (v (Seq.index s2 4)) (19 * p53) 0x80000000000000;
  lemma_mul_ineq (v (Seq.index s1 2)) (v (Seq.index s2 4)) (19 * p53) 0x80000000000000;
  lemma_mul_ineq (v (Seq.index s1 3)) (v (Seq.index s2 4)) (19 * p53) 0x80000000000000;
  lemma_mul_ineq (v (Seq.index s1 4)) (v (Seq.index s2 4)) 0x20000000000000 0x80000000000000;
  assert_norm(p108 = 0x20000000000000 * 0x80000000000000);
  cut (sum_scalar_multiplication_pre_' o s1 (Seq.index s2 4));
  lemma_sum_scalar_muitiplication_pre_ o s1 (Seq.index s2 4);
  lemma_shift_reduce_spec_ s1;
  let s1' = shift_reduce_spec s1 in
  Math.Lemmas.pow2_plus 53 55


#set-options "--z3rlimit 10 --initial_fuel 2 --max_fuel 2"

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
  let ctr = 4 in
  lemma_mul_shift_reduce_spec_def output input_init input input2 ctr;
  let i = ctr in
  let j = len - i - 1 in
  let input2j = Seq.index input2 j in
  let output' = sum_scalar_multiplication_spec output input input2j in
  lemma_sum_scalar_multiplication_ output input input2j len;
  let input'  = shift_reduce_spec input in
  output', input'


private 
val mul_shift_reduce_unrolled_1:
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


private 
val mul_shift_reduce_unrolled_2:
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


private 
val mul_shift_reduce_unrolled_3:
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
  Tot (t:seqelem_wide{let x, _ = mul_shift_reduce_spec_ output input_init input input2 0 in t == x})
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

#set-options "--z3rlimit 50 --initial_fuel 0 --max_fuel 0"

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
  s1:seqelem{red_53 s1} -> s2:seqelem{red_55 s2} ->
  Lemma (mul_shift_reduce_pre' s1 s2 /\
    bounds' (mul_shift_reduce_unrolled__ s1 s2) (77*p108) (59*p108) (41*p108) (23*p108) (5*p108))
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
  lemma_shift_reduce_then_carry_wide_4 o4 s14 s2; ()


#reset-options "--z3rlimit 50 --initial_fuel 0 --max_fuel 0"

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
  cut (w (Seq.index s4 4) < w (Seq.index s 4) + pow2 (2*word_size - limb_size));
  s4


#set-options "--z3rlimit 100 --initial_fuel 5 --max_fuel 5"

val lemma_carry_wide_spec_unrolled:
  s:seqelem_wide{carry_wide_pre s 0} -> Lemma (carry_wide_spec_unrolled s == carry_wide_spec s)
let lemma_carry_wide_spec_unrolled s = ()

#set-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

inline_for_extraction let p51 : p:pos{p = 0x8000000000000} = assert_norm (pow2 51 = 0x8000000000000); pow2 51
inline_for_extraction let p77 : p:pos{p = 0x20000000000000000000} = assert_norm (pow2 77 = 0x20000000000000000000); pow2 77

#set-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

val lemma_53_55_is_fine_to_carry:
  s:seqelem_wide{bounds' s (77*p108) (59*p108) (41*p108) (23*p108) (5*p108)} ->
  Lemma (carry_wide_pre s 0 /\ bounds' (carry_wide_spec s) p51 p51 p51 p51 (5*p108+p77))
let lemma_53_55_is_fine_to_carry s =
  assert_norm (pow2 53 = 0x20000000000000);
  assert_norm (pow2 55 = 0x80000000000000);
  assert_norm (pow2 64 = 0x10000000000000000);
  assert_norm (pow2 wide_n = 0x100000000000000000000000000000000);
  assert_norm (pow2 (wide_n-1) = 0x80000000000000000000000000000000);
  assert_norm(p108 = 0x20000000000000 * 0x80000000000000);
  lemma_carry_wide_spec_unrolled s


#set-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

val lemma_copy_then_carry: s:seqelem_wide -> Lemma
  ((copy_from_wide_pre s /\ (w (Seq.index s 0) < pow2 word_size /\ w (Seq.index s 1) < pow2 limb_size
    /\ w (Seq.index s 2) < pow2 limb_size /\ w (Seq.index s 3) < pow2 limb_size
    /\ w (Seq.index s 4) < pow2 limb_size)) ==>
     (carry_0_to_1_pre (copy_from_wide_spec s) ))
let lemma_copy_then_carry s = ()



val lemma_carry_top_wide_then_copy: s:seqelem_wide{carry_top_wide_pre s} -> Lemma
  ((w (Seq.index s 0) + 19 * w (Seq.index s 4) / pow2 limb_size < pow2 word_size /\ w (Seq.index s 1) < pow2 word_size /\ w (Seq.index s 2) < pow2 word_size /\ w (Seq.index s 3) < pow2 word_size) ==> copy_from_wide_pre (carry_top_wide_spec s))
let lemma_carry_top_wide_then_copy s =
  lemma_carry_top_wide_spec_ s;
  assert_norm(pow2 64 > pow2 51)

#set-options "--z3rlimit 50 --initial_fuel 0 --max_fuel 0"

val lemma_carry_wide_then_carry_top: s:seqelem_wide{carry_wide_pre s 0} -> Lemma
  (((w (Seq.index s 4) + pow2 (2*word_size - limb_size))/ pow2 limb_size < pow2 word_size
    /\ 19 * (w (Seq.index s 4) + pow2 (2*word_size - limb_size) / pow2 limb_size) + pow2 limb_size < pow2 word_size)
    ==> carry_top_wide_pre (carry_wide_spec s) )
let lemma_carry_wide_then_carry_top s =
  let s' = carry_wide_spec_unrolled s in
  lemma_carry_wide_spec_unrolled s;
  cut (w (Seq.index s' 4) < w (Seq.index s 4) + pow2 (2*word_size-limb_size));
  Math.Lemmas.nat_times_nat_is_nat 19 (w (Seq.index s 4) + pow2 (2*word_size-limb_size));
  if ((w (Seq.index s 4) + pow2 (2*word_size - limb_size))/ pow2 limb_size < pow2 word_size
    && 19 * (w (Seq.index s 4) + pow2 (2*word_size - limb_size) / pow2 limb_size) + pow2 limb_size < pow2 word_size) then (
    Math.Lemmas.lemma_div_le (w (Seq.index s' 4)) (w (Seq.index s 4) + pow2 (2*word_size-limb_size)) (pow2 limb_size);
    cut (w (Seq.index s' 4) / pow2 limb_size <= (w (Seq.index s 4) + pow2 (2*word_size-limb_size)) / pow2 limb_size);
    Math.Lemmas.nat_over_pos_is_nat (w (Seq.index s' 4)) (pow2 limb_size);
    Math.Lemmas.nat_over_pos_is_nat (((w (Seq.index s 4)+(pow2 (2*word_size-limb_size)))/pow2 limb_size)) (pow2 limb_size);
    Math.Lemmas.multiplication_order_lemma (w (Seq.index s' 4) / pow2 limb_size)
                                           ((w (Seq.index s 4)+(pow2 (2*word_size-limb_size)))/pow2 limb_size) 19;
    cut (19 * (w (Seq.index s' 4) / pow2 limb_size) <= 19 * ((w (Seq.index s 4) + pow2 (2*word_size-limb_size)) / pow2 limb_size));
    cut (w (Seq.index s' 0) < pow2 limb_size);
    cut (19 * (w (Seq.index s' 4) / pow2 limb_size) + w (Seq.index s' 0) < pow2 word_size);
    Math.Lemmas.pow2_lt_compat (2*word_size) word_size
  )
  else ()



val lemma_53_55_is_fine_to_carry_top:
  s:seqelem_wide{bounds' s p51 p51 p51 p51 (5*p108+p77)} ->
  Lemma (carry_top_wide_pre s /\ bounds' (carry_top_wide_spec s) (p51+19*((5*p108+p77)/p51)) p51 p51 p51 p51)
let lemma_53_55_is_fine_to_carry_top s =
  assert_norm (pow2 53 = 0x20000000000000);
  assert_norm (pow2 55 = 0x80000000000000);
  assert_norm (pow2 64 = 0x10000000000000000);
  assert_norm (pow2 wide_n = 0x100000000000000000000000000000000);
  assert_norm (pow2 (wide_n-1) = 0x80000000000000000000000000000000);
  assert_norm(p108 = 0x20000000000000 * 0x80000000000000);
  lemma_carry_wide_then_carry_top s;
  lemma_carry_top_wide_spec_ s


val lemma_53_55_is_fine_to_copy:
  s:seqelem_wide{bounds' (s) (p51+19*((5*p108+p77)/p51)) p51 p51 p51 p51} ->
  Lemma (copy_from_wide_pre s /\ bounds (copy_from_wide_spec s) (p51+19*((5*p108+p77)/p51)) p51 p51 p51 p51)
let lemma_53_55_is_fine_to_copy s =
  assert_norm (pow2 53 = 0x20000000000000);
  assert_norm (pow2 55 = 0x80000000000000);
  assert_norm (pow2 64 = 0x10000000000000000);
  assert_norm (pow2 wide_n = 0x100000000000000000000000000000000);
  assert_norm (pow2 (wide_n-1) = 0x80000000000000000000000000000000);
  assert_norm(p108 = 0x20000000000000 * 0x80000000000000)

inline_for_extraction let p13 : p:pos{p = 0x2000} = assert_norm(pow2 13 = 0x2000); pow2 13

val lemma_53_55_is_fine_to_carry_last:
  s:seqelem{bounds (s) (p51+19*((5*p108+p77)/p51)) p51 p51 p51 p51} ->
  Lemma (carry_0_to_1_pre s /\ bounds (carry_0_to_1_spec s) (p51) (p51+p13) p51 p51 p51)
let lemma_53_55_is_fine_to_carry_last s =
  assert_norm (pow2 53 = 0x20000000000000);
  assert_norm (pow2 55 = 0x80000000000000);
  assert_norm (pow2 64 = 0x10000000000000000);
  assert_norm (pow2 wide_n = 0x100000000000000000000000000000000);
  assert_norm (pow2 (wide_n-1) = 0x80000000000000000000000000000000);
  assert_norm(p108 = 0x20000000000000 * 0x80000000000000)


#set-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

val fmul_53_55_is_fine:
  s1:seqelem{red_53 s1} -> s2:seqelem{red_55 s2} ->
  Lemma (fmul_pre s1 s2 /\ red_513 (fmul_spec s1 s2))
let fmul_53_55_is_fine s1 s2 =
  lemma_shift_reduce_then_carry_wide s1 s2;
  lemma_mul_shift_reduce_unrolled s1 s2;
  let o = mul_shift_reduce_spec s1 s2 in
  lemma_53_55_is_fine_to_carry o;
  let o' = carry_wide_spec o in
  lemma_53_55_is_fine_to_carry_top o';
  let o'' = carry_top_wide_spec o' in
  lemma_53_55_is_fine_to_copy o'';
  let o''' = copy_from_wide_spec o'' in
  lemma_53_55_is_fine_to_carry_last o''';
  let o'''' = carry_0_to_1_spec o''' in
  assert_norm(pow2 52 = 0x10000000000000);
  cut (bounds o'''' (p51) (p51+p13) p51 p51 p51);
  cut (o'''' == fmul_spec s1 s2);
  assert_norm(p51 < pow2 52);
  assert_norm(p51+p13 < pow2 52)


val fsum_52_is_53:
  s1:seqelem{red_52 s1} -> s2:seqelem{red_52 s2} ->
  Lemma (red s1 len /\ red s2 len /\ red_53 (fsum_spec s1 s2))
let fsum_52_is_53 s1 s2 =
  assert_norm (pow2 53 = 0x20000000000000);
  assert_norm (pow2 52 = 0x10000000000000);
  assert_norm (pow2 63 = 0x8000000000000000);
  assert_norm (pow2 64 = 0x10000000000000000);
  let s' = fsum_spec s1 s2 in
  lemma_fsum_def s1 s2


val fsum_513_is_53:
  s1:seqelem{red_513 s1} -> s2:seqelem{red_513 s2} ->
  Lemma (red s1 len /\ red s2 len /\ red_53 (fsum_spec s1 s2))
let fsum_513_is_53 s1 s2 =
  assert_norm (pow2 63 = 0x8000000000000000);
  assert_norm (pow2 64 = 0x10000000000000000);
  let s' = fsum_spec s1 s2 in
  lemma_fsum_def s1 s2


#set-options "--z3rlimit 10 --initial_fuel 0 --max_fuel 0"

val fscalar_unrolled: s1:seqelem -> sc:limb -> Tot (s:seqelem_wide{
  w (Seq.index s 0) = v (Seq.index s1 0) * v (sc)
  /\ w (Seq.index s 1) = v (Seq.index s1 1) * v (sc)
  /\ w (Seq.index s 2) = v (Seq.index s1 2) * v (sc)
  /\ w (Seq.index s 3) = v (Seq.index s1 3) * v (sc)
  /\ w (Seq.index s 4) = v (Seq.index s1 4) * v (sc)})
let fscalar_unrolled a sc =
    Math.Lemmas.pow2_double_sum (limb_n-1);
    let open Hacl.Bignum.Wide in
    let c = Seq.create len wide_zero in
    let c = Seq.upd c 4 ((Seq.index a 4) *^ (sc)) in
    let c = Seq.upd c 3 ((Seq.index a 3) *^ (sc)) in
    let c = Seq.upd c 2 ((Seq.index a 2) *^ (sc)) in
    let c = Seq.upd c 1 ((Seq.index a 1) *^ (sc)) in
    let c = Seq.upd c 0 ((Seq.index a 0) *^ (sc)) in
    c


#set-options "--z3rlimit 40 --initial_fuel 0 --max_fuel 0"

val lemma_fscalar_unrolled: s1:seqelem -> sc:limb -> Lemma
  (fscalar_unrolled s1 sc == Hacl.Spec.Bignum.Fscalar.fscalar_spec s1 sc)
let lemma_fscalar_unrolled s1 sc =
  Seq.lemma_eq_intro (fscalar_unrolled s1 sc) (Hacl.Spec.Bignum.Fscalar.fscalar_spec s1 sc)


#set-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

private let lemma_mul_le (a:nat) (b:nat) (c:nat) (d:nat) :
  Lemma (requires (a < c /\ b < d))
        (ensures ( a * b < c * d )) = ()


#set-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

inline_for_extraction let p74 : p:pos{p = 0x4000000000000000000} = assert_norm(pow2 74 = 0x4000000000000000000); pow2 74


val lemma_74_is_fine_to_carry:
  s:seqelem_wide{bounds' s p74 p74 p74 p74 p74} ->
  Lemma (carry_wide_pre s 0 /\ bounds' (carry_wide_spec s) p51 p51 p51 p51 (p74+p77))
let lemma_74_is_fine_to_carry s =
  assert_norm (pow2 64 = 0x10000000000000000);
  assert_norm (pow2 wide_n = 0x100000000000000000000000000000000);
  assert_norm (pow2 (wide_n-1) = 0x80000000000000000000000000000000);
  lemma_carry_wide_spec_unrolled s


val lemma_74_is_fine_to_carry_top:
  s:seqelem_wide{bounds' s p51 p51 p51 p51 (p74+p77)} ->
  Lemma (carry_top_wide_pre s /\ bounds' (carry_top_wide_spec s) (p51+19*((p74+p77)/p51)) p51 p51 p51 p51)
let lemma_74_is_fine_to_carry_top s =
  assert_norm (pow2 64 = 0x10000000000000000);
  assert_norm (pow2 wide_n = 0x100000000000000000000000000000000);
  assert_norm (pow2 (wide_n-1) = 0x80000000000000000000000000000000);
  lemma_carry_wide_then_carry_top s;
  lemma_carry_top_wide_spec_ s


val lemma_74_is_fine_to_copy:
  s:seqelem_wide{bounds' (s) (p51+19*((p74+p77)/p51)) p51 p51 p51 p51} ->
  Lemma (copy_from_wide_pre s /\ bounds (copy_from_wide_spec s) (p51+19*((p74+p77)/p51)) p51 p51 p51 p51)
let lemma_74_is_fine_to_copy s =
  assert_norm (pow2 64 = 0x10000000000000000);
  assert_norm (pow2 wide_n = 0x100000000000000000000000000000000);
  assert_norm (pow2 (wide_n-1) = 0x80000000000000000000000000000000)


val fscalar_is_fine: a:seqelem{red_5413 a} -> s:limb{v s  = 121665} ->
  Lemma (carry_wide_pre (Hacl.Spec.Bignum.Fscalar.fscalar_spec a s) 0
    /\ carry_top_wide_pre (carry_wide_spec (Hacl.Spec.Bignum.Fscalar.fscalar_spec a s))
    /\ copy_from_wide_pre (carry_top_wide_spec (carry_wide_spec (Hacl.Spec.Bignum.Fscalar.fscalar_spec a s)))
    /\ red_52 (fscalar_tot a s))
let fscalar_is_fine a sc =
  let o = fscalar_unrolled a sc in
  lemma_fscalar_unrolled a sc;
  assert_norm(pow2 64 = 0x10000000000000000);
  cut (bounds' o p74 p74 p74 p74 p74);
  lemma_74_is_fine_to_carry o;
  let o' = carry_wide_spec o in
  lemma_74_is_fine_to_carry_top o';
  let o'' = carry_top_wide_spec o' in
  lemma_74_is_fine_to_copy o'';
  let o''' = copy_from_wide_spec o'' in
  assert(o''' == fscalar_tot a sc);
  assert_norm(p51+19*((p74+p77)/p51) < p52);
  assert_norm(p51 < p52);
  ()
