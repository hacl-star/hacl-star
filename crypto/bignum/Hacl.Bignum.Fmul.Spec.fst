module Hacl.Bignum.Fmul.Spec

open FStar.Mul

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Bignum.Bigint
open Hacl.Bignum.Limb
open Hacl.Bignum.Modulo.Spec
open Hacl.Bignum.Fproduct.Spec

module U32 = FStar.UInt32


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 5"

let shift_reduce_pre (s:seqelem) : GTot Type0 = reduce_pre (shift_spec s)


val shift_reduce_spec: s:seqelem{shift_reduce_pre s} -> Tot (s':seqelem)
let shift_reduce_spec s =
  reduce_spec (shift_spec s)

#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val lemma_shift_spec_eq: s:seqelem -> Lemma
  (Seq.append (Seq.slice (shift_spec s) 1 (len)) (Seq.slice (shift_spec s) 0 1) == s)
let lemma_shift_spec_eq s =
  Seq.lemma_eq_intro (Seq.append (Seq.slice (shift_spec s) 1 (len)) (Seq.slice (shift_spec s) 0 1)) (s)


val lemma_shift_reduce_spec: s:seqelem{shift_reduce_pre s} -> Lemma
  (seval (shift_reduce_spec s) % prime = (pow2 limb_size * seval s) % prime)
let lemma_shift_reduce_spec s =
  lemma_shift_spec_eq s;
  lemma_reduce_spec (shift_spec s)


#set-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 50"

let rec mul_shift_reduce_pre (output:seqelem_wide) (input:seqelem) (input2:seqelem) (ctr:nat{ctr <= len}) : GTot Type0 (decreases ctr) =
  if ctr > 0 then (
    sum_scalar_multiplication_pre_ output input (Seq.index input2 (len-ctr)) len
    /\ (let output' = sum_scalar_multiplication_spec output input (Seq.index input2 (len-ctr)) len in
       (ctr > 1 ==> shift_reduce_pre input) /\
         (let input'  = if ctr > 1 then shift_reduce_spec input else input in
          mul_shift_reduce_pre output' input' input2 (ctr-1))))
          else true


#set-options "--z3rlimit 10 --initial_fuel 1 --max_fuel 1"

assume val lemma_mod_mul_distr: a:nat -> b:nat -> p:pos -> Lemma ((a+b)%p = ((a%p) + b) % p)
assume val lemma_mod_mul_comm: a:nat -> b:nat -> p:pos -> Lemma ((a*b)%p = ((a%p)*b)%p)


(* val mul_shift_reduce_spec_step_1: o1:nat -> o2:nat -> i0:nat -> i1:nat -> i2:nat -> x:nat -> ctr:nat -> Lemma *)
(*   (requires (o2 = o1 + i1 * x /\ i1 % p = pow2 ((len - ctr) * limb_size) * i0 % p)) *)
(*   (ensures (o2 % p = (pow2 ((len-ctr)*limb_size) * i0 * x))) *)


(* val mul_shift_reduce_spec_step: *)
(*   output:seqelem_wide -> *)
(*   input_init:seqelem -> *)
(*   input:seqelem -> *)
(*   input2:seqelem -> *)
(*   ctr:pos{ctr <= len /\ mul_shift_reduce_pre output input input2 ctr *)
(*     /\ (ctr > 0 ==> seval input % prime = pow2 ((len - ctr) * limb_size) * seval input_init % prime) *)
(*     /\ seval_wide output % prime = (seval input_init * seval_ input2 (len - ctr)) % prime} -> *)
(*   Tot (s:seqelem_wide{((ctr = 1) ==> seval_wide s % prime = (seval input * seval input2) % prime) *)
(*     /\ (ctr <> 1 ==> seval_wide s % prime = (seval input_init * seval_ input2 (len-ctr+1)) % prime)}) *)
(* let mul_shift_reduce_spec_step output input_init input input2 ctr = *)
(*   let i = ctr - 1 in *)
(*   let j = len - i - 1 in *)
(*   let input2j = Seq.index input2 j in *)
(*   let output' = sum_scalar_multiplication_spec output input input2j len in *)
(*   lemma_sum_scalar_multiplication_ output input input2j len; *)
(*   cut (seval_wide output' = seval_wide output + (seval input * v input2j)); *)
(*   Math.Lemmas.nat_times_nat_is_nat (seval input) (v input2j); *)
(*   let input'  = if ctr > 1 then shift_reduce_spec input else input in *)
(*   if ctr = 1 then ( *)
(*     (\* admit(); *\) *)
(*     (\* let o1 = seval_wide output in *\) *)
(*     (\* let o2 = seval_wide output' in *\) *)
(*     (\* let p = prime in *\) *)
(*     (\* let i0 = seval input_init in *\) *)
(*     (\* let i1 = seval input in *\) *)
(*     (\* lemma_mod_mul_distr (seval_wide output) (seval input * v input2j) prime; *\) *)
(*     (\* cut (seval_wide output' % prime = ((seval input_init * seval_ input2 (len-1)) % prime *\) *)
(*     (\*                                   + seval input * v input2j) % prime); *\) *)
(*     (\* lemma_mod_mul_distr (seval input_init * seval_ input2 (len-1)) (seval input * v input2j) prime; *\) *)
(*     (\* cut (seval_wide output' % prime = (seval input_init * seval_ input2 (len-1) *\) *)
(*     (\*                                   + seval input * v input2j) % prime); *\) *)
(*     (\* lemma_mod_mul_distr (seval input * v input2j) (seval input_init * seval_ input2 (len-1)) prime; *\) *)
(*     (\* lemma_mod_mul_distr (seval input_init * v input2j) (seval input_init * seval_ input2 (len-1)) prime; *\) *)
(*     (\* cut (seval_wide output' % prime = *\) *)
(*     (\*   (seval input_init * seval_ input2 (len-1) + seval input_init * pow2 (limb_size * (len-1)) * v input2j) % prime); *\) *)
(*     (\* () *\) *)
(*     assume (seval_wide output' % prime = (seval input_init * seval input2) % prime); *)
(*   ) else ( *)
(*     (\* cut (seval_wide output' = seval_wide output + (seval input * v input2j)); *\) *)
(*     (\* cut (seval input' % prime = seval input + (pow2 limb_size * seval input) % prime); *\) *)
(*     admit() *)
(*   ); *)

#set-options "--z3rlimit 10 --initial_fuel 0 --max_fuel 0"

val mul_shift_reduce_spec_:
  output:seqelem_wide ->
  input_init:seqelem ->
  input:seqelem ->
  input2:seqelem ->
  ctr:nat{ctr <= len /\ mul_shift_reduce_pre output input input2 ctr
    /\ seval_wide output % prime = (seval input * seval_ input2 (len - ctr)) % prime
    /\ (ctr > 0 ==> seval input % prime = (pow2 ((len - ctr) * limb_size) * seval input_init) % prime)
    } ->
  Tot (s:seqelem_wide{seval_wide s % prime = (seval input * seval input2) % prime})
  (decreases ctr)

#set-options "--z3rlimit 50 --initial_fuel 1 --max_fuel 1"

let rec mul_shift_reduce_spec_ output input_init input input2 ctr =
  if ctr = 0 then output
  else (
    let i = ctr - 1 in
    let j = len - i - 1 in
    let input2j = Seq.index input2 j in
    let output' = sum_scalar_multiplication_spec output input input2j len in
    lemma_sum_scalar_multiplication_ output input input2j len;
    cut (seval_wide output' = seval_wide output + (seval input * v input2j));
    let input'  = if ctr > 1 then shift_reduce_spec input else input in
    if ctr = 1 then (
      lemma_mod_mul_distr (seval_wide output) (seval input * v input2j) prime;
      cut (seval_wide output' % prime = ((seval input * seval_ input2 (len-1)) % prime + seval input * v input2j) % prime);
      admit() (* TODO *)
    );
    admit();  (* TODO *)
    mul_shift_reduce_spec_ output' input_init input' input2 i
  )


val lemma_seval_wide_null: a:seqelem_wide -> ctr:nat{ctr <= len} -> Lemma
  (requires (a == Seq.create len wide_zero))
  (ensures (seval_wide_ a ctr = 0))
let rec lemma_seval_wide_null a ctr =
  if ctr = 0 then () else lemma_seval_wide_null a (ctr-1)


val mul_shift_reduce_spec:
  input:seqelem -> input2:seqelem{mul_shift_reduce_pre (Seq.create len wide_zero) input input2 len} ->
  Tot (s:seqelem_wide{seval_wide s % prime = (seval input * seval input2) % prime})
let rec mul_shift_reduce_spec input input2 =
  lemma_seval_wide_null (Seq.create len wide_zero) len;
  assert_norm (pow2 0 = 1);
  mul_shift_reduce_spec_ (Seq.create len wide_zero) input input input2 len


#set-options "--z3rlimit 5 --initial_fuel 2 --max_fuel 2"

(* val lemma_mul_shift_reduce_spec_: *)
(*   output:seqelem_wide -> *)
(*   input:seqelem -> input2:seqelem -> *)
(*   ctr:nat{ctr <= len /\ mul_shift_reduce_pre output input input2 ctr} -> *)
(*   Lemma *)
(*     ((seval_wide (mul_shift_reduce_spec_ output input input2 ctr)) % prime *)
(*     = (seval input * seval_ input2 (len - ctr)) % prime) *)
(* let rec lemma_mul_shift_reduce_spec_ input input2 ctr = *)
(*   if ctr = 0 then ( *)
(*     lemma_seval_wide_null (mul_shift_reduce_spec input input2 ctr) len *)
(*   ) else ( *)
(*     let zeros = Seq.create len wide_zero in *)
(*     let s = sum_scalar_multiplication_spec zeros input (Seq.index input2 (len-ctr-1)) in *)
(*     let input' = if ctr = 1 then input else shift_reduce_spec input in *)
(*     lemma_mul_shift_reduce_spec_ input' input2 (ctr-1); *)
(*     admit(); *)
(*     if ctr = 1 then ( *)
(*       (\* lemma_seval_wide_null (mul_shift_reduce_spec input input2 0) len; *\) *)
(*       (\* assert(seval_wide (mul_shift_reduce_spec input input2 (ctr-1)) % prime = 0); *\) *)
(*       admit() *)
(*     ) *)
(*     else admit() *)
(*   ) *)


let fmul_pre (input:seqelem) (input2:seqelem) : GTot Type0 =
  mul_shift_reduce_pre (Seq.create len wide_zero) input input2 len
