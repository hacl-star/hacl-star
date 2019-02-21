module Hacl.Bignum.Fmul

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All


open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Bignum.Limb
open Hacl.Bignum.Modulo
open Hacl.Bignum.Fproduct
(* open Hacl.Spec.Bignum.Fmul.Lemmas *)
open Hacl.Spec.Bignum.Fmul
(* open Hacl.Spec.Bignum.Fmul2 *)

module U32 = FStar.UInt32


#set-options "--z3rlimit 40"

[@"c_inline"]
val shift_reduce: output:felem -> Stack unit
  (requires (fun h -> live h output /\ shift_reduce_pre (as_seq h output)))
  (ensures (fun h0 _ h1 -> live h0 output /\ live h1 output /\ modifies_1 output h0 h1
    /\ shift_reduce_pre (as_seq h0 output)
    /\ as_seq h1 output == shift_reduce_spec (as_seq h0 output)))
[@"c_inline"]
let shift_reduce output =
  shift output;
  reduce output


#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

[@"substitute"]
val mul_shift_reduce_:
  output:felem_wide ->
  input:felem{disjoint output input} ->
  input2:felem{disjoint output input2 /\ disjoint input input2}  ->
  Stack unit
    (requires (fun h -> live h output /\ live h input /\ live h input2
      /\ mul_shift_reduce_pre (as_seq h output) (as_seq h input) (as_seq h input) (as_seq h input2) (len) ))
    (ensures (fun h0 _ h1 -> live h0 output /\ live h0 input /\ live h0 input2 /\ modifies_2 output input h0 h1
      /\ live h1 output /\ live h1 input
      /\ mul_shift_reduce_pre (as_seq h0 output) (as_seq h0 input) (as_seq h0 input) (as_seq h0 input2) (len)
      /\ (let output', input' = mul_shift_reduce_spec_ (as_seq h0 output) (as_seq h0 input) (as_seq h0 input) (as_seq h0 input2) (0) in
         as_seq h1 output == output')
      ))
#reset-options "--z3rlimit 200 --initial_fuel 1 --max_fuel 1"

let mul_shift_reduce_ output input input2 =
  let h0 = ST.get() in
  let inv h i =
    live h output /\ live h input /\ modifies_2 output input h0 h /\ 0 <= i /\ i < len /\
    (let output', input' =
      mul_shift_reduce_spec_
        (as_seq h0 output) (as_seq h0 input)
        (as_seq h0 input) (as_seq h0 input2)
        (len - i) in
     as_seq h output == output' /\ as_seq h input == input')
  in
  let f' (i:U32.t{0 <= U32.v i /\ U32.v i < len - 1}) : Stack unit
    (requires (fun h -> inv h (U32.v i)))
    (ensures  (fun _ _ h1 -> inv h1 (U32.v i + 1)))
  = let h0' = ST.get() in
    lemma_mul_shift_reduce_spec_def
      (as_seq h0 output) (as_seq h0 input)
      (as_seq h0 input) (as_seq h0 input2)
      (len - U32.v i - 1);
    let input2i = input2.(i) in
    Hacl.Spec.Bignum.Fproduct.lemma_sum_scalar_multiplication_
      (as_seq h0' output) (as_seq h0' input) (input2i) len;
    sum_scalar_multiplication_ output input input2i;
    let h1 = ST.get() in
    shift_reduce input;
    let h' = ST.get() in
    lemma_modifies_1_1 output input h0' h1 h';
    lemma_modifies_2_trans output input h0 h0' h';
    lemma_shift_reduce_spec (as_seq h0' input);
    lemma_mul_shift_reduce_spec_1 (as_seq h' output) (as_seq h0' output) (as_seq h0 input)
                                  (as_seq h0' input) (as_seq h' input) (as_seq h0' input2)
                                  (v input2i) (len - U32.v i)
    in
  lemma_mul_shift_reduce_spec_def_0
    (as_seq h0 output) (as_seq h0 input) (as_seq h0 input) (as_seq h0 input2);
  C.Compat.Loops.for 0ul U32.(clen -^ 1ul) inv f';
  let i = U32.(clen -^ 1ul) in
  let h0' = ST.get() in
  lemma_mul_shift_reduce_spec_def
    (as_seq h0 output) (as_seq h0 input)
    (as_seq h0 input) (as_seq h0 input2)
    0;
  let input2i = input2.(i) in
  Hacl.Spec.Bignum.Fproduct.lemma_sum_scalar_multiplication_
    (as_seq h0' output) (as_seq h0' input) (input2i) len;
  sum_scalar_multiplication_ output input input2i;
  let h' = ST.get() in
  lemma_mul_shift_reduce_spec_2 (as_seq h' output) (as_seq h0' output) (as_seq h0 input)
                                (as_seq h0' input) (as_seq h' input) (as_seq h0' input2)
                                (v input2i)


#reset-options "--z3rlimit 10 --initial_fuel 0 --max_fuel 0"

let as_seq' (h:mem) (b:felem{live h b}) : GTot seqelem = as_seq h b
  

[@"substitute"]
private val fmul_:
  output:felem ->
  input:felem{disjoint output input} ->
  input2:felem{(* disjoint output input2 /\  *)disjoint input input2} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input /\ live h input2
      /\ fmul_pre (as_seq h input) (as_seq h input2)))
    (ensures (fun h0 _ h1 -> live h0 output /\ live h0 output /\ live h0 input /\ live h0 input2 
      /\ modifies_2 output input h0 h1 /\ live h1 output /\ live h1 input
      /\ fmul_pre (as_seq h0 input) (as_seq h0 input2)
      /\ as_seq h1 output == fmul_spec (as_seq h0 input) (as_seq h0 input2)
      ))
#reset-options "--z3rlimit 100 --max_fuel 0"
[@"substitute"]
private let fmul_ output input input2 =
  let h0 = ST.get() in
  push_frame();
  let h1 = ST.get() in
  let t   = create wide_zero clen in
  let h2 = ST.get() in
  mul_shift_reduce_ t input input2;
  let h2' = ST.get() in
  assert(as_seq h2' t == (let input = as_seq h0 input in
                          let input2 = as_seq h0 input2 in
                          Hacl.Spec.Bignum.Fmul.mul_shift_reduce_spec input input2));
  carry_wide_ t;
  let h3 = ST.get() in
  Hacl.Spec.Bignum.Modulo.lemma_carry_top_wide_spec (as_seq h3 t);
  carry_top_wide t;
  let h4 = ST.get() in
  Hacl.Spec.Bignum.Fproduct.lemma_copy_from_wide (as_seq h4 t);
  copy_from_wide_ output t;
  carry_0_to_1 output;
  let h5 = ST.get() in
  pop_frame();
  let h6 = ST.get() in
  lemma_modifies_1_trans t h2' h3 h4;
  lemma_modifies_0_2 input t h1 h2 h2';
  lemma_modifies_1_1 t output h2' h4 h5;
  lemma_modifies_2_1'  t input h2 h2' h4;
  lemma_modifies_2_1'' input output h1 h4 h5;
  modifies_popped_3_2 input output h0 h1 h5 h6


#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0"

[@"c_inline"]
val fmul:
  output:felem ->
  input:felem ->
  input2:felem ->
  Stack unit
    (requires (fun h -> live h output /\ live h input /\ live h input2
      /\ fmul_pre (as_seq h input) (as_seq h input2)))
    (ensures (fun h0 _ h1 -> live h0 output /\ live h0 output /\ live h0 input /\ live h0 input2
      /\ modifies_1 output h0 h1 /\ live h1 output
      /\ fmul_pre (as_seq h0 input) (as_seq h0 input2)
      /\ as_seq h1 output == fmul_spec (as_seq h0 input) (as_seq h0 input2)
      ))
[@"c_inline"]
let fmul output input input2 =
  let h0 = ST.get() in
  push_frame();
  let h1 = ST.get() in
  let tmp = create limb_zero clen in
  let h1' = ST.get() in
  blit input 0ul tmp 0ul clen;
  let h2 = ST.get() in
  lemma_whole_slice (as_seq h2 input);
  lemma_whole_slice (as_seq h2 tmp);
  no_upd_lemma_1 h1' h2 tmp output;
  no_upd_lemma_1 h1' h2 tmp input2;
  fmul_ output tmp input2;
  let h3 = ST.get() in
  pop_frame();
  let h4 = ST.get() in
  lemma_modifies_0_1' tmp h1 h1' h2;
  lemma_modifies_2_comm tmp output h2 h3;
  lemma_modifies_1_2'' tmp output h1' h2 h3;
  lemma_modifies_0_2' output tmp h1 h1' h3;
  modifies_popped_1 output h0 h1 h3 h4
