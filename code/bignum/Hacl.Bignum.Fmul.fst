module Hacl.Bignum.Fmul


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

[@"c_inline"]
val mul_shift_reduce_:
  output:felem_wide ->
  (* init_input:Ghost.erased seqelem -> *)
  input:felem{disjoint output input} ->
  input2:felem{disjoint output input2 /\ disjoint input input2}  ->
  (* ctr:U32.t{U32.v ctr <= len} -> *)
  Stack unit
    (requires (fun h -> live h output /\ live h input /\ live h input2
      (* /\ mul_shift_reduce_pre (as_seq h output) (Ghost.reveal init_input) (as_seq h input) (as_seq h input2) (U32.v ctr) *)
      /\ mul_shift_reduce_pre (as_seq h output) (as_seq h input) (as_seq h input) (as_seq h input2) (len)
      ))
    (ensures (fun h0 _ h1 -> live h0 output /\ live h0 input /\ live h0 input2 /\ modifies_2 output input h0 h1
      /\ live h1 output /\ live h1 input
      /\ mul_shift_reduce_pre (as_seq h0 output) (as_seq h0 input) (as_seq h0 input) (as_seq h0 input2) (len)
      (* /\ mul_shift_reduce_pre (as_seq h0 output) (Ghost.reveal init_input) (as_seq h0 input) (as_seq h0 input2) (U32.v ctr) *)
      /\ (let output', input' = mul_shift_reduce_spec_ (as_seq h0 output) (as_seq h0 input) (as_seq h0 input) (as_seq h0 input2) (0) in
         as_seq h1 output == output')
      ))
#reset-options "--z3rlimit 1000 --initial_fuel 1 --max_fuel 1"
let mul_shift_reduce_ output (* init_input  *)input input2 =
  let h0 = ST.get() in
  let inv (h1: HyperStack.mem) (i: nat): Type0 =
    live h1 output /\ live h1 input /\ modifies_2 output input h0 h1 /\ 0 <= i /\ i <= len /\
    (let output', input' = mul_shift_reduce_spec_ (as_seq h0 output) (as_seq h0 input) (as_seq h0 input) (as_seq h0 input2) (len - i) in
     as_seq h1 output == output' /\ as_seq h1 input == input')
  in
  let f' (i:UInt32.t{FStar.UInt32.( 0 <= v i /\ v i < len) }): Stack unit
    (requires (fun h -> inv h (UInt32.v i)))
    (ensures (fun h_1 _ h_2 -> FStar.UInt32.(inv h_2 (v i + 1))))
  = let h0' = ST.get() in
    lemma_mul_shift_reduce_spec_def (as_seq h0 output) (as_seq h0 input) (as_seq h0 input) (as_seq h0 input2) (len - UInt32.v i - 1);
    let ctr = FStar.UInt32.(clen -^ i -^ 1ul) in
    let i = FStar.UInt32.(ctr) in
    let j = FStar.UInt32.(clen -^ 1ul -^ i) in
    let input2i = input2.(j) in
    (* lemma_mul_shift_reduce_pre_def (as_seq h0 output) (as_seq h0 input) (as_seq h0 input2) (UInt32.v ctr + 1); *)
    Hacl.Spec.Bignum.Fproduct.lemma_sum_scalar_multiplication_ (as_seq h0' output) (as_seq h0' input)
                                                               (input2i) len;
    sum_scalar_multiplication_ output input input2i;
    if FStar.UInt32.(ctr >^ 0ul) then shift_reduce input;
    let h' = ST.get() in
    if FStar.UInt32.(ctr >^ 0ul) then (
      let open Hacl.Bignum.Limb in
      lemma_shift_reduce_spec (as_seq h0' input);
      lemma_mul_shift_reduce_spec_1 (as_seq h' output) (as_seq h0' output) (as_seq h0 input)
                                   (as_seq h0' input) (as_seq h' input) (as_seq h0' input2)
                                   (v input2i) (FStar.UInt32.v ctr + 1);
      ()
    ) else (
      let open Hacl.Bignum.Limb in
      lemma_mul_shift_reduce_spec_2 (as_seq h' output) (as_seq h0' output) (as_seq h0 input)
                                   (as_seq h0' input) (as_seq h' input) (as_seq h0' input2)
                                   (v input2i);
      ()
    )
    in
  lemma_mul_shift_reduce_spec_def_0 (as_seq h0 output) (as_seq h0 input) (as_seq h0 input) (as_seq h0 input2);
  C.Loops.for 0ul clen inv f'


#reset-options "--z3rlimit 10 --initial_fuel 0 --max_fuel 0"


let as_seq' (h:mem) (b:felem{live h b}) : GTot seqelem = as_seq h b
  

[@"c_inline"]
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
[@"c_inline"]
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
  let h3 = ST.get() in
  pop_frame()


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
  blit input 0ul tmp 0ul clen;
  let h2 = ST.get() in
  lemma_whole_slice (as_seq h2 input);
  lemma_whole_slice (as_seq h2 tmp);
  fmul_ output tmp input2;
  let h3 = ST.get() in
  pop_frame()
