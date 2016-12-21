module Hacl.Bignum.Fmul


open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Bignum.Limb
open Hacl.Bignum.Modulo
open Hacl.Bignum.Fproduct
open Hacl.Spec.Bignum.Fmul.Lemmas
open Hacl.Spec.Bignum.Fmul
open Hacl.Spec.Bignum.Fmul2

module U32 = FStar.UInt32

#set-options "--z3rlimit 40"


val shift_reduce: output:felem -> Stack unit
  (requires (fun h -> live h output /\ shift_reduce_pre (as_seq h output)))
  (ensures (fun h0 _ h1 -> live h0 output /\ live h1 output /\ modifies_1 output h0 h1
    /\ shift_reduce_pre (as_seq h0 output)
    /\ as_seq h1 output == shift_reduce_spec (as_seq h0 output)))
let shift_reduce output =
  shift output;
  reduce output


#set-options "--z3rlimit 50 --initial_fuel 1 --max_fuel 1"

val mul_shift_reduce_:
  output:felem_wide ->
  init_input:Ghost.erased seqelem ->
  input:felem{disjoint output input} ->
  input2:felem{disjoint output input2 /\ disjoint input input2}  ->
  ctr:U32.t{U32.v ctr <= len} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input /\ live h input2
      /\ mul_shift_reduce_pre (as_seq h output) (Ghost.reveal init_input) (as_seq h input) (as_seq h input2) (U32.v ctr)))
    (ensures (fun h0 _ h1 -> live h0 output /\ live h0 input /\ live h0 input2 /\ modifies_2 output input h0 h1
      /\ live h1 output /\ live h1 input
      /\ mul_shift_reduce_pre (as_seq h0 output) (Ghost.reveal init_input) (as_seq h0 input) (as_seq h0 input2) (U32.v ctr)
      /\ as_seq h1 output == mul_shift_reduce_spec_ (as_seq h0 output) (Ghost.reveal init_input) (as_seq h0 input) (as_seq h0 input2) (U32.v ctr)
      ))
let rec mul_shift_reduce_ output init_input input input2 ctr =
  let open FStar.UInt32 in
  if (ctr =^ 0ul) then ()
  else (
    let h0 = ST.get() in
    let i = ctr -^ 1ul in
    let j = clen -^ 1ul -^ i in
    let input2i = input2.(j) in
    sum_scalar_multiplication_ output input input2i clen;
    if (ctr >^ 1ul) then shift_reduce input;
    mul_shift_reduce_ output init_input input input2 i
  )


val fmul_:
  output:felem ->
  input:felem{disjoint output input} ->
  input2:felem{disjoint output input2 /\ disjoint input input2} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input /\ live h input2
      /\ fmul_pre (as_seq h input) (as_seq h input2)))
    (ensures (fun h0 _ h1 -> live h0 output /\ live h0 output /\ live h0 input /\ live h0 input2 
      /\ modifies_2 output input h0 h1 /\ live h1 output /\ live h1 input
      /\ fmul_pre (as_seq h0 input) (as_seq h0 input2)
      /\ as_seq h1 output == fmul_spec (as_seq h0 input) (as_seq h0 input2)
      ))
let fmul_ output input input2 =
  let h0 = ST.get() in
  lemma_mul_to_red (as_seq h0 input) (as_seq h0 input2);
  push_frame();
  let h1 = ST.get() in
  let t   = create wide_zero clen in
  let h2 = ST.get() in
  (* TODO: something more developer friendly ? *)
  let input_init = Ghost.elift2_p #HyperStack.mem #felem
                                  #(fun h x -> live h x) #seqelem 
                                  (as_seq) (Ghost.hide h2) (Ghost.hide input) in
  mul_shift_reduce_ t input_init input input2 clen;
  carry_wide_ t 0ul;
  carry_top_wide t;
  copy_from_wide_ output t clen;
  carry_0_to_1 output;
  let h3 = ST.get() in
  assume (modifies_2 output input h1 h3);
  pop_frame()


val fmul:
  output:felem ->
  input:felem{disjoint output input} ->
  input2:felem{disjoint output input2} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input /\ live h input2
      /\ fmul_pre (as_seq h input) (as_seq h input2)))
    (ensures (fun h0 _ h1 -> live h0 output /\ live h0 output /\ live h0 input /\ live h0 input2
      /\ modifies_1 output h0 h1 /\ live h1 output
      /\ fmul_pre (as_seq h0 input) (as_seq h0 input2)
      /\ as_seq h1 output == fmul_spec (as_seq h0 input) (as_seq h0 input2)
      ))
let fmul output input input2 =
  let h0 = ST.get() in
  lemma_mul_to_red (as_seq h0 input) (as_seq h0 input2);
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


#set-options "--lax"

val fsquare_times_:
  input:felem ->
  count:U32.t ->
  Stack unit
    (requires (fun _ -> true))
    (ensures (fun _ _ _ -> true))
let rec fsquare_times_ tmp count =
  if U32.(count =^ 0ul) then ()
  else (
    fmul tmp tmp tmp;
    fsquare_times_ tmp (U32.(count -^ 1ul))
  )


val fsquare_times:
  output:felem ->
  input:felem ->
  count:U32.t ->
  Stack unit
    (requires (fun _ -> true))
    (ensures (fun _ _ _ -> true))
let fsquare_times output input count =
  push_frame();
  let tmp = create limb_zero clen in
  blit input 0ul tmp 0ul clen;
  fsquare_times_ tmp count;
  blit tmp 0ul output 0ul clen;
  pop_frame()
