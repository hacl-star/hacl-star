module Hacl.Bignum.Fsquare


open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Bignum.Limb
open Hacl.Spec.Bignum.Bigint
open Hacl.Bignum.Modulo
open Hacl.Bignum.Fproduct
open Hacl.Spec.Bignum.Fsquare


#set-options "--z3rlimit 50 --initial_fuel 0 --max_fuel 0"

[@"c_inline"]
private inline_for_extraction val upd_5:
  tmp:felem_wide -> s0:wide -> s1:wide -> s2:wide -> s3:wide -> s4:wide ->
  Stack unit
    (requires (fun h -> live h tmp))
    (ensures (fun h0 _ h1 -> live h1 tmp /\ as_seq h1 tmp == seq_upd_5 s0 s1 s2 s3 s4
      /\ modifies_1 tmp h0 h1))
[@"c_inline"]
private inline_for_extraction let upd_5 tmp s0 s1 s2 s3 s4 =
  tmp.(0ul) <- s0;
  tmp.(1ul) <- s1;
  tmp.(2ul) <- s2;
  tmp.(3ul) <- s3;
  tmp.(4ul) <- s4;
  let h1 = ST.get() in
  Seq.lemma_eq_intro (as_seq h1 tmp) (seq_upd_5 s0 s1 s2 s3 s4)


#set-options "--z3rlimit 50 --initial_fuel 0 --max_fuel 0"

[@"c_inline"]
private inline_for_extraction val fsquare__:
  tmp:felem_wide ->
  output:felem{disjoint tmp output} ->
  Stack unit
    (requires (fun h -> live h tmp /\ live h output /\ fsquare_pre_ (as_seq h output)))
    (ensures (fun h0 _ h1 -> live h0 tmp /\ live h0 output /\ live h1 tmp /\ modifies_1 tmp h0 h1
      /\ fsquare_pre_ (as_seq h0 output)
      /\ as_seq h1 tmp == fsquare_spec_ (as_seq h0 output)))
[@"c_inline"]
private inline_for_extraction let fsquare__ tmp output =
  let h0 = ST.get() in
  let r0 = output.(0ul) in
  let r1 = output.(1ul) in
  let r2 = output.(2ul) in
  let r3 = output.(3ul) in
  let r4 = output.(4ul) in
  let d0 = r0 *^ (uint64_to_limb 2uL) in
  let d1 = r1 *^ (uint64_to_limb 2uL) in
  let d2 = r2 *^ (uint64_to_limb 2uL) *^ (uint64_to_limb 19uL) in
  let d419 = r4 *^ (uint64_to_limb 19uL) in
  let d4 = d419 *^ (uint64_to_limb 2uL) in
  let open Hacl.UInt128 in
  let s0 = computation_1 r0 r1 r2 r3 r4 d4 d2 in
  let s1 =  computation_2 r0 r1 r2 r3 r4 d4 d0 in
  let s2 =  computation_3 r0 r1 r2 r3 r4 d4 d0 in
  let s3 = computation_4 r0 r1 r2 r3 r4 d419 d0 d1 in
  let s4 = computation_5 r0 r1 r2 r3 r4 d0 d1 in
  upd_5 tmp s0 s1 s2 s3 s4;
  let h1 = ST.get() in
  Seq.lemma_eq_intro (as_seq h1 tmp) (fsquare_spec_ (as_seq h0 output))


#set-options "--z3rlimit 5"

[@"c_inline"]
private inline_for_extraction val fsquare_:
  tmp:felem_wide ->
  output:felem{disjoint tmp output} ->
  Stack unit
    (requires (fun h -> live h tmp /\ live h output /\ fsquare_pre (as_seq h output)))
    (ensures (fun h0 _ h1 -> live h0 tmp /\ live h0 output /\ live h1 tmp /\ modifies_2 output tmp h0 h1
      /\ live h1 output
      /\ fsquare_pre (as_seq h0 output)
      /\ as_seq h1 output == fsquare_spec (as_seq h0 output)))
[@"c_inline"]
private inline_for_extraction let fsquare_ tmp output =
  let h0 = ST.get() in
  fsquare__ tmp output;
  let h3  = ST.get() in
  Hacl.Bignum.Fproduct.carry_wide_ tmp 0ul;
  carry_top_wide tmp;
  copy_from_wide_ output tmp clen;
  carry_0_to_1 output


#set-options "--z3rlimit 100 --initial_fuel 1 --max_fuel 1"

[@"c_inline"]
private val fsquare_times_:
  input:felem ->
  tmp:felem_wide{disjoint input tmp} ->
  count:FStar.UInt32.t{FStar.UInt32.v count > 0} ->
  Stack unit
    (requires (fun h -> live h input /\ live h tmp /\ Hacl.Spec.EC.AddAndDouble.red_5413 (as_seq h input)))
    (ensures (fun h0 _ h1 -> live h0 input /\ live h1 input /\ live h1 tmp /\ modifies_2 input tmp h0 h1
      /\ Hacl.Spec.EC.AddAndDouble.red_5413 (as_seq h0 input)
      /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h1 input)
      /\ as_seq h1 input == fsquare_times_tot (as_seq h0 input) (FStar.UInt32.v count)))
[@"c_inline"]
private let rec fsquare_times_ output tmp count =
  if FStar.UInt32.(count =^ 1ul) then (
    let h0 = ST.get() in
    fsquare_5413_is_fine (as_seq h0 output);
    fsquare_  tmp output
  )
  else (
    let i = FStar.UInt32.(count -^ 1ul) in
    cut (FStar.UInt32.v i > 0);
    let h0 = ST.get() in
    fsquare_5413_is_fine (as_seq h0 output);
    fsquare_  tmp output;
    let h1 = ST.get() in
    cut (Hacl.Spec.EC.AddAndDouble.red_5413 (as_seq h1 output));
    cut (modifies_2 tmp output h0 h1);
    fsquare_times_ output tmp i
  )


#set-options "--z3rlimit 10 --initial_fuel 0 --max_fuel 0"

[@"c_inline"]
inline_for_extraction val fsquare_times:
  output:felem ->
  input:felem{disjoint output input} ->
  count:FStar.UInt32.t{FStar.UInt32.v count > 0} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input /\ Hacl.Spec.EC.AddAndDouble.red_5413 (as_seq h input)))
    (ensures (fun h0 _ h1 -> live h0 output /\ live h1 output /\ live h0 input /\ modifies_1 output h0 h1
      /\ Hacl.Spec.EC.AddAndDouble.red_5413 (as_seq h0 input)
      /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h1 output)
      /\ (as_seq h1 output) == fsquare_times_tot (as_seq h0 input) (FStar.UInt32.v count)))
[@"c_inline"]
inline_for_extraction let fsquare_times output input count =
  push_frame();
  let t   = create wide_zero clen in
  let h0 = ST.get() in
  blit input 0ul output 0ul clen;
  let h1 = ST.get() in
  Hacl.Spec.Bignum.Fmul.lemma_whole_slice (as_seq h0 input);
  Hacl.Spec.Bignum.Fmul.lemma_whole_slice (as_seq h1 output);
  fsquare_times_ output t count;
  pop_frame()


[@"c_inline"]
inline_for_extraction val fsquare_times_inplace:
  output:felem ->
  count:FStar.UInt32.t{FStar.UInt32.v count > 0} ->
  Stack unit
    (requires (fun h -> live h output /\ Hacl.Spec.EC.AddAndDouble.red_5413 (as_seq h output)))
    (ensures (fun h0 _ h1 -> live h0 output /\ live h1 output /\ modifies_1 output h0 h1
      /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h1 output)
      /\ Hacl.Spec.EC.AddAndDouble.red_5413 (as_seq h0 output)
      /\ (as_seq h1 output) == fsquare_times_tot (as_seq h0 output) (FStar.UInt32.v count)))
[@"c_inline"]
inline_for_extraction let fsquare_times_inplace output count =
  push_frame();
  let t   = create wide_zero clen in
  let h1 = ST.get() in
  Hacl.Spec.Bignum.Fmul.lemma_whole_slice (as_seq h1 output);
  fsquare_times_ output t count;
  pop_frame()
