module Hacl.Bignum.Fsquare

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All


open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Bignum.Limb
open Hacl.Spec.Bignum.Bigint
open Hacl.Bignum.Modulo
open Hacl.Bignum.Fproduct
open Hacl.Spec.Bignum.Fsquare

module U32 = FStar.UInt32
module AD  = Hacl.Spec.EC.AddAndDouble


#set-options "--z3rlimit 50 --initial_fuel 0 --max_fuel 0"

[@"substitute"]
private val upd_5:
  tmp:felem_wide -> s0:wide -> s1:wide -> s2:wide -> s3:wide -> s4:wide ->
  Stack unit
    (requires (fun h -> live h tmp))
    (ensures (fun h0 _ h1 -> live h1 tmp /\ as_seq h1 tmp == seq_upd_5 s0 s1 s2 s3 s4
      /\ modifies_1 tmp h0 h1))
[@"substitute"]
private let upd_5 tmp s0 s1 s2 s3 s4 =
  tmp.(0ul) <- s0;
  tmp.(1ul) <- s1;
  tmp.(2ul) <- s2;
  tmp.(3ul) <- s3;
  tmp.(4ul) <- s4;
  let h1 = ST.get() in
  Seq.lemma_eq_intro (as_seq h1 tmp) (seq_upd_5 s0 s1 s2 s3 s4)


[@"c_inline"]
private val fsquare__:
  tmp:felem_wide ->
  output:felem{disjoint tmp output} ->
  Stack unit
    (requires (fun h -> live h tmp /\ live h output /\ fsquare_pre_ (as_seq h output)))
    (ensures (fun h0 _ h1 -> live h0 tmp /\ live h0 output /\ live h1 tmp /\ modifies_1 tmp h0 h1
      /\ fsquare_pre_ (as_seq h0 output)
      /\ as_seq h1 tmp == fsquare_spec_ (as_seq h0 output)))
[@"c_inline"]
private let fsquare__ tmp output =
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


#reset-options "--z3rlimit 100 --max_fuel 0"

[@"c_inline"]
val fsquare_:
  tmp:felem_wide ->
  output:felem{disjoint tmp output} ->
  Stack unit
    (requires (fun h -> live h tmp /\ live h output /\ fsquare_pre (as_seq h output)))
    (ensures (fun h0 _ h1 -> live h0 tmp /\ live h0 output /\ live h1 tmp /\ modifies_2 output tmp h0 h1
      /\ live h1 output
      /\ fsquare_pre (as_seq h0 output)
      /\ as_seq h1 output == fsquare_spec (as_seq h0 output)))
[@"c_inline"]
let fsquare_ tmp output =
  let h0 = ST.get() in
  fsquare__ tmp output;
  let h3  = ST.get() in
  Hacl.Bignum.Fproduct.carry_wide_ tmp;
  carry_top_wide tmp;
  copy_from_wide_ output tmp;
  carry_0_to_1 output


#set-options "--initial_ifuel 0 --max_ifuel 0 --initial_fuel 1 --max_fuel 1"

private val relax: s:seqelem -> Lemma
  (requires (AD.red_513 s))
  (ensures  (AD.red_5413 s))
let relax s = ()

private val fsquare_times_one: s:seqelem{AD.red_5413 s} -> Lemma
  (fsquare_pre s /\ fsquare_times_tot s 1 == fsquare_spec s)
let fsquare_times_one s =
  fsquare_5413_is_fine s

private val fsquare_times_many: s:seqelem{AD.red_5413 s} -> i:pos{i > 1} -> Lemma
  (fsquare_pre s /\
   AD.red_5413 (fsquare_spec s) /\
   fsquare_times_tot s i == fsquare_times_tot (fsquare_spec s) (i - 1))
let fsquare_times_many s i =
  fsquare_5413_is_fine s

#set-options "--z3rlimit 200 --initial_fuel 0 --max_fuel 0"

private val fsquare_fsquare_times: s:seqelem{AD.red_5413 s} -> i:pos -> j:pos -> Lemma
  (ensures (AD.red_5413 (fsquare_times_tot s i) /\
            fsquare_times_tot (fsquare_times_tot s i) j == fsquare_times_tot s (i + j)))
  (decreases i)
let rec fsquare_fsquare_times s i j =
  relax (fsquare_times_tot s i);
  if i = 1 then
    begin
    fsquare_times_one s;
    fsquare_times_many s (i + j)
    end
  else
    begin
    fsquare_5413_is_fine s;
    relax (fsquare_times_tot s i);
    relax (fsquare_spec s);
    fsquare_times_many s i;
    assert (fsquare_times_tot (fsquare_times_tot s i) j ==
            fsquare_times_tot (fsquare_times_tot (fsquare_spec s) (i - 1)) j);
    fsquare_fsquare_times (fsquare_spec s) (i - 1) j;
    assert (fsquare_times_tot (fsquare_times_tot (fsquare_spec s) (i - 1)) j ==
            fsquare_times_tot (fsquare_spec s) (i + j - 1));
    fsquare_times_many s (i + j);
    assert (fsquare_times_tot (fsquare_spec s) (i + j - 1) ==
            fsquare_times_tot s (i + j))
    end

#set-options "--z3rlimit 50"

[@"c_inline"]
private val fsquare_times_:
  input:felem ->
  tmp:felem_wide{disjoint input tmp} ->
  count:U32.t{U32.v count > 0} ->
  Stack unit
    (requires (fun h -> live h input /\ live h tmp /\ AD.red_5413 (as_seq h input)))
    (ensures  (fun h0 _ h1 ->
        live h1 input /\ live h1 tmp
      /\ modifies_2 input tmp h0 h1
      /\ AD.red_5413 (as_seq h0 input)
      /\ AD.red_513 (as_seq h1 input)
      /\ as_seq h1 input == fsquare_times_tot (as_seq h0 input) (U32.v count)))
let fsquare_times_ input tmp count =
  let h0 = ST.get() in
  let inv h i =
    1 <= i /\ i <= U32.v count /\
    live h input /\ live h tmp /\
    modifies_2 input tmp h0 h /\
    AD.red_513 (as_seq h input) /\
    as_seq h input == fsquare_times_tot (as_seq h0 input) i
  in
  fsquare_times_one (as_seq h0 input);
  fsquare_5413_is_fine (as_seq h0 input);
  fsquare_ tmp input;
  C.Compat.Loops.for 1ul count inv (fun i ->
    let h1 = ST.get() in
    relax (as_seq h1 input);
    fsquare_5413_is_fine (as_seq h1 input);
    fsquare_ tmp input;
    let h2 = ST.get() in
    fsquare_times_one (as_seq h1 input);
    fsquare_fsquare_times (as_seq h0 input) (U32.v i) 1;
    lemma_modifies_2_trans input tmp h0 h1 h2
  )


#set-options "--z3rlimit 10"

[@"c_inline"]
val fsquare_times:
  output:felem ->
  input:felem{disjoint output input} ->
  count:U32.t{U32.v count > 0} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input /\ AD.red_5413 (as_seq h input)))
    (ensures (fun h0 _ h1 ->
        live h0 output /\ live h1 output /\ live h0 input /\ modifies_1 output h0 h1
      /\ AD.red_5413 (as_seq h0 input)
      /\ AD.red_513 (as_seq h1 output)
      /\ as_seq h1 output == fsquare_times_tot (as_seq h0 input) (U32.v count)))
[@"c_inline"]
let fsquare_times output input count =
  push_frame();
  let h0 = ST.get() in
  let t = create wide_zero clen in
  let h1 = ST.get() in
  blit input 0ul output 0ul clen;
  let h2 = ST.get() in
  Hacl.Spec.Bignum.Fmul.lemma_whole_slice (as_seq h1 input);
  Hacl.Spec.Bignum.Fmul.lemma_whole_slice (as_seq h2 output);
  fsquare_times_ output t count;
  let h3 = ST.get() in
  lemma_modifies_1_2'' output t h1 h2 h3;
  lemma_modifies_0_2 output t h0 h1 h3;
  pop_frame()


[@"c_inline"]
val fsquare_times_inplace:
  output:felem ->
  count:U32.t{U32.v count > 0} ->
  Stack unit
    (requires (fun h -> live h output /\ AD.red_5413 (as_seq h output)))
    (ensures (fun h0 _ h1 -> live h0 output /\ live h1 output /\ modifies_1 output h0 h1
      /\ AD.red_513 (as_seq h1 output)
      /\ AD.red_5413 (as_seq h0 output)
      /\ (as_seq h1 output) == fsquare_times_tot (as_seq h0 output) (U32.v count)))
[@"c_inline"]
let fsquare_times_inplace output count =
  push_frame();
  let t   = create wide_zero clen in
  let h1 = ST.get() in
  Hacl.Spec.Bignum.Fmul.lemma_whole_slice (as_seq h1 output);
  fsquare_times_ output t count;
  pop_frame()
