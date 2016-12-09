module Hacl.Bignum.Fproduct


open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Bignum.Bigint
open Hacl.Bignum.Limb
open Hacl.Bignum.Modulo
open Hacl.Bignum.Fproduct.Spec

module U32 = FStar.UInt32

#set-options "--z3rlimit 50 --initial_fuel 1 --max_fuel 1"

val copy_from_wide_:
  output:felem ->
  input:felem_wide{disjoint output input} ->
  ctr:U32.t{U32.v ctr <= len} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input /\ copy_from_wide_pre (as_seq h input)
      /\ (forall (i:nat). (i >= U32.v ctr /\ i < len) ==> v (get h output i) == w (get h input i))))
    (ensures (fun h0 _ h1 -> live h0 input /\ copy_from_wide_pre (as_seq h0 input) /\ live h1 output
      /\ modifies_1 output h0 h1
      /\ as_seq h1 output == copy_from_wide_spec (as_seq h0 input) ))
let rec copy_from_wide_ output input ctr =
  if U32.(ctr =^ 0ul) then (
    let h = ST.get() in
    assert(forall (i:nat). i < len ==> v (Seq.index (as_seq h output) i) = w (Seq.index (as_seq h input) i));
    Seq.lemma_eq_intro (as_seq h output) (copy_from_wide_spec (as_seq h input))
  )
  else (
    let i = U32.(ctr -^ 1ul) in
    let inputi = input.(i) in
    Math.Lemmas.modulo_lemma (w inputi) (pow2 n);
    output.(i) <- wide_to_limb inputi;
    copy_from_wide_ output input i
  )


#set-options "--z3rlimit 50"

val shift_:
  output:felem ->
  ctr:U32.t{U32.v ctr < len} ->
  Stack unit
    (requires (fun h -> live h output))
    (ensures (fun h0 _ h1 -> live h0 output /\ live h1 output /\ modifies_1 output h0 h1
      /\ (forall (i:nat). (i < U32.v ctr) ==> v (get h1 output (i+1)) = v (get h0 output i))
      /\ (forall (i:nat). (i > U32.v ctr /\ i < len) ==> get h1 output i == get h0 output i)))
let rec shift_ output ctr =
  let open FStar.UInt32 in
  if (ctr =^ 0ul) then ()
  else (
    let z = output.(ctr -^ 1ul) in
    output.(ctr) <- z;
    shift_ output (ctr -^ 1ul)
  )

#set-options "--z3rlimit 50"


val shift:
  output:felem ->
  Stack unit
    (requires (fun h -> live h output))
    (ensures (fun h0 _ h1 -> live h0 output /\ live h1 output /\ modifies_1 output h0 h1
      /\ as_seq h1 output == shift_spec (as_seq h0 output)))
let rec shift output =
  let h0 = ST.get() in
  let open FStar.UInt32 in
  let tmp = output.(clen -^ 1ul) in
  shift_ output (clen -^ 1ul);
  output.(0ul) <- tmp;
  let h = ST.get() in
  Seq.lemma_eq_intro (as_seq h output) (shift_spec (as_seq h0 output))

#set-options "--z3rlimit 20"


#set-options "--z3rlimit 20 --initial_fuel 1 --max_fuel 1"

val sum_scalar_multiplication_:
  output:felem_wide ->
  input:felem{disjoint output input} ->
  s:limb ->
  ctr:U32.t{U32.v ctr <= len} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input /\ sum_scalar_multiplication_pre_ (as_seq h output) (as_seq h input) s (U32.v ctr)))
    (ensures (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1 /\ live h0 input /\ live h0 output
      /\ sum_scalar_multiplication_pre_ (as_seq h0 output) (as_seq h0 input) s (U32.v ctr)
      /\ (as_seq h1 output) == sum_scalar_multiplication_spec (as_seq h0 output) (as_seq h0 input) s (U32.v ctr)))
let rec sum_scalar_multiplication_ output input s ctr =
  if U32.(ctr =^ 0ul) then ()
  else (
    let i = U32.(ctr -^ 1ul) in
    let oi = output.(i) in let ii = input.(i) in
    let open Hacl.Bignum.Wide in
    output.(i) <- (oi +^ (ii *^ s));
    let h = ST.get() in
    sum_scalar_multiplication_ output input s i
  )


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
  input:felem{disjoint output input} ->
  input2:felem{disjoint output input2 /\ disjoint input input2}  ->
  ctr:U32.t{U32.v ctr <= len} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input /\ live h input2
      /\ mul_shift_reduce_pre (as_seq h output) (as_seq h input) (as_seq h input2) (U32.v ctr)))
    (ensures (fun h0 _ h1 -> live h0 output /\ live h0 input /\ live h0 input2 /\ modifies_2 output input h0 h1
      /\ live h1 output /\ live h1 input
      /\ mul_shift_reduce_pre (as_seq h0 output) (as_seq h0 input) (as_seq h0 input2) (U32.v ctr)
      /\ as_seq h1 output == mul_shift_reduce_spec (as_seq h0 output) (as_seq h0 input) (as_seq h0 input2) (U32.v ctr)))
let rec mul_shift_reduce_ output input input2 ctr =
  let open FStar.UInt32 in
  if (ctr =^ 0ul) then ()
  else (
    let h0 = ST.get() in
    let i = ctr -^ 1ul in
    let j = clen -^ 1ul -^ i in
    let input2i = input2.(j) in
    sum_scalar_multiplication_ output input input2i clen;
    if (ctr >^ 1ul) then shift_reduce input;
    mul_shift_reduce_ output input input2 i
  )



val carry_wide_:
  t:felem_wide ->
  ctr:U32.t{U32.v ctr < len} ->
  Stack unit
    (requires (fun h -> live h t /\ carry_wide_pre (as_seq h t) (U32.v ctr)))
    (ensures (fun h0 _ h1 -> live h0 t /\ live h1 t /\ modifies_1 t h0 h1
      /\ carry_wide_pre (as_seq h0 t) (U32.v ctr)
      /\ as_seq h1 t == carry_wide_spec (as_seq h0 t) (U32.v ctr)))
let rec carry_wide_ tmp ctr =
  if U32.(ctr =^ clen -^ 1ul) then ()
  else (
    let tctr = tmp.(ctr) in
    let tctrp1 = tmp.(U32.(ctr+^1ul)) in
    assert_norm(pow2 0 = 1);
    Math.Lemmas.pow2_lt_compat limb_size 0;
    Math.Lemmas.pow2_lt_compat limb_n limb_size;
    Math.Lemmas.modulo_lemma (pow2 limb_size) (pow2 limb_n);
    let r0 = wide_to_limb (tctr) &^ ((limb_one <<^ climb_size) -^ limb_one) in
    UInt.logand_mask #limb_n (v (wide_to_limb tctr)) limb_size;
    Math.Lemmas.pow2_plus (limb_n - limb_size) (limb_size);
    Math.Lemmas.modulo_modulo_lemma (w tctr) (pow2 limb_size) (pow2 (limb_n - limb_size));
    assert(v r0 = w tctr % pow2 limb_size);
    assert(v r0 < pow2 limb_size);
    let open Hacl.Bignum.Wide in
    let c  = tctr >>^ climb_size in
    Math.Lemmas.pow2_lt_compat (wide_n - 1) (limb_n);
    Math.Lemmas.pow2_double_sum (wide_n - 1);
    Math.Lemmas.lemma_div_lt (w tctr) (wide_n) (limb_size);
    Math.Lemmas.pow2_le_compat (wide_n - 1) (wide_n - limb_size);
    tmp.(ctr) <- limb_to_wide r0;
    tmp.(U32.(ctr +^ 1ul)) <- tctrp1 +^ c;
    carry_wide_ tmp (U32.(ctr +^ 1ul))
  )


#set-options "--z3rlimit 5"

#set-options "--z3rlimit 20"

val carry_0_to_1:
  output:felem ->
  Stack unit
    (requires (fun h -> live h output /\ carry_0_to_1_pre (as_seq h output)))
    (ensures (fun h0 _ h1 -> live h0 output /\ live h1 output /\ modifies_1 output h0 h1
      /\ carry_0_to_1_pre (as_seq h0 output)
      /\ as_seq h1 output == carry_0_to_1_spec (as_seq h0 output)))
let carry_0_to_1 output =
  assume (length output > 1);
  let i0 = output.(0ul) in
  let i1 = output.(1ul) in
  assert_norm(pow2 0 = 1);
  Math.Lemmas.pow2_lt_compat limb_size 0;
  Math.Lemmas.pow2_lt_compat limb_n limb_size;
  Math.Lemmas.modulo_lemma (pow2 limb_size) (pow2 limb_n);
  UInt.logand_mask #limb_n (v i0) limb_size;
  Math.Lemmas.pow2_plus (limb_n - limb_size) (limb_size);
  Math.Lemmas.modulo_modulo_lemma (v i0) (pow2 limb_size) (pow2 (limb_n - limb_size));
  Math.Lemmas.pow2_double_sum (limb_n - 1);
  Math.Lemmas.pow2_le_compat (limb_n - 1) limb_size;
  Math.Lemmas.lemma_div_lt (v i0) (limb_n) (limb_size);
  Math.Lemmas.pow2_le_compat (limb_n - 1) (limb_n - limb_size);
  let i0' = i0 &^ ((limb_one <<^ climb_size) -^ limb_one) in
  cut (v i1 < pow2 (limb_size));
  let i1'   = i1 +^ (i0 >>^ climb_size) in
  output.(0ul) <- i0';
  output.(1ul) <- i1'

#set-options "--z3rlimit 40"


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
  mul_shift_reduce_ t input input2 clen;
  carry_wide_ t 0ul;
  reduce_wide t;
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
