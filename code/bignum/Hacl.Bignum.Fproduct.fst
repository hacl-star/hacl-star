module Hacl.Bignum.Fproduct


open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Bignum.Limb
open Hacl.Bignum.Modulo
open Hacl.Spec.Bignum.Fproduct

module U32 = FStar.UInt32

#set-options "--z3rlimit 50 --initial_fuel 1 --max_fuel 1"

[@"c_inline"]
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
[@"c_inline"]
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

[@"c_inline"]
val shift_:
  output:felem ->
  ctr:U32.t{U32.v ctr < len} ->
  Stack unit
    (requires (fun h -> live h output))
    (ensures (fun h0 _ h1 -> live h0 output /\ live h1 output /\ modifies_1 output h0 h1
      /\ (forall (i:nat). (i < U32.v ctr) ==> v (get h1 output (i+1)) = v (get h0 output i))
      /\ (forall (i:nat). (i > U32.v ctr /\ i < len) ==> get h1 output i == get h0 output i)))
[@"c_inline"]
let rec shift_ output ctr =
  let open FStar.UInt32 in
  if (ctr =^ 0ul) then ()
  else (
    let z = output.(ctr -^ 1ul) in
    output.(ctr) <- z;
    shift_ output (ctr -^ 1ul)
  )

#set-options "--z3rlimit 50"


[@"c_inline"]
val shift:
  output:felem ->
  Stack unit
    (requires (fun h -> live h output))
    (ensures (fun h0 _ h1 -> live h0 output /\ live h1 output /\ modifies_1 output h0 h1
      /\ as_seq h1 output == shift_spec (as_seq h0 output)))
[@"c_inline"]
let rec shift output =
  let h0 = ST.get() in
  let open FStar.UInt32 in
  let tmp = output.(clen -^ 1ul) in
  shift_ output (clen -^ 1ul);
  output.(0ul) <- tmp;
  let h = ST.get() in
  Seq.lemma_eq_intro (as_seq h output) (shift_spec (as_seq h0 output))


#set-options "--z3rlimit 20 --initial_fuel 1 --max_fuel 1"

[@"c_inline"]
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
[@"c_inline"]
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

#set-options "--z3rlimit 100 --initial_fuel 1 --max_fuel 1"

[@"c_inline"]
val carry_wide_:
  t:felem_wide ->
  ctr:U32.t{U32.v ctr < len} ->
  Stack unit
    (requires (fun h -> live h t /\ carry_wide_pre (as_seq h t) (U32.v ctr)))
    (ensures (fun h0 _ h1 -> live h0 t /\ live h1 t /\ modifies_1 t h0 h1
      /\ carry_wide_pre (as_seq h0 t) (U32.v ctr)
      /\ as_seq h1 t == carry_wide_spec (as_seq h0 t) (U32.v ctr)))
[@"c_inline"]
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


#reset-options "--z3rlimit 200 --initial_fuel 1 --max_fuel 1"

[@"c_inline"]
val carry_limb_:
  t:felem ->
  ctr:U32.t{U32.v ctr < len} ->
  Stack unit
    (requires (fun h -> live h t /\ carry_limb_pre (as_seq h t) (U32.v ctr)))
    (ensures (fun h0 _ h1 -> live h0 t /\ live h1 t /\ modifies_1 t h0 h1
      /\ carry_limb_pre (as_seq h0 t) (U32.v ctr)
      /\ as_seq h1 t == carry_limb_spec (as_seq h0 t) (U32.v ctr)))
[@"c_inline"]
let rec carry_limb_ tmp ctr =
  if U32.(ctr =^ clen -^ 1ul) then ()
  else (
    let tctr = tmp.(ctr) in
    let tctrp1 = tmp.(U32.(ctr+^1ul)) in
    assert_norm(pow2 0 = 1);
    Math.Lemmas.pow2_lt_compat limb_size 0;
    Math.Lemmas.pow2_lt_compat limb_n limb_size;
    Math.Lemmas.modulo_lemma (pow2 limb_size) (pow2 limb_n);
    let r0 = (tctr) &^ ((limb_one <<^ climb_size) -^ limb_one) in
    UInt.logand_mask #limb_n (v ( tctr)) limb_size;
    Math.Lemmas.pow2_plus (limb_n - limb_size) (limb_size);
    Math.Lemmas.modulo_modulo_lemma (v tctr) (pow2 limb_size) (pow2 (limb_n - limb_size));
    assert(v r0 = v tctr % pow2 limb_size);
    assert(v r0 < pow2 limb_size);
    let open Hacl.Bignum.Limb in
    let c  = tctr >>^ climb_size in
    Math.Lemmas.pow2_double_sum (limb_n - 1);
    Math.Lemmas.lemma_div_lt (v tctr) (limb_n) (limb_size);
    Math.Lemmas.pow2_le_compat (limb_n - 1) (limb_n - limb_size);
    tmp.(ctr) <-  r0;
    tmp.(U32.(ctr +^ 1ul)) <- tctrp1 +^ c;
    carry_limb_ tmp (U32.(ctr +^ 1ul))
  )


#set-options "--z3rlimit 20"

[@"c_inline"]
val carry_0_to_1:
  output:felem ->
  Stack unit
    (requires (fun h -> live h output /\ carry_0_to_1_pre (as_seq h output)))
    (ensures (fun h0 _ h1 -> live h0 output /\ live h1 output /\ modifies_1 output h0 h1
      /\ carry_0_to_1_pre (as_seq h0 output)
      /\ as_seq h1 output == carry_0_to_1_spec (as_seq h0 output)))
[@"c_inline"]
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

