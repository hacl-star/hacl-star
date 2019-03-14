module Hacl.Bignum.Fproduct

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All


open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Bignum.Limb
open Hacl.Bignum.Modulo
open Hacl.Spec.Bignum.Fproduct

module U32 = FStar.UInt32

#reset-options "--z3rlimit 50 --max_fuel 0 --max_fuel 0"

[@"c_inline"]
val copy_from_wide_:
  output:felem ->
  input:felem_wide{disjoint output input} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input /\ copy_from_wide_pre (as_seq h input)))
    (ensures (fun h0 _ h1 -> live h0 input /\ copy_from_wide_pre (as_seq h0 input) /\ live h1 output
      /\ modifies_1 output h0 h1
      /\ as_seq h1 output == copy_from_wide_spec (as_seq h0 input) ))
[@"c_inline"]
let copy_from_wide_ output input  =
  C.Compat.Loops.map output input clen (fun x -> wide_to_limb x)


#reset-options "--z3rlimit 100 --max_fuel 0 --max_fuel 0"

private
let lemma_variable_change h h0 (b:felem{live h0 b /\ live h b}) : Lemma
  (requires (forall (i:nat). (i <= len - 1 /\ i > 0) ==> v (get h b i) == v (get h0 b (i-1))))
  (ensures (forall (i:nat). (i < len - 1) ==> v (get h b (i+1)) == v (get h0 b (i))))
  = ()

[@"substitute"]
val shift_:
  output:felem ->
  Stack unit
    (requires (fun h -> live h output))
    (ensures (fun h0 _ h1 -> live h0 output /\ live h1 output /\ modifies_1 output h0 h1
      /\ (forall (i:nat). (i < len - 1) ==> v (get h1 output (i+1)) = v (get h0 output i)) ))
  
[@"substitute"]
let shift_ output =
  let h0 = ST.get() in
  let inv (h1: HyperStack.mem) (j: nat): Type0 =
    live h1 output /\ modifies_1 output h0 h1 /\ j <= len - 1 /\ 0 <= j
    /\ (forall (i:nat). {:pattern (v (get h1 output (i)))} (i <= len - 1 /\ i > (len-1-j)) ==> v (get h1 output (i)) = v (get h0 output (i-1)))
    /\ (forall (i:nat). {:pattern (v (get h1 output (i)))} (i < (len - 1 - j)) ==> get h1 output i == get h0 output i)
  in
  let open FStar.UInt32 in
  let f' (i:UInt32.t{FStar.UInt32.( 0 <= v i /\ v i < len - 1) }): Stack unit
    (requires (fun h -> inv h (UInt32.v i)))
    (ensures (fun h_1 _ h_2 -> FStar.UInt32.(inv h_1 (v i) /\ inv h_2 (v i + 1))))
  = let h = ST.get() in
    assert(forall (j:nat). (j <= len - 1 /\ j > len - 1 - v i) ==> Hacl.Bignum.Limb.v (get h output (j)) = Hacl.Bignum.Limb.v (get h0 output (j-1)));
    assert(forall (j:nat). (j < len - 1 - v i) ==> Hacl.Bignum.Limb.v (get h output (j)) = Hacl.Bignum.Limb.v (get h0 output j));
    let ctr = clen -^ i -^ 1ul in
    let z = output.(ctr -^ 1ul) in
    output.(ctr) <- z;
    let h' = ST.get() in
    assert(Hacl.Bignum.Limb.v (get h' output (v ctr)) = Hacl.Bignum.Limb.v (get h0 output (v ctr-1)));
    assert(forall (j:nat). (j <= len - 1 /\ j > len - 1 - (v i+1)) ==> Hacl.Bignum.Limb.v (get h' output (j)) = Hacl.Bignum.Limb.v (get h0 output (j-1)))
  in
  C.Compat.Loops.for 0ul (clen -^ 1ul) inv f';
  let h = ST.get() in
  assert(forall (i:nat). (i <= len - 1 /\ i > 0) ==> Hacl.Bignum.Limb.v (get h output (i)) == Hacl.Bignum.Limb.v (get h0 output (i-1)));
  lemma_variable_change h h0 output

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

[@"substitute"]
val shift:
  output:felem ->
  Stack unit
    (requires (fun h -> live h output))
    (ensures (fun h0 _ h1 -> live h0 output /\ live h1 output /\ modifies_1 output h0 h1
      /\ as_seq h1 output == shift_spec (as_seq h0 output)))
[@"substitute"]
let shift output =
  let h0 = ST.get() in
  let open FStar.UInt32 in
  let tmp = output.(clen -^ 1ul) in
  shift_ output;
  output.(0ul) <- tmp;
  let h = ST.get() in
  Seq.lemma_eq_intro (as_seq h output) (shift_spec (as_seq h0 output))


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

[@"c_inline"]
val sum_scalar_multiplication_:
  output:felem_wide ->
  input:felem{disjoint output input} ->
  s:limb ->
  Stack unit
    (requires (fun h -> live h output /\ live h input /\ sum_scalar_multiplication_pre_ (as_seq h output) (as_seq h input) s (len)))
    (ensures (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1 /\ live h0 input /\ live h0 output
      /\ sum_scalar_multiplication_pre_ (as_seq h0 output) (as_seq h0 input) s (len)
      /\ (as_seq h1 output) == sum_scalar_multiplication_spec (as_seq h0 output) (as_seq h0 input) s))
[@"c_inline"]
let sum_scalar_multiplication_ output input s =
  C.Compat.Loops.in_place_map2 output input clen (fun x y -> Hacl.Bignum.Wide.(x +%^ (y *^ s)))


#reset-options "--z3rlimit 100 --initial_fuel 1 --max_fuel 1"

val lemma_carry_wide_spec_0: s:seqelem_wide{carry_wide_pre s 0} -> Lemma
  (carry_wide_spec_ s 0 0 == s)
let lemma_carry_wide_spec_0 s = ()

val lemma_carry_wide_spec_1: s:seqelem_wide -> i:nat{i < len - 1 /\ carry_wide_pre s i} -> Lemma
  (carry_wide_spec_ s i (len-1) == (let s'' = carry_wide_step' s i in
                                    carry_wide_spec_ s'' (i+1) (len-1)))
let lemma_carry_wide_spec_1 s i = ()


#reset-options "--z3rlimit 500 --max_fuel 0 --max_ifuel 0"

[@"c_inline"]
val carry_wide_:
  t:felem_wide ->
  Stack unit
    (requires (fun h -> live h t /\ carry_wide_pre (as_seq h t) 0))
    (ensures (fun h0 _ h1 -> live h0 t /\ live h1 t /\ modifies_1 t h0 h1
      /\ carry_wide_pre (as_seq h0 t) 0
      /\ as_seq h1 t == carry_wide_spec (as_seq h0 t)))
[@"c_inline"]
let carry_wide_ tmp =
  let h0 = ST.get() in
  let inv (h1: HyperStack.mem) (j: nat): Type0 =
    live h1 tmp /\ modifies_1 tmp h0 h1 /\ 0 <= j /\ j <= len - 1
    /\ as_seq h1 tmp == carry_wide_spec_ (as_seq h0 tmp) 0 j
  in
  let f' (i:UInt32.t{FStar.UInt32.( 0 <= v i /\ v i < len - 1) }): Stack unit
    (requires (fun h -> inv h (UInt32.v i)))
    (ensures (fun h_1 _ h_2 -> FStar.UInt32.(inv h_2 (v i + 1))))
  = let h = ST.get() in
    let ctr = i in
    let tctr = tmp.(ctr) in
    let tctrp1 = tmp.(U32.(ctr+^1ul)) in
    assert_norm(pow2 0 = 1);
    Math.Lemmas.pow2_lt_compat limb_size 0;
    Math.Lemmas.pow2_lt_compat limb_n limb_size;
    Math.Lemmas.modulo_lemma (pow2 limb_size) (pow2 limb_n);
    let r0 = wide_to_limb (tctr) &^ climb_mask in
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
    lemma_carry_wide_spec_ 0 (UInt32.v i + 1) (as_seq h0 tmp)
  in
  lemma_carry_wide_spec_0 (as_seq h0 tmp);
  C.Compat.Loops.for 0ul FStar.UInt32.(clen -^ 1ul) inv f'


#reset-options "--z3rlimit 100 --initial_fuel 1 --max_fuel 1"

val lemma_carry_limb_spec_0: s:seqelem{carry_limb_pre s 0} -> Lemma (carry_limb_spec_ s 0 0 == s)
let lemma_carry_limb_spec_0 s = ()

#reset-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0"

[@"c_inline"]
val carry_limb_:
  t:felem ->
  Stack unit
    (requires (fun h -> live h t /\ carry_limb_pre (as_seq h t) 0))
    (ensures (fun h0 _ h1 -> live h0 t /\ live h1 t /\ modifies_1 t h0 h1
      /\ carry_limb_pre (as_seq h0 t) 0
      /\ as_seq h1 t == carry_limb_spec (as_seq h0 t)))
[@"c_inline"]
let carry_limb_ tmp =
  let h0 = ST.get() in
  let inv (h1: HyperStack.mem) (j: nat): Type0 =
    live h1 tmp /\ modifies_1 tmp h0 h1 /\ 0 <= j /\ j <= len - 1
    /\ as_seq h1 tmp == carry_limb_spec_ (as_seq h0 tmp) 0 j
  in
  let f' (i:UInt32.t{FStar.UInt32.( 0 <= v i /\ v i < len - 1) }): Stack unit
    (requires (fun h -> inv h (UInt32.v i)))
    (ensures (fun h_1 _ h_2 -> FStar.UInt32.(inv h_2 (v i + 1))))
  = let h = ST.get() in
    let ctr = i in
    let tctr = tmp.(ctr) in
    let tctrp1 = tmp.(U32.(ctr+^1ul)) in
    assert_norm(pow2 0 = 1);
    Math.Lemmas.pow2_lt_compat limb_size 0;
    Math.Lemmas.pow2_lt_compat limb_n limb_size;
    Math.Lemmas.modulo_lemma (pow2 limb_size) (pow2 limb_n);
    let r0 = (tctr) &^ climb_mask in
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
    lemma_carry_limb_spec_ 0 (UInt32.v i + 1) (as_seq h0 tmp)
  in
  lemma_carry_limb_spec_0 (as_seq h0 tmp);
  C.Compat.Loops.for 0ul FStar.UInt32.(clen -^ 1ul) inv f'


#set-options "--z3rlimit 20"

[@"substitute"]
val carry_0_to_1:
  output:felem ->
  Stack unit
    (requires (fun h -> live h output /\ carry_0_to_1_pre (as_seq h output)))
    (ensures (fun h0 _ h1 -> live h0 output /\ live h1 output /\ modifies_1 output h0 h1
      /\ carry_0_to_1_pre (as_seq h0 output)
      /\ as_seq h1 output == carry_0_to_1_spec (as_seq h0 output)))
[@"substitute"]
let carry_0_to_1 output =
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
  let i0' = i0 &^ climb_mask in
  cut (v i1 < pow2 (limb_size));
  let i1'   = i1 +^ (i0 >>^ climb_size) in
  output.(0ul) <- i0';
  output.(1ul) <- i1'

