module Hacl.EC.Curve25519_donna_c64.Fscalar


open FStar.Mul
open FStar.HyperStack
open FStar.Buffer
open FStar.Int.Cast
open Hacl.UInt64
open Hacl.Cast

open Hacl.EC.Curve25519_donna_c64.Bigint


module U8 = FStar.UInt8
module U32 = FStar.UInt32

module H8 = Hacl.UInt8
module H64 = Hacl.UInt64
module H128 = Hacl.UInt128


inline_for_extraction let zero_8 = uint8_to_sint8 0uy
inline_for_extraction let zero_64 = uint64_to_sint64 0uL
inline_for_extraction let one_8 = uint8_to_sint8 1uy
inline_for_extraction let one_64 = uint64_to_sint64 1uL


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 5"

private inline_for_extraction let trim_128_to_51 (a:H128.t) : Tot (b:H64.t{v b = H128.v a % pow2 51})
  = let mask_51 = uint64_to_sint64 0x7ffffffffffffuL in
    assert_norm(v mask_51 = pow2 51 - 1);
    let res = sint128_to_sint64 a &^ mask_51 in
    UInt.logand_mask #64 ((H128.v a) % (pow2 64)) 51;
    Math.Lemmas.pow2_plus 51 13;
    Math.Lemmas.modulo_modulo_lemma (H128.v a) (pow2 51) (pow2 13);
    res


val lemma_div_pow2_lt: x:nat -> n:nat -> m:nat{m <= n} -> Lemma
  (requires (x < pow2 n))
  (ensures  (x / pow2 m < pow2 (n - m)))
let lemma_div_pow2_lt x n m =
  Math.Lemmas.lemma_div_mod x (pow2 m);
  Math.Lemmas.pow2_plus (m) (n-m)


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

private inline_for_extraction val mul_and_add_carry:
  a:H128.t -> input:H64.t{v input < pow2 52} -> scalar:H64.t{v scalar < pow2 44} ->
  Tot (a':H128.t{H128.v a' = (v input * v scalar) + (H128.v a / pow2 51) /\ H128.v a' < pow2 97})
private inline_for_extraction let mul_and_add_carry a input scalar =
  Math.Lemmas.pow2_plus 52 44;
  lemma_div_pow2_lt (H128.v a) (128) (51);
  Math.Lemmas.pow2_lt_compat 96 77;
  Math.Lemmas.pow2_double_sum 96;
  Math.Lemmas.pow2_lt_compat 128 97;
  let open Hacl.UInt128 in
  cut (v (input *^ scalar) = H64.v input * H64.v scalar);
  cut (v (input *^ scalar) < pow2 96);
  cut (v (a >>^ 51ul) < pow2 77);
  cut (v (a >>^ 51ul) < pow2 96);
  H128.((input *^ scalar) +^ (a >>^ 51ul))


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"


private let geval_5 (o0:nat) (o1:nat) (o2:nat) (o3:nat) (o4:nat) =
  o0 + pow2 51 * o1 + pow2 102 * o2 + pow2 153 * o3 + pow2 204 * o4


private let fscalar_product_lemma_11 (a:nat) (b:nat) (n:nat) (m:nat) : Lemma
  (pow2 n * (a % pow2 m) + pow2 (n+m) * (b + a / pow2 m) = pow2 n * a + pow2 (n+m) * b)
  = Math.Lemmas.pow2_plus n m;
    Math.Lemmas.distributivity_add_right (pow2 (n + m)) b (a/pow2 m);
    Math.Lemmas.lemma_div_mod a (pow2 m);
    Math.Lemmas.distributivity_add_right (pow2 n) (pow2 m * (a / pow2 m)) (a % pow2 m)


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

private val fscalar_product_lemma_1:
  i0:nat -> i1:nat -> i2:nat -> i3:nat -> i4:nat ->
  o0:nat -> o1:nat -> o2:nat -> o3:nat -> o4:nat ->
  s:nat ->
  Lemma (requires (let p = pow2 51 in
    o0 = ((i0 * s) % (p))
    /\ o1 = ((i1 * s) + ((i0 * s) / p)) % p
    /\ o2 = ((i2 * s) + (((i1 * s) + ((i0 * s) / p)) / p)) % p
    /\ o3 = ((i3 * s) + (((i2 * s) + (((i1 * s) + ((i0 * s) / p)) / p))/p)) % p
    /\ o4 = ((i4 * s) + (((i3 * s) + (((i2 * s) + (((i1 * s) + ((i0 * s) / p)) / p))/p)) / p)) ))
    (ensures (geval_5 o0 o1 o2 o3 o4 = geval_5 i0 i1 i2 i3 i4 * s))
let fscalar_product_lemma_1 i0 i1 i2 i3 i4 o0 o1 o2 o3 o4 s =
  assert_norm(pow2 0 = 1);
  let p = pow2 51 in
  let v0 = i0 * s in
  let v1 = (i1 * s) + ((i0 * s) / p) in
  let v2 = (i2 * s) + (((i1 * s) + ((i0 * s) / p)) / p) in
  let v3 = (i3 * s) + (((i2 * s) + (((i1 * s) + ((i0 * s) / p)) / p))/p) in
  let v4 = (i4 * s) + (((i3 * s) + (((i2 * s) + (((i1 * s) + ((i0 * s) / p)) / p))/p)) / p) in
  fscalar_product_lemma_11 v3 (i4 * s) 153 51;
  fscalar_product_lemma_11 v2 (i3 * s) 102 51;
  fscalar_product_lemma_11 v1 (i2 * s) 51 51;
  fscalar_product_lemma_11 v0 (i1 * s) 0 51


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"


private val fscalar_product_lemma_2:
  o0:nat -> o1:nat -> o2:nat -> o3:nat -> o4:nat{o4 < pow2 64} -> o0':nat -> o4':nat ->
  Lemma (requires (o4' = o4 % pow2 51 /\ o0' = o0 + 19 * (o4 / pow2 51)))
        (ensures (geval_5 o0 o1 o2 o3 o4 % (pow2 255 - 19) = geval_5 o0' o1 o2 o3 o4' % (pow2 255 - 19)))
let fscalar_product_lemma_2 o0 o1 o2 o3 o4 o0' o4' =
  Math.Lemmas.lemma_div_mod o4 (pow2 51);
  cut (geval_5 o0 o1 o2 o3 o4 = o0 + pow2 51 * o1 + pow2 102 * o2 + pow2 153 * o3
    + pow2 204 * (pow2 51 * (o4 / pow2 51) + (o4 % pow2 51)));
  Math.Lemmas.pow2_plus 204 51;
  Math.Lemmas.distributivity_add_right (pow2 204) (pow2 51 * (o4 / pow2 51)) (o4 % pow2 51);
  Math.Lemmas.lemma_mod_plus_distr_l (pow2 255 * (o4 / pow2 51)) (o0 + pow2 51 * o1 + pow2 102 * o2 + pow2 153 * o3
    + pow2 204 * (o4 % pow2 51)) (pow2 255 - 19);
  Math.Lemmas.lemma_mod_mul_distr_l (pow2 255) (o4 / pow2 51) (pow2 255 - 19);
  lemma_div_pow2_lt (o4) 64 51;
  assert_norm(pow2 13 = 8192);
  Math.Lemmas.modulo_lemma (19 * (o4 / pow2 51)) (pow2 255 - 19)


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 200"


val fscalar_product:
  output:felem -> input:felem ->
  scalar:limb{v scalar < pow2 44} ->
  Stack unit
  (requires (fun h -> live h output /\ bound h input 52))
  (ensures (fun h0 _ h1 -> bound h0 input 52 /\ bound h1 output 52 /\ modifies_1 output h0 h1
    /\ eval h1 output % (pow2 255 - 19) = (eval h0 input * v scalar) % (pow2 255 - 19)))
let fscalar_product output input scalar =
  let input0 = input.(0ul) in let input1 = input.(1ul) in
  let input2 = input.(2ul) in let input3 = input.(3ul) in
  let input4 = input.(4ul) in let output0 = output.(0ul) in
  let output1 = output.(1ul) in let output2 = output.(2ul) in
  let output3 = output.(3ul) in let output4 = output.(4ul) in
  let a = H128.(input0 *^ scalar) in
  (* let output0 = sint128_to_sint64 a &^ mask_51 in *)
  let output0 = trim_128_to_51 a in
  cut (v output0 = (v input0 * v scalar) % pow2 51);
  (* let a = H128.((input1 *^ scalar) +^ (a >>^ 51ul)) in *)
  let a1 = mul_and_add_carry a input1 scalar in
  cut (H128.v a1 = v input1 * v scalar + H128.v a / pow2 51);
  (* let output1 = sint128_to_sint64 a &^ mask_51 in *)
  let output1 = trim_128_to_51 a1 in
  (* let a = H128.((input2 *^ scalar) +^ (a >>^ 51ul)) in *)
  let a2 = mul_and_add_carry a1 input2 scalar in
  cut (H128.v a1 = v input1 * v scalar + H128.v a / pow2 51);
  (* let output2 = sint128_to_sint64 a &^ mask_51 in *)
  let output2 = trim_128_to_51 a2 in
  (* let a = H128.((input3 *^ scalar) +^ (a >>^ 51ul)) in *)
  let a3 = mul_and_add_carry a2 input3 scalar in
  (* let output3 = sint128_to_sint64 a &^ mask_51 in *)
  let output3 = trim_128_to_51 a3 in
  (* let a = H128.((input4 *^ scalar) +^ (a >>^ 51ul)) in *)
  let a4 = mul_and_add_carry a3 input4 scalar in
  (* let output4 = sint128_to_sint64 a &^ mask_51 in *)
  let output4 = trim_128_to_51 a4 in
  fscalar_product_lemma_1 (v input0) (v input1) (v input2) (v input3) (v input4)
                         (v output0) (v output1) (v output2) (v output3) (H128.v a4) (v scalar);
  lemma_div_pow2_lt (H128.v a4) 97 51; Math.Lemmas.pow2_lt_compat 64 46;
  assert_norm (pow2 5 = 32); Math.Lemmas.pow2_plus 46 5;
  cut (v (sint128_to_sint64 (H128.(sint128_to_sint64 (a4 >>^ 51ul) *^ uint64_to_sint64 19uL))) < pow2 51);
  Math.Lemmas.pow2_double_sum 51;
  Math.Lemmas.modulo_lemma (H128.v a4) (pow2 64);
  let output0 = output0 +^ sint128_to_sint64 (H128.(sint128_to_sint64 (a4 >>^ 51ul) *^ uint64_to_sint64 19uL)) in
  fscalar_product_lemma_2 (v output0) (v output1) (v output2) (v output3) (H128.v a4) (v output0) (v output4);
  output.(0ul) <- output0;
  output.(1ul) <- output1;
  output.(2ul) <- output2;
  output.(3ul) <- output3;
  output.(4ul) <- output4
