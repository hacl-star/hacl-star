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


#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 5"


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


#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 20"

private inline_for_extraction val mul_and_add_carry:
  a:H128.t -> input:H64.t{v input < pow2 52} -> scalar:H64.t{v scalar < pow2 51} ->
  Tot (a':H128.t{H128.v a' = (v input * v scalar) + (H128.v a / pow2 51) /\ H128.v a' < pow2 104})
private inline_for_extraction let mul_and_add_carry a input scalar =
  Math.Lemmas.pow2_plus 52 51;
  lemma_div_pow2_lt (H128.v a) (128) (51);
  Math.Lemmas.pow2_lt_compat 103 77;
  Math.Lemmas.pow2_double_sum 103;
  Math.Lemmas.pow2_lt_compat 128 104;
  let open Hacl.UInt128 in
  cut (v (input *^ scalar) = H64.v input * H64.v scalar);
  cut (v (input *^ scalar) < pow2 103);
  cut (v (a >>^ 51ul) < pow2 77);
  cut (v (a >>^ 51ul) < pow2 103);
  H128 ((input *^ scalar) +^ (a >>^ 51ul))


val fscalar_product:
  output:felem -> input:felem ->
  scalar:limb{v scalar < pow2 51} ->
  Stack unit
  (requires (fun h -> live h output /\ bound h input 52))
  (ensures (fun h0 _ h1 -> bound h0 input 52 /\ bound h1 output 52 /\ modifies_1 output h0 h1
    /\ eval h1 output % (pow2 255 - 19) = eval h0 input * v scalar))
let fscalar_product output input scalar =
  let input0 = input.(0ul) in let input1 = input.(1ul) in
  let input2 = input.(2ul) in let input3 = input.(3ul) in
  let input4 = input.(4ul) in let output0 = output.(0ul) in
  let output1 = output.(1ul) in let output2 = output.(2ul) in
  let output3 = output.(3ul) in let output4 = output.(4ul) in
  let a = H128 (input0 *^ scalar) in
  (* let output0 = sint128_to_sint64 a &^ mask_51 in *)
  let output0 = trim_128_to_51 a in
  cut (v output0 = (v input0 * v scalar) % pow2 51);
  (* let a = H128 ((input1 *^ scalar) +^ (a >>^ 51ul)) in *)
  let a = mul_and_add_carry a input1 scalar in
  (* let output1 = sint128_to_sint64 a &^ mask_51 in *)
  let output1 = trim_128_to_51 a in
  (* let a = H128 ((input2 *^ scalar) +^ (a >>^ 51ul)) in *)
  let a = mul_and_add_carry a input2 scalar in
  (* let output2 = sint128_to_sint64 a &^ mask_51 in *)
  let output2 = trim_128_to_51 a in
  (* let a = H128 ((input3 *^ scalar) +^ (a >>^ 51ul)) in *)
  let a = mul_and_add_carry a input3 scalar in
  (* let output3 = sint128_to_sint64 a &^ mask_51 in *)
  let output3 = trim_128_to_51 a in
  (* let a = H128 ((input4 *^ scalar) +^ (a >>^ 51ul)) in *)
  let a = mul_and_add_carry a input4 scalar in
  (* let output4 = sint128_to_sint64 a &^ mask_51 in *)
  let output4 = trim_128_to_51 a in
  let output0 = output0 +^ sint128_to_sint64 (H128 (sint128_to_sint64 (a >>^ 51ul) *^ uint64_to_sint64 19uL)) in
  output.(0ul) <- output0;
  output.(1ul) <- output1;
  output.(2ul) <- output2;
  output.(3ul) <- output3;
  output.(4ul) <- output4
