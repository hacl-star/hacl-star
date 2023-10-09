module Hacl.Impl.PCurves.Bignum

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

module BN = Hacl.Bignum
module SN = Hacl.Spec.Bignum
module BD = Hacl.Spec.Bignum.Definitions
module BC = Hacl.Bignum.Convert
module LSeq = Lib.Sequence

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let bn_v_is_as_nat4 a =
  let open Lib.Sequence in
  let open Hacl.Spec.Bignum.Definitions in
  assert_norm (pow2 64 * pow2 64 = pow2 128);
  assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 192);

  calc (==) {
    bn_v a;
  (==) { bn_eval1 (slice a 0 1); bn_eval_split_i #U64 a 1 }
    v a.[0] + pow2 64 * bn_v (slice a 1 4);
  (==) { bn_eval_split_i #U64 (slice a 1 4) 1; bn_eval1 (slice a 1 2) }
    v a.[0] + pow2 64 * v a.[1] + pow2 64 * pow2 64 * bn_v (slice a 2 4);
  (==) { bn_eval_split_i #U64 (slice a 2 4) 1; bn_eval1 (slice a 2 3) }
    v a.[0] + pow2 64 * v a.[1] + pow2 64 * pow2 64 * v a.[2]
    + pow2 64 * pow2 64 * pow2 64 * bn_v (slice a 3 4);
  (==) { bn_eval1 (slice a 3 4) }
    v a.[0] + pow2 64 * v a.[1] + pow2 64 * pow2 64 * v a.[2]
    + pow2 64 * pow2 64 * pow2 64 * v a.[3];
  }


///  Create a bignum

let create_felem {| c:S.curve_params |} =
  BD.bn_eval_zeroes #U64 (v c.bn_limbs) (v c.bn_limbs);
  create c.bn_limbs (u64 0)


let create_widefelem {| c:S.curve_params |} =
  BD.bn_eval_zeroes #U64 (2 * v c.bn_limbs) (2 * v c.bn_limbs);
  create (2ul *. c.bn_limbs) (u64 0)


let bn_make_u64_4 res a0 a1 a2 a3 =
  let h0 = ST.get () in
  upd res 0ul a0;
  let h1 = ST.get () in
  upd res 1ul a1;
  let h2 = ST.get () in
  upd res 2ul a2;
  let h3 = ST.get () in
  upd res 3ul a3;
  let h4 = ST.get () in
  BD.bn_upd_eval (as_seq h0 res) a0 0;
  BD.bn_upd_eval (as_seq h1 res) a1 1;
  BD.bn_upd_eval (as_seq h2 res) a2 2;
  BD.bn_upd_eval (as_seq h3 res) a3 3;
  bn_v_is_as_nat4 (as_seq h0 res)


///  Create zero and one

let bn_set_zero {| c:S.curve_params |} f =
  if c.bn_limbs = 4ul then 
    bn_make_u64_4 f (u64 0) (u64 0) (u64 0) (u64 0)
  else (
    Hacl.Bignum.Convert.bn_from_uint c.bn_limbs (u64 0) f;
    Hacl.Spec.Bignum.Convert.bn_from_uint_lemma (v c.bn_limbs) (u64 0)
  )

let bn_set_one {| c:S.curve_params |} f =
  if c.bn_limbs = 4ul then 
    bn_make_u64_4 f (u64 1) (u64 0) (u64 0) (u64 0)
  else (
    Hacl.Bignum.Convert.bn_from_uint c.bn_limbs (u64 1) f;
    Hacl.Spec.Bignum.Convert.bn_from_uint_lemma (v c.bn_limbs) (u64 1)
  )

///  Comparison

[@CInline]
let bn_is_zero_mask {| c:S.curve_params |} f =
  let h0 = ST.get () in
  SN.bn_is_zero_mask_lemma (as_seq h0 f);
  BN.bn_is_zero_mask #U64 c.bn_limbs f


[@CInline]
let bn_is_zero_vartime {| c:S.curve_params |} f =
  let m = bn_is_zero_mask f in
  Hacl.Bignum.Base.unsafe_bool_of_limb m


[@CInline]
let bn_is_eq_mask {| c:S.curve_params |} a b =
  let h0 = ST.get () in
  SN.bn_eq_mask_lemma (as_seq h0 a) (as_seq h0 b);
  BN.bn_eq_mask #U64 c.bn_limbs a b


[@CInline]
let bn_is_eq_vartime {| c:S.curve_params |}  a b =
  let m = bn_is_eq_mask a b in
  Hacl.Bignum.Base.unsafe_bool_of_limb m


let bn_is_odd {| c:S.curve_params |} f =
  let h0 = ST.get () in
  SN.bn_is_odd_lemma (as_seq h0 f);
  BN.bn_is_odd c.bn_limbs f


///  Conditional copy

[@CInline]
let bn_cmovznz {| c:S.curve_params |} res cin x y =
  let mask = neq_mask cin (u64 0) in
  Lib.ByteBuffer.buf_mask_select y x mask res


///  Addition and subtraction

[@CInline]
let bn_add_mod {| c:S.curve_params |} res n x y =
  let h0 = ST.get () in
  SN.bn_add_mod_n_lemma (as_seq h0 n) (as_seq h0 x) (as_seq h0 y);
  BN.bn_add_mod_n c.bn_limbs n x y res

[@CInline]
let bn_sub {| cp:S.curve_params |} res x y =
  let h0 = ST.get () in
  let c = BN.bn_sub_eq_len cp.bn_limbs x y res in
  let h1 = ST.get () in
  SN.bn_sub_lemma (as_seq h0 x) (as_seq h0 y);
  assert (as_nat h1 res - v c * pow2 (64 * v cp.bn_limbs) = as_nat h0 x - as_nat h0 y);
  BD.bn_eval_bound (as_seq h1 res) (v cp.bn_limbs);
  BD.bn_eval_bound (as_seq h0 x) (v cp.bn_limbs);
  BD.bn_eval_bound (as_seq h0 y) (v cp.bn_limbs);
  assert (if v c = 0 then as_nat h0 x >= as_nat h0 y else as_nat h0 x < as_nat h0 y);
  c


[@CInline]
let bn_sub_mod {| c:S.curve_params |} res n x y =
  let h0 = ST.get () in
  SN.bn_sub_mod_n_lemma (as_seq h0 n) (as_seq h0 x) (as_seq h0 y);
  BN.bn_sub_mod_n c.bn_limbs n x y res


///  Multiplication

[@CInline]
let bn_mul {| c:S.curve_params |} res x y =
  let h0 = ST.get () in
  SN.bn_mul_lemma (as_seq h0 x) (as_seq h0 y);
  BN.bn_mul #U64 c.bn_limbs c.bn_limbs x y res


[@CInline]
let bn_sqr {| c:S.curve_params |} res x =
  let h0 = ST.get () in
  SN.bn_sqr_lemma (as_seq h0 x);
  BN.bn_sqr #U64 c.bn_limbs x res


///  Conversion between bignum and bytes representation

[@CInline]
let bn_to_bytes_be {| c:S.curve_params |} res f =
  let h0 = ST.get () in
  Hacl.Spec.Bignum.Convert.bn_to_bytes_be_lemma #U64 c.bytes (as_seq h0 f);
  Hacl.Bignum.Convert.mk_bn_to_bytes_be true (size c.bytes) f res


[@CInline]
let bn_from_bytes_be {| c:S.curve_params |} res b =
  let h0 = ST.get () in
  Hacl.Spec.Bignum.Convert.bn_from_bytes_be_lemma #U64 c.bytes (as_seq h0 b);
  Hacl.Bignum.Convert.mk_bn_from_bytes_be true (size c.bytes) b res


[@CInline]
let bn2_to_bytes_be {| c:S.curve_params |} res x y =
  let h0 = ST.get () in
  update_sub_f h0 res 0ul (size c.bytes)
    (fun h -> BSeq.nat_to_bytes_be c.bytes (as_nat h0 x))
    (fun _ -> bn_to_bytes_be (sub res 0ul (size c.bytes)) x);

  let h1 = ST.get () in
  update_sub_f h1 res (size c.bytes) (size c.bytes)
    (fun h -> BSeq.nat_to_bytes_be c.bytes (as_nat h1 y))
    (fun _ -> bn_to_bytes_be (sub res (size c.bytes) (size c.bytes)) y);

  let h2 = ST.get () in
  let x = Ghost.hide (BSeq.nat_to_bytes_be c.bytes (as_nat h0 x)) in
  let y = Ghost.hide (BSeq.nat_to_bytes_be c.bytes (as_nat h0 y)) in
  LSeq.eq_intro (as_seq h2 res) (LSeq.concat #_ #c.bytes #c.bytes x y)

