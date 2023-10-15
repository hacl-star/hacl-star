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
  create (normalize_term c.bn_limbs) (u64 0)


let create_widefelem {| c:S.curve_params |} =
  BD.bn_eval_zeroes #U64 (2 * v c.bn_limbs) (2 * v c.bn_limbs);
  create (2ul *. (normalize_term c.bn_limbs)) (u64 0)


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
  if (normalize_term c.bn_limbs) = 4ul then 
    bn_make_u64_4 f (u64 0) (u64 0) (u64 0) (u64 0)
  else (
    Hacl.Bignum.Convert.bn_from_uint (normalize_term c.bn_limbs) (u64 0) f;
    Hacl.Spec.Bignum.Convert.bn_from_uint_lemma (v c.bn_limbs) (u64 0)
  )

let bn_set_one {| c:S.curve_params |} f =
  if (normalize_term c.bn_limbs) = 4ul then 
    bn_make_u64_4 f (u64 1) (u64 0) (u64 0) (u64 0)
  else (
    Hacl.Bignum.Convert.bn_from_uint (normalize_term c.bn_limbs) (u64 1) f;
    Hacl.Spec.Bignum.Convert.bn_from_uint_lemma (v c.bn_limbs) (u64 1)
  )

///  Comparison

let bn_is_eq_mask_g {| c:S.curve_params |} a b =
  let h0 = ST.get () in
  SN.bn_eq_mask_lemma (as_seq h0 a) (as_seq h0 b);
  BN.bn_eq_mask #U64 (normalize_term c.bn_limbs) a b



///  Conditional copy

let bn_cmovznz_g {| c:S.curve_params |} res cin x y =
  let mask = neq_mask cin (u64 0) in
  Lib.ByteBuffer.buf_mask_select y x mask res


///  Addition and subtraction

let bn_add_mod_g {| c:S.curve_params |} res n x y =
  let h0 = ST.get () in
  SN.bn_add_mod_n_lemma (as_seq h0 n) (as_seq h0 x) (as_seq h0 y);
  BN.bn_add_mod_n (normalize_term c.bn_limbs) n x y res

let bn_sub_g {| cp:S.curve_params |} res x y =
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

let bn_sub_mod_g {| c:S.curve_params |} res n x y =
  let h0 = ST.get () in
  SN.bn_sub_mod_n_lemma (as_seq h0 n) (as_seq h0 x) (as_seq h0 y);
  BN.bn_sub_mod_n (normalize_term c.bn_limbs) n x y res


///  Multiplication


let bn_mul_g {| c:S.curve_params |} res x y =
  let h0 = ST.get () in
  SN.bn_mul_lemma (as_seq h0 x) (as_seq h0 y);
  BN.bn_mul #U64 (normalize_term c.bn_limbs) (normalize_term c.bn_limbs) x y res

let bn_sqr_g {| c:S.curve_params |} res x =
  let h0 = ST.get () in
  SN.bn_sqr_lemma (as_seq h0 x);
  BN.bn_sqr #U64 (normalize_term c.bn_limbs) x res


///  Conversion between bignum and bytes representation

let bn_to_bytes_be_g {| c:S.curve_params |} res f =
  let h0 = ST.get () in
  Hacl.Spec.Bignum.Convert.bn_to_bytes_be_lemma #U64 c.bytes (as_seq h0 f);
  Hacl.Bignum.Convert.mk_bn_to_bytes_be true (normalize_term c.size_bytes) f res


let bn_from_bytes_be_g {| c:S.curve_params |} res b =
  let h0 = ST.get () in
  Hacl.Spec.Bignum.Convert.bn_from_bytes_be_lemma #U64 c.bytes (as_seq h0 b);
  Hacl.Bignum.Convert.mk_bn_from_bytes_be true (normalize_term c.size_bytes) b res


inline_for_extraction noextract
instance bn_inst {| cp:S.curve_params |} : BN.bn U64 = {
  BN.len = cp.bn_limbs;
  BN.add = BN.bn_add_eq_len cp.bn_limbs;
  BN.sub = BN.bn_sub_eq_len cp.bn_limbs;
  BN.add_mod_n = BN.bn_add_mod_n cp.bn_limbs;
  BN.sub_mod_n = BN.bn_sub_mod_n cp.bn_limbs;
  BN.mul = BN.bn_mul cp.bn_limbs cp.bn_limbs ;
  BN.sqr = BN.bn_sqr cp.bn_limbs
}


let bn_mont_reduction_g {| cp:S.curve_params |} mont_mu res x n =
  BM.bn_mont_reduction bn_inst n mont_mu x res

///---

let bn_is_zero_mask {| c:S.curve_params |} {| bn_ops |} f =
  push_frame ();
  let bn_zero = create_felem #c in
  let res = bn_is_eq_mask f bn_zero in
  pop_frame ();
  res

let bn_is_zero_vartime {| c:S.curve_params |} {| bn_ops |} f =
  let m = bn_is_zero_mask f in
  unsafe_bool_of_limb m


let bn_is_eq_vartime {| c:S.curve_params |}  {| bn_ops |} a b =
  let m = bn_is_eq_mask a b in
  unsafe_bool_of_limb m


let bn_is_odd {| c:S.curve_params |} {| bn_ops |} f =
  let h0 = ST.get () in
  SN.bn_is_odd_lemma (as_seq h0 f);
  BN.bn_is_odd (normalize_term c.bn_limbs) f


let bn2_to_bytes_be {| c:S.curve_params |} {| bn_ops |} res x y =
  let h0 = ST.get () in
  update_sub_f h0 res 0ul (normalize_term c.size_bytes)
    (fun h -> BSeq.nat_to_bytes_be c.bytes (as_nat h0 x))
    (fun _ -> bn_to_bytes_be (sub res 0ul (normalize_term c.size_bytes)) x);

  let h1 = ST.get () in
  update_sub_f h1 res (normalize_term c.size_bytes) (normalize_term c.size_bytes)
    (fun h -> BSeq.nat_to_bytes_be c.bytes (as_nat h1 y))
    (fun _ -> bn_to_bytes_be (sub res (normalize_term c.size_bytes) (normalize_term c.size_bytes)) y);

  let h2 = ST.get () in
  let x = Ghost.hide (BSeq.nat_to_bytes_be c.bytes (as_nat h0 x)) in
  let y = Ghost.hide (BSeq.nat_to_bytes_be c.bytes (as_nat h0 y)) in
  LSeq.eq_intro (as_seq h2 res) (LSeq.concat #_ #c.bytes #c.bytes x y)


