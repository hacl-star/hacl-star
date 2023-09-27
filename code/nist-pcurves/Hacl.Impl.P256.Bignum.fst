module Hacl.Impl.P256.Bignum

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

module BN = Hacl.Bignum
module SN = Hacl.Spec.Bignum
module BD = Hacl.Spec.Bignum.Definitions
module LSeq = Lib.Sequence

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let bn_v_is_as_nat a =
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

let create_felem () =
  BD.bn_eval_zeroes #U64 4 4;
  create 4ul (u64 0)


let create_widefelem () =
  BD.bn_eval_zeroes #U64 8 8;
  create 8ul (u64 0)


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
  bn_v_is_as_nat (as_seq h0 res)


///  Create zero and one

let bn_set_zero4 f =
  bn_make_u64_4 f (u64 0) (u64 0) (u64 0) (u64 0)


let bn_set_one4 f =
  bn_make_u64_4 f (u64 1) (u64 0) (u64 0) (u64 0)


///  Comparison

[@CInline]
let bn_is_zero_mask4 f =
  let h0 = ST.get () in
  SN.bn_is_zero_mask_lemma (as_seq h0 f);
  bn_v_is_as_nat (as_seq h0 f);
  BN.bn_is_zero_mask #U64 4ul f


[@CInline]
let bn_is_zero_vartime4 f =
  let m = bn_is_zero_mask4 f in
  Hacl.Bignum.Base.unsafe_bool_of_limb m


[@CInline]
let bn_is_eq_mask4 a b =
  let h0 = ST.get () in
  SN.bn_eq_mask_lemma (as_seq h0 a) (as_seq h0 b);
  bn_v_is_as_nat (as_seq h0 a);
  bn_v_is_as_nat (as_seq h0 b);
  BN.bn_eq_mask #U64 4ul a b


[@CInline]
let bn_is_eq_vartime4 a b =
  let m = bn_is_eq_mask4 a b in
  Hacl.Bignum.Base.unsafe_bool_of_limb m


let bn_is_odd4 f =
  let h0 = ST.get () in
  bn_v_is_as_nat (as_seq h0 f);
  SN.bn_is_odd_lemma (as_seq h0 f);
  BN.bn_is_odd 4ul f


///  Conditional copy

[@CInline]
let bn_cmovznz4 res cin x y =
  let mask = neq_mask cin (u64 0) in
  Lib.ByteBuffer.buf_mask_select y x mask res


///  Addition and subtraction

[@CInline]
let bn_add_mod4 res n x y =
  let h0 = ST.get () in
  SN.bn_add_mod_n_lemma (as_seq h0 n) (as_seq h0 x) (as_seq h0 y);
  BN.bn_add_mod_n 4ul n x y res


[@CInline]
let bn_sub4 res x y =
  let h0 = ST.get () in
  SN.bn_sub_lemma (as_seq h0 x) (as_seq h0 y);
  let c = BN.bn_sub_eq_len 4ul x y res in
  let h1 = ST.get () in
  assert (as_nat h1 res - v c * pow2 256 = as_nat h0 x - as_nat h0 y);
  BD.bn_eval_bound (as_seq h1 res) 4;
  BD.bn_eval_bound (as_seq h0 x) 4;
  BD.bn_eval_bound (as_seq h0 y) 4;
  assert (if v c = 0 then as_nat h0 x >= as_nat h0 y else as_nat h0 x < as_nat h0 y);
  c


[@CInline]
let bn_sub_mod4 res n x y =
  let h0 = ST.get () in
  SN.bn_sub_mod_n_lemma (as_seq h0 n) (as_seq h0 x) (as_seq h0 y);
  BN.bn_sub_mod_n 4ul n x y res


///  Multiplication

[@CInline]
let bn_mul4 res x y =
  let h0 = ST.get () in
  SN.bn_mul_lemma (as_seq h0 x) (as_seq h0 y);
  BN.bn_mul #U64 4ul 4ul x y res


[@CInline]
let bn_sqr4 res x =
  let h0 = ST.get () in
  SN.bn_sqr_lemma (as_seq h0 x);
  BN.bn_sqr #U64 4ul x res


///  Conversion between bignum and bytes representation

[@CInline]
let bn_to_bytes_be4 res f =
  let h0 = ST.get () in
  Hacl.Spec.Bignum.Convert.bn_to_bytes_be_lemma #U64 32 (as_seq h0 f);
  Hacl.Bignum.Convert.mk_bn_to_bytes_be true 32ul f res


[@CInline]
let bn_from_bytes_be4 res b =
  let h0 = ST.get () in
  Hacl.Spec.Bignum.Convert.bn_from_bytes_be_lemma #U64 32 (as_seq h0 b);
  Hacl.Bignum.Convert.mk_bn_from_bytes_be true 32ul b res


[@CInline]
let bn2_to_bytes_be4 res x y =
  let h0 = ST.get () in
  update_sub_f h0 res 0ul 32ul
    (fun h -> BSeq.nat_to_bytes_be 32 (as_nat h0 x))
    (fun _ -> bn_to_bytes_be4 (sub res 0ul 32ul) x);

  let h1 = ST.get () in
  update_sub_f h1 res 32ul 32ul
    (fun h -> BSeq.nat_to_bytes_be 32 (as_nat h1 y))
    (fun _ -> bn_to_bytes_be4 (sub res 32ul 32ul) y);

  let h2 = ST.get () in
  let x = Ghost.hide (BSeq.nat_to_bytes_be 32 (as_nat h0 x)) in
  let y = Ghost.hide (BSeq.nat_to_bytes_be 32 (as_nat h0 y)) in
  LSeq.eq_intro (as_seq h2 res) (LSeq.concat #_ #32 #32 x y)
