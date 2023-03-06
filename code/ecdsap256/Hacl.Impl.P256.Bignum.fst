module Hacl.Impl.P256.Bignum

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.IntTypes.Intrinsics

open Hacl.Spec.P256.Felem
module BN = Hacl.Bignum
module SN = Hacl.Spec.Bignum

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

///  Create a bignum

let bn_make_u64_4 a0 a1 a2 a3 res =
  assert_norm (pow2 64 * pow2 64 = pow2 128);
  assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 192);
  upd res (size 0) a0;
  upd res (size 1) a1;
  upd res (size 2) a2;
  upd res (size 3) a3


///  Create zero and one

let bn_set_zero4 f =
  bn_make_u64_4 (u64 0) (u64 0) (u64 0) (u64 0) f


let bn_set_one4 f =
  bn_make_u64_4 (u64 1) (u64 0) (u64 0) (u64 0) f


///  Comparison

[@CInline]
let bn_is_zero_vartime4 f =
  let open Lib.RawIntTypes in
  let f0 = index f 0ul in
  let f1 = index f 1ul in
  let f2 = index f 2ul in
  let f3 = index f 3ul in
  u64_to_UInt64 f0 =. 0uL &&
  u64_to_UInt64 f1 =. 0uL &&
  u64_to_UInt64 f2 =. 0uL &&
  u64_to_UInt64 f3 =. 0uL


[@CInline]
let bn_is_zero_mask4 f =
  let h0 = ST.get () in
  SN.bn_is_zero_mask_lemma (as_seq h0 f);
  bignum_bn_v_is_as_nat h0 f;
  BN.bn_is_zero_mask #U64 4ul f


[@CInline]
let bn_is_eq_mask4 a b =
  let h0 = ST.get () in
  SN.bn_eq_mask_lemma (as_seq h0 a) (as_seq h0 b);
  bignum_bn_v_is_as_nat h0 a;
  bignum_bn_v_is_as_nat h0 b;
  BN.bn_eq_mask #U64 4ul a b


///  Conditional copy

[@CInline]
let bn_copy_conditional4 out x mask =
  Lib.ByteBuffer.buf_mask_select x out mask out


[@CInline]
let bn_cmovznz4 cin x y out =
  let mask = neq_mask cin (u64 0) in
  Lib.ByteBuffer.buf_mask_select y x mask out


///  Addition and subtraction

[@CInline]
let bn_add_mod4 x y n out =
  let h0 = ST.get () in
  BN.bn_add_mod_n 4ul n x y out;
  let h1 = ST.get () in
  bignum_bn_v_is_as_nat h0 n;
  bignum_bn_v_is_as_nat h0 x;
  bignum_bn_v_is_as_nat h0 y;
  SN.bn_add_mod_n_lemma (as_seq h0 n) (as_seq h0 x) (as_seq h0 y);
  bignum_bn_v_is_as_nat h1 out


[@CInline]
let bn_sub4 x y out =
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
  let h0 = ST.get () in
  let c = BN.bn_sub_eq_len 4ul x y out in
  let h1 = ST.get () in
  SN.bn_sub_lemma (as_seq h0 x) (as_seq h0 y);
  bignum_bn_v_is_as_nat h0 x;
  bignum_bn_v_is_as_nat h0 y;
  bignum_bn_v_is_as_nat h1 out;
  c


[@CInline]
let bn_sub4_il x y result =
  let r0 = sub result (size 0) (size 1) in
  let r1 = sub result (size 1) (size 1) in
  let r2 = sub result (size 2) (size 1) in
  let r3 = sub result (size 3) (size 1) in

  let cc = sub_borrow_u64 (u64 0) x.(size 0) y.(size 0) r0 in
  let cc = sub_borrow_u64 cc x.(size 1) y.(size 1) r1 in
  let cc = sub_borrow_u64 cc x.(size 2) y.(size 2) r2 in
  let cc = sub_borrow_u64 cc x.(size 3) y.(size 3) r3 in

  assert_norm (pow2 64 * pow2 64 = pow2 128);
  assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 192);
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);

  cc


[@CInline]
let bn_sub_mod4 x y n out =
  let h0 = ST.get () in
  BN.bn_sub_mod_n 4ul n x y out;
  let h1 = ST.get () in
  bignum_bn_v_is_as_nat h0 n;
  bignum_bn_v_is_as_nat h0 x;
  bignum_bn_v_is_as_nat h0 y;
  SN.bn_sub_mod_n_lemma (as_seq h0 n) (as_seq h0 x) (as_seq h0 y);
  bignum_bn_v_is_as_nat h1 out


///  Multiplication

[@CInline]
let bn_mul4 f r out =
  let h0 = ST.get () in
  BN.bn_mul #U64 4ul 4ul f r out;
  let h1 = ST.get () in
  SN.bn_mul_lemma (as_seq h0 f) (as_seq h0 r);
  bignum_bn_v_is_as_nat h0 f;
  bignum_bn_v_is_as_nat h0 r;
  bignum_bn_v_is_wide_as_nat h1 out


[@CInline]
let bn_sqr4 f out =
  let h0 = ST.get () in
  BN.bn_sqr #U64 4ul f out;
  let h1 = ST.get () in
  SN.bn_sqr_lemma (as_seq h0 f);
  bignum_bn_v_is_as_nat h0 f;
  bignum_bn_v_is_wide_as_nat h1 out


///  pow2-operations

val lemma_shift_256: a: int -> b: int -> c: int -> d: int -> Lemma (
    a * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
    b * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
    c * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64  +
    d * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 ==
    (a + b * pow2 64 + c * pow2 64 * pow2 64 + d * pow2 64 * pow2 64 * pow2 64) * pow2 64 * pow2 64 * pow2 64 * pow2 64)

let lemma_shift_256 a b c d = ()


[@CInline]
let bn_lshift256 i o =
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);

  let h0 = ST.get() in
    upd o (size 0) (u64 0);
    upd o (size 1) (u64 0);
    upd o (size 2) (u64 0);
    upd o (size 3) (u64 0);
    upd o (size 4) i.(size 0);
    upd o (size 5) i.(size 1);
    upd o (size 6) i.(size 2);
    upd o (size 7) i.(size 3);

  lemma_shift_256
    (v (Lib.Sequence.index (as_seq h0 i) 0))
    (v (Lib.Sequence.index (as_seq h0 i) 1))
    (v (Lib.Sequence.index (as_seq h0 i) 2))
    (v (Lib.Sequence.index (as_seq h0 i) 3))


///  Conversion between bignum and bytes representation

[@CInline]
let bn_to_bytes_be4 f res =
  let h0 = ST.get () in
  bignum_bn_v_is_as_nat h0 f;
  Hacl.Spec.Bignum.Convert.bn_to_bytes_be_lemma #U64 32 (as_seq h0 f);
  Hacl.Bignum.Convert.mk_bn_to_bytes_be true 32ul f res


[@CInline]
let bn_from_bytes_be4 b res =
  let h0 = ST.get () in
  Hacl.Spec.Bignum.Convert.bn_from_bytes_be_lemma #U64 32 (as_seq h0 b);
  Hacl.Bignum.Convert.mk_bn_from_bytes_be true 32ul b res;
  let h1 = ST.get () in
  bignum_bn_v_is_as_nat h1 res


[@CInline]
let bn_to_bytes_le4 f res =
  let h0 = ST.get () in
  bignum_bn_v_is_as_nat h0 f;
  Hacl.Spec.Bignum.Convert.bn_to_bytes_le_lemma #U64 32 (as_seq h0 f);
  Hacl.Bignum.Convert.mk_bn_to_bytes_le true 32ul f res


[@CInline]
let bn_from_bytes_le4 b res =
  let h0 = ST.get () in
  Hacl.Spec.Bignum.Convert.bn_from_bytes_le_lemma #U64 32 (as_seq h0 b);
  Hacl.Bignum.Convert.mk_bn_from_bytes_le true 32ul b res;
  let h1 = ST.get () in
  bignum_bn_v_is_as_nat h1 res
