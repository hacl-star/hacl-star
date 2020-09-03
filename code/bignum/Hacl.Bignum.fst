module Hacl.Bignum

friend Hacl.Spec.Bignum

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let bn_add_eq_len aLen a b res =
  Hacl.Bignum.Addition.bn_add_eq_len aLen a b res

let bn_sub_eq_len aLen a b res =
  Hacl.Bignum.Addition.bn_sub_eq_len aLen a b res

let bn_add aLen a bLen b res =
  Hacl.Bignum.Addition.bn_add aLen a bLen b res

let bn_sub aLen a bLen b res =
  Hacl.Bignum.Addition.bn_sub aLen a bLen b res

let bn_reduce_once len n c0 res =
  push_frame ();
  let tmp = create len (u64 0) in
  let c1 = bn_sub_eq_len len res n tmp in
  let c = c0 -. c1 in
  map2T len res (mask_select c) res tmp;
  pop_frame()

let bn_add_mod_n len n a b res =
  let c0 = bn_add_eq_len len a b res in
  bn_reduce_once len n c0 res

let bn_karatsuba_mul aLen a b res =
  let h0 = ST.get () in
  Hacl.Spec.Bignum.bn_karatsuba_mul_lemma (as_seq h0 a) (as_seq h0 b);
  Hacl.Bignum.Karatsuba.bn_karatsuba_mul aLen a b res

let bn_mul aLen a bLen b res =
  Hacl.Bignum.Multiplication.bn_mul aLen a bLen b res

let bn_karatsuba_sqr aLen a res =
  let h0 = ST.get () in
  Hacl.Spec.Bignum.bn_karatsuba_sqr_lemma (as_seq h0 a);
  Hacl.Bignum.Karatsuba.bn_karatsuba_sqr aLen a res

let bn_sqr aLen a res =
  let h0 = ST.get () in
  Hacl.Spec.Bignum.bn_sqr_lemma (as_seq h0 a);
  Hacl.Bignum.Multiplication.bn_sqr aLen a res

let bn_mul1_lshift_add_in_place aLen a b j res =
  Hacl.Bignum.Multiplication.bn_mul1_lshift_add aLen a b j res

let bn_rshift len b i res =
  copy res (sub b i (len -! i))

let bn_sub_mask len n a =
  push_frame ();
  let mask = create 1ul (ones U64 SEC) in
  let mod_mask = create len (u64 0) in
  let mask = Lib.ByteBuffer.buf_eq_mask n a len mask in
  mapT len mod_mask (logand mask) n;
  let _ = Hacl.Bignum.Addition.bn_sub_eq_len len a mod_mask a in
  pop_frame ()

let bn_get_ith_bit len input ind =
  Hacl.Bignum.Lib.bn_get_ith_bit len input ind

let bn_set_ith_bit len input ind =
  Hacl.Bignum.Lib.bn_set_ith_bit len input ind

(* bignum comparison and test functions *)

let bn_is_odd len a =
  Hacl.Bignum.Comparison.bn_is_odd len a

let bn_eq_mask len a b =
  Hacl.Bignum.Comparison.bn_eq_mask len a b

let bn_is_zero_mask len b =
  Hacl.Bignum.Comparison.bn_is_zero_mask len b

let mk_bn_lt_mask len a b =
  Hacl.Bignum.Comparison.bn_lt_mask len a b

[@CInline]
let bn_lt_mask = mk_bn_lt_mask

let bn_lt_pow2_mask len b x =
  Hacl.Bignum.Comparison.bn_lt_pow2_mask len b x

let bn_gt_pow2_mask len b x =
  Hacl.Bignum.Comparison.bn_gt_pow2_mask len b x

(* Convertion functions *)

let bn_from_uint len x b =
  Hacl.Bignum.Convert.bn_from_uint len x b

let bn_from_bytes_be len b res =
  Hacl.Bignum.Convert.bn_from_bytes_be len b res

let bn_to_bytes_be len b res =
  Hacl.Bignum.Convert.bn_to_bytes_be len b res

let bn_from_bytes_le len b res =
  Hacl.Bignum.Convert.bn_from_bytes_le len b res

let bn_to_bytes_le len b res =
  Hacl.Bignum.Convert.bn_to_bytes_le len b res
