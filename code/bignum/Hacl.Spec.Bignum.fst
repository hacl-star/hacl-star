module Hacl.Spec.Bignum

module Loops = Lib.LoopCombinators


#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let bn_add #t #aLen #bLen a b =
  Hacl.Spec.Bignum.Addition.bn_add a b

let bn_add_lemma #t #aLen #bLen a b =
  Hacl.Spec.Bignum.Addition.bn_add_lemma a b

let bn_sub #t #aLen #bLen a b =
  Hacl.Spec.Bignum.Addition.bn_sub a b

let bn_sub_lemma #t #aLen #bLen a b =
  Hacl.Spec.Bignum.Addition.bn_sub_lemma a b

let bn_reduce_once #t #len n c0 a =
  let c1, res = bn_sub a n in
  let c = c0 -. c1 in
  map2 (mask_select c) a res


let bn_reduce_once_lemma #t #len n c0 res0 =
  let pbits = bits t in
  let tmp = bn_v res0 + v c0 * pow2 (pbits * len) in
  let c1, res1 = bn_sub res0 n in
  bn_sub_lemma res0 n;
  assert (bn_v res1 - v c1 * pow2 (pbits * len) == bn_v res0 - bn_v n);
  let c = c0 -. c1 in
  assert (bn_v res1 + (v c0 - v c1) * pow2 (pbits * len) == tmp - bn_v n);
  let res = map2 (mask_select c) res0 res1 in

  if tmp < bn_v n then begin
    assert (v c0 == 0);
    assert (v c1 == 1);
    assert (v c == pow2 pbits - 1);
    lseq_mask_select_lemma res0 res1 c;
    assert (bn_v res == bn_v res0);
    Math.Lemmas.small_mod tmp (bn_v n);
    assert (bn_v res == tmp % bn_v n) end
  else begin
    assert (tmp - bn_v n < bn_v n);
    bn_eval_bound res1 len;
    bn_eval_bound n len;
    assert (v c == 0);
    lseq_mask_select_lemma res0 res1 c;
    assert (bn_v res == bn_v res1);
    Math.Lemmas.modulo_addition_lemma tmp (bn_v n) (- 1);
    assert (bn_v res % bn_v n == tmp % bn_v n);
    Math.Lemmas.small_mod (bn_v res) (bn_v n) end


let bn_add_mod_n #t #len n a b =
  let c0, res0 = bn_add a b in
  bn_reduce_once n c0 res0


let bn_add_mod_n_lemma #t #len n a b =
  let c0, res0 = bn_add a b in
  bn_add_lemma a b;
  bn_reduce_once_lemma n c0 res0

let bn_mul #t #aLen #bLen a b =
  Hacl.Spec.Bignum.Multiplication.bn_mul a b

let bn_mul_lemma #t #aLen #bLen a b =
  Hacl.Spec.Bignum.Multiplication.bn_mul_lemma a b

let bn_karatsuba_mul #t #aLen a b =
  Hacl.Spec.Bignum.Karatsuba.bn_karatsuba_mul a b

let bn_karatsuba_mul_lemma #t #aLen a b =
  Hacl.Spec.Bignum.Karatsuba.bn_karatsuba_mul_lemma a b

let bn_sqr #t #aLen a =
  Hacl.Spec.Bignum.Multiplication.bn_sqr a

let bn_sqr_lemma #t #aLen a =
  Hacl.Spec.Bignum.Multiplication.bn_sqr_lemma a

let bn_karatsuba_sqr #t #aLen a =
  Hacl.Spec.Bignum.Karatsuba.bn_karatsuba_sqr a

let bn_karatsuba_sqr_lemma #t #aLen a =
  Hacl.Spec.Bignum.Karatsuba.bn_karatsuba_sqr_lemma a

let bn_mul1_lshift_add #t #aLen #resLen a b j acc =
  Hacl.Spec.Bignum.Multiplication.bn_mul1_lshift_add a b j acc

let bn_mul1_lshift_add_lemma #t #aLen #resLen a b j acc =
  Hacl.Spec.Bignum.Multiplication.bn_mul1_lshift_add_lemma a b j acc

let bn_rshift #t #len b i =
  Hacl.Spec.Bignum.Lib.bn_div_pow2 b i

let bn_rshift_lemma #t #len c i =
  Hacl.Spec.Bignum.Lib.bn_div_pow2_lemma c i

let bn_sub_mask #t #len n a =
  let mask = BSeq.seq_eq_mask n a len in
  let mod_mask = map (logand mask) n in
  let c, res = Hacl.Spec.Bignum.Addition.bn_sub a mod_mask in
  res

let bn_sub_mask_lemma #t #len n a =
  let mask = Lib.ByteSequence.seq_eq_mask n a len in
  assert (n == a ==> v mask == v (ones t SEC));
  assert (n =!= a ==> v mask == v (zeros t SEC));
  let mod_mask = map (logand mask) n in
  bn_mask_lemma n mask;
  assert (n == a ==> bn_v mod_mask == bn_v n);
  assert (n =!= a ==> bn_v mod_mask == 0);

  let c, res = Hacl.Spec.Bignum.Addition.bn_sub a mod_mask in
  Hacl.Spec.Bignum.Addition.bn_sub_lemma a mod_mask;
  assert (bn_v res - v c * pow2 (bits t * len) == bn_v a - bn_v mod_mask);
  bn_eval_bound res len;
  assert (bn_v res == bn_v a - bn_v mod_mask);

  Classical.move_requires_2 (bn_eval_inj len) n a

(* get and set i-th bit of a bignum *)

let bn_get_ith_bit #t #len input ind =
  Hacl.Spec.Bignum.Lib.bn_get_ith_bit input ind

let bn_get_ith_bit_lemma #t #len b ind =
  Hacl.Spec.Bignum.Lib.bn_get_ith_bit_lemma b ind

let bn_set_ith_bit #t #len input ind =
  Hacl.Spec.Bignum.Lib.bn_set_ith_bit input ind

let bn_set_ith_bit_lemma #t #len input ind =
  Hacl.Spec.Bignum.Lib.bn_set_ith_bit_lemma input ind

(* conditional swap *)

let cswap2 #t #len bit b1 b2 =
  Hacl.Spec.Bignum.Lib.cswap2 bit b1 b2

let cswap2_lemma #t #len bit b1 b2 =
  Hacl.Spec.Bignum.Lib.cswap2_lemma bit b1 b2

(* Bignum comparison and test functions *)

let bn_is_odd #t #len b =
  Hacl.Spec.Bignum.Comparison.bn_is_odd b

let bn_is_odd_lemma #t #len b =
  Hacl.Spec.Bignum.Comparison.bn_is_odd_lemma b

let bn_eq_mask #t #len a b =
  Hacl.Spec.Bignum.Comparison.bn_eq_mask a b

let bn_eq_mask_lemma #t #len a b =
  Hacl.Spec.Bignum.Comparison.bn_eq_mask_lemma a b

let bn_is_zero_mask #t #len b =
  Hacl.Spec.Bignum.Comparison.bn_is_zero_mask b

let bn_is_zero_mask_lemma #t #len b =
  Hacl.Spec.Bignum.Comparison.bn_is_zero_mask_lemma b

let bn_lt_mask #t #len a b =
  Hacl.Spec.Bignum.Comparison.bn_lt_mask a b

let bn_lt_mask_lemma #t #len a b =
  Hacl.Spec.Bignum.Comparison.bn_lt_mask_lemma a b

let bn_lt_pow2_mask #t #len b x =
  Hacl.Spec.Bignum.Comparison.bn_lt_pow2_mask b x

let bn_lt_pow2_mask_lemma #t #len b x =
  Hacl.Spec.Bignum.Comparison.bn_lt_pow2_mask_lemma b x

let bn_gt_pow2_mask #t #len b x =
  Hacl.Spec.Bignum.Comparison.bn_gt_pow2_mask b x

let bn_gt_pow2_mask_lemma #t #len b x =
  Hacl.Spec.Bignum.Comparison.bn_gt_pow2_mask_lemma b x

(* Conversion functions *)

let bn_from_uint #t len x =
  Hacl.Spec.Bignum.Convert.bn_from_uint len x

let bn_from_uint_lemma #t len x =
  Hacl.Spec.Bignum.Convert.bn_from_uint_lemma len x

let bn_from_bytes_be #t len b =
  Hacl.Spec.Bignum.Convert.bn_from_bytes_be len b

let bn_from_bytes_be_lemma #t len b =
  Hacl.Spec.Bignum.Convert.bn_from_bytes_be_lemma #t len b

let bn_from_bytes_le #t len b =
  Hacl.Spec.Bignum.Convert.bn_from_bytes_le #t len b

let bn_from_bytes_le_lemma #t len b =
  Hacl.Spec.Bignum.Convert.bn_from_bytes_le_lemma #t len b

let bn_to_bytes_be #t len b =
  Hacl.Spec.Bignum.Convert.bn_to_bytes_be len b

let bn_to_bytes_be_lemma #t len b =
  Hacl.Spec.Bignum.Convert.bn_to_bytes_be_lemma len b

let bn_to_bytes_le #t len b =
  Hacl.Spec.Bignum.Convert.bn_to_bytes_le len b

let bn_to_bytes_le_lemma #t len b =
  Hacl.Spec.Bignum.Convert.bn_to_bytes_le_lemma len b
