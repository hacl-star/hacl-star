module Vale.Math.Bits
open FStar.Mul

let lemma_pow2_le m n = FStar.Math.Lemmas.pow2_le_compat n m

let lemma_i2b_eq #n a b =
  assert_norm (b_i2b a == b_i2b b ==> int2bv a == int2bv b);
  int2bv_lemma_2 #n a b

let lemma_i2b_uext #n m a =
  Vale.Lib.Bv_s.int2bv_uext #n #m a (uext #n #m a);
  assert_norm (b_i2b (uext #n #m a) == b_uext #n #m (b_i2b #n a))

let lemma_i2b_and #n a b =
  int2bv_logand #n #a #b #(bvand #n (int2bv #n a) (int2bv #n b)) ();
  assert_norm (b_i2b #n (logand #n a b) == b_and #n (b_i2b a) (b_i2b b))

let lemma_i2b_or #n a b =
  int2bv_logor #n #a #b #(bvor #n (int2bv #n a) (int2bv #n b)) ();
  assert_norm (b_i2b #n (logor #n a b) == b_or #n (b_i2b a) (b_i2b b))

let lemma_i2b_xor #n a b =
  int2bv_logxor #n #a #b #(bvxor #n (int2bv #n a) (int2bv #n b)) ();
  assert_norm (b_i2b #n (logxor #n a b) == b_xor #n (b_i2b a) (b_i2b b))

let lemma_i2b_shl #n a b =
  int2bv_shl #n #a #b #(bvshl #n (int2bv #n a) b) ();
  assert_norm (b_i2b #n (shift_left #n a b) == b_shl #n (b_i2b a) b)

let lemma_i2b_shr #n a b =
  int2bv_shr #n #a #b #(bvshr #n (int2bv #n a) b) ();
  assert_norm (b_i2b #n (shift_right #n a b) == b_shr #n (b_i2b a) b)

let lemma_i2b_add #n a b =
  int2bv_add #n #a #b #(bvadd #n (int2bv #n a) (int2bv #n b)) ();
  assert_norm (b_i2b #n (add_mod #n a b) == b_add #n (b_i2b a) (b_i2b b))

let lemma_i2b_sub #n a b =
  int2bv_sub #n #a #b #(bvsub #n (int2bv #n a) (int2bv #n b)) ();
  assert_norm (b_i2b #n (sub_mod #n a b) == b_sub #n (b_i2b a) (b_i2b b))

let lemma_i2b_mul #n a b =
  int2bv_mul #n #a #b #(bvmul #n (int2bv #n a) b) ();
  assert_norm (b_i2b #n (mul_mod #n a b) == b_mul #n (b_i2b a) b)

let lemma_i2b_div #n a b =
  int2bv_div #n #a #b #(bvdiv #n (int2bv #n a) b) ();
  assert_norm (b_i2b #n (udiv #n a b) == b_div #n (b_i2b a) b)

let lemma_i2b_mod #n a b =
  int2bv_mod #n #a #b #(bvmod #n (int2bv #n a) b) ();
  assert_norm (bvmod #n (int2bv a) b == b_mod #n (b_i2b a) b);
  assert_norm (int2bv #n (mod #n a b) == b_i2b #n (mod #n a b));
  ()

let add_hide #n a b =
  if a + b < pow2 n then FStar.Math.Lemmas.modulo_lemma (a + b) (pow2 n);
  add_mod a b

let sub_hide #n a b =
  if 0 <= a - b then FStar.Math.Lemmas.modulo_lemma (a - b) (pow2 n);
  sub_mod a b

let mul_hide #n a b =
  FStar.Math.Lemmas.nat_times_nat_is_nat a b;
  if a * b < pow2 n then FStar.Math.Lemmas.modulo_lemma (a * b) (pow2 n);
  assert_norm (mul_mod a b == (a * b) % pow2 n);
  mul_mod a b

let lemma_i2b_all () =
  FStar.Classical.forall_intro_3 (fun n a b -> lemma_i2b_uext #n a b);
  FStar.Classical.forall_intro_3 (fun n a b -> lemma_i2b_and #n a b);
  FStar.Classical.forall_intro_3 (fun n a b -> lemma_i2b_or #n a b);
  FStar.Classical.forall_intro_3 (fun n a b -> lemma_i2b_xor #n a b);
  FStar.Classical.forall_intro_3 (fun n a b -> lemma_i2b_shl #n a b);
  FStar.Classical.forall_intro_3 (fun n a b -> lemma_i2b_shr #n a b);
  FStar.Classical.forall_intro_3 (fun n a b -> lemma_i2b_add #n a b);
  FStar.Classical.forall_intro_3 (fun n a b -> lemma_i2b_sub #n a b);
  FStar.Classical.forall_intro_3 (fun n a b -> lemma_i2b_mul #n a b);
  FStar.Classical.forall_intro_3 (fun n a b -> lemma_i2b_div #n a b);
  FStar.Classical.forall_intro_3 (fun n a b -> lemma_i2b_mod #n a b);
  ()

let lemma_i2b_with_all n p =
  lemma_i2b_all ()

let lemma_i2b_equal #n x y =
  lemma_i2b_all ();
  lemma_i2b_eq x y

#reset-options "--initial_fuel 0 --max_fuel 0"
let lemma_bveq #n a b =
  let ia = bv2int a in
  let ib = bv2int b in
  int2bv_logxor #n #ia #ib #(bvxor a b) ();
  int2bv_logxor #n #ia #ia #(bvxor a a) ();
  assert (int2bv #n (logxor #n ia ib) == int2bv #n (logxor #n ia ia));
  assert (bv2int (int2bv #n (logxor #n ia ib)) == logxor #n ia ib);
  assert (bv2int (int2bv #n (logxor #n ia ia)) == logxor #n ia ia);
  assert (logxor #n ia ib == logxor #n ia ia);
  logxor_self ia;
  logxor_neq_nonzero ia ib;
  ()

let lemma_to_is_bv8_bv (a:bv_t 32) : Lemma
  (requires bvult a (int2bv 0x100))
  (ensures is_bv8 a)
  =
  lemma_bveq a (bvand a (int2bv 0xff));
  assert_norm (is_bv8 a)

let lemma_to_is_bv8 a =
  int2bv_lemma_ult_1 a 0x100;
  lemma_to_is_bv8_bv (int2bv a);
  assert_norm (b_i2b a == int2bv a)

