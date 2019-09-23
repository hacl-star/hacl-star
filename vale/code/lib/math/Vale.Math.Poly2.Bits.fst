module Vale.Math.Poly2.Bits
open FStar.Mul
open Vale.Arch.TypesNative

let lemma_to_of_uint n u =
  let a = of_uint n u in
  let u' = to_uint n a in
  lemma_index a;
  lemma_reverse_define_all ();
  let s = UInt.to_vec #n u in
  let s' = UInt.to_vec #n u' in
  assert (equal s s');
  ()

let rec of_nat x =
  if x = 0 then zero
  else
    let p = shift (of_nat (x / 2)) 1 in
    if x % 2 = 0 then p else p +. one

let rec lemma_of_to_vec_zero (i:nat) (n:nat) : Lemma
  (requires i < n)
  (ensures index (to_vec #n 0) i == false)
  [SMTPat (index (to_vec #n 0) i)]
  =
  if i + 1 < n then lemma_of_to_vec_zero i (n - 1)

let lemma_of_uint_zero (n:nat) : Lemma
  (ensures of_uint_ n 0 == zero)
  =
  lemma_bitwise_all ();
  lemma_equal (of_uint_ n 0) zero

let rec lemma_of_nat_of_uint n x
  =
  if n > 0 then
  (
    lemma_of_nat_of_uint (n - 1) (x / 2);
    lemma_bitwise_all ();
    lemma_equal (of_nat x) (of_uint n x)
  )

let rec lemma_to_nat_rec (len:nat) (p:poly) (c:nat) (n:nat) (i:nat) : Lemma
  (requires degree p < len /\ normalize (poly_nat_eq_rec len p c n))
  (ensures p.[len - n + i] == (of_nat c).[i])
  =
  lemma_bitwise_all ();
  if (i > 0 && n > 0) then lemma_to_nat_rec len p (c / 2) (n - 1) (i - 1)

let lemma_to_nat len p c =
  lemma_bitwise_all ();
  let f (i:int) : Lemma (p.[i] == (of_nat c).[i]) =
    if 0 <= i then lemma_to_nat_rec len p c len i
    in
  FStar.Classical.forall_intro f;
  lemma_equal p (of_nat c)

let of_nat32 n =
  lemma_of_nat_of_uint 32 n;
  of_uint 32 n

let rec lemma_of_nat_of_uint32 (x:nat32) : Lemma
  (ensures of_nat32 x == of_nat x)
  =
  lemma_of_nat_of_uint 32 x

let of_nat32_zero =
  lemma_bitwise_all ();
  lemma_zero_nth 32;
  lemma_equal (of_nat32 0) zero

let of_nat32_ones =
  lemma_bitwise_all ();
  lemma_to_nat 32 (ones 32) 0xffffffff

let of_nat32_eq a b =
  lemma_of_nat_of_uint 32 a;
  lemma_of_nat_of_uint 32 b;
  lemma_to_of_uint 32 a;
  lemma_to_of_uint 32 b;
  ()

let of_nat32_xor a b =
  lemma_bitwise_all ();
  lemma_ixor_nth_all 32;
  lemma_equal (of_nat32 a +. of_nat32 b) (of_nat32 (ixor a b))

let of_nat32_and a b =
  lemma_bitwise_all ();
  lemma_iand_nth_all 32;
  lemma_equal (poly_and (of_nat32 a) (of_nat32 b)) (of_nat32 (iand a b))

let lemma_poly128_extract_nat32s a0 a1 a2 a3 =
  let a = poly128_of_nat32s a0 a1 a2 a3 in
  lemma_bitwise_all ();
  lemma_equal (of_nat32 a0) (mask a 32);
  lemma_equal (of_nat32 a1) (mask (shift a (-32)) 32);
  lemma_equal (of_nat32 a2) (mask (shift a (-64)) 32);
  lemma_equal (of_nat32 a3) (shift a (-96));
  ()

#reset-options "--z3rlimit 20"
let lemma_quad32_of_nat32s a0 a1 a2 a3 =
  let a = poly128_of_nat32s a0 a1 a2 a3 in
  reveal_to_quad32 a;
  lemma_bitwise_all ();
  lemma_quad32_vec_equal (Mkfour a0 a1 a2 a3) (to_quad32 a)
#reset-options

let lemma_quad32_to_nat32s a =
  let Mkfour a0 a1 a2 a3 = to_quad32 a in
  reveal_to_quad32 a;
  lemma_bitwise_all ();
  lemma_equal a (poly128_of_nat32s a0 a1 a2 a3)

let lemma_quad32_extract_nat32s a =
  let Mkfour a0 a1 a2 a3 = to_quad32 a in
  lemma_quad32_to_nat32s a;
  lemma_poly128_extract_nat32s a0 a1 a2 a3;
  ()

let lemma_quad32_double a =
  let q = to_quad32 a in
  let lo = quad32_double_lo q in
  let hi = quad32_double_hi q in
  let n = monomial 64 in
  reveal_to_quad32 a;
  reveal_of_double32 lo;
  reveal_of_double32 hi;
  lemma_split_define a 64;
  lemma_add_define_all ();
  lemma_reverse_define_all ();
  lemma_index_all ();
  lemma_equal (of_double32 lo) (a %. n);
  lemma_equal (of_double32 hi) (a /. n);
  ()

let lemma_of_double32_degree (d:double32) =
  reveal_of_double32 d

let lemma_of_quad32_degree (q:quad32) =
  reveal_of_quad32 q

#reset-options "--z3rlimit 30"
let lemma_to_of_quad32 q =
  reveal_of_quad32 q;
  reveal_to_quad32 (of_quad32 q);
  let a = of_quad32 q in
  let Mkfour q0 q1 q2 q3 = q in
  let Mkfour q0' q1' q2' q3' = to_quad32 a in
  lemma_index a;
  lemma_reverse_define_all ();
  let s0 = UInt.to_vec #32 q0 in
  let s1 = UInt.to_vec #32 q1 in
  let s2 = UInt.to_vec #32 q2 in
  let s3 = UInt.to_vec #32 q3 in
  let s0' = UInt.to_vec #32 q0' in
  let s1' = UInt.to_vec #32 q1' in
  let s2' = UInt.to_vec #32 q2' in
  let s3' = UInt.to_vec #32 q3' in
  assert (equal s0 s0');
  assert (equal s1 s1');
  assert (equal s2 s2');
  assert (equal s3 s3');
  ()
#reset-options

let lemma_of_to_quad32 a =
  reveal_to_quad32 a;
  reveal_of_quad32 (to_quad32 a);
  lemma_index_all ();
  lemma_reverse_define_all ();
  lemma_equal a (of_quad32 (to_quad32 a))

let lemma_of_to_quad32_mask a =
  reveal_to_quad32 a;
  reveal_of_quad32 (to_quad32 a);
  lemma_index_all ();
  lemma_reverse_define_all ();
  lemma_mask_define_all ();
  lemma_equal (mask a 128) (of_quad32 (to_quad32 a))
