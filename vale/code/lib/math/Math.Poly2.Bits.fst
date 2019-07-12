module Math.Poly2.Bits
open Arch.TypesNative

let lemma_add128 a b =
  reveal_to_quad32 a;
  reveal_to_quad32 b;
  reveal_to_quad32 (a +. b);
  lemma_reverse_define_all ();
  lemma_add_define_all ();
  lemma_ixor_nth_all 32;
  Opaque_s.reveal_opaque quad32_xor_def;
  Opaque_s.reveal_opaque reverse_bytes_nat32_def;
  lemma_quad32_vec_equal (to_quad32 (a +. b)) (quad32_xor (to_quad32 a) (to_quad32 b));
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

let lemma_quad32_double_shift a =
  let q = to_quad32 a in
  let Mkfour q0 q1 q2 q3 = to_quad32 a in
  let n = monomial 64 in
  reveal_to_quad32 a;
  reveal_to_quad32 (a /. n);
  reveal_to_quad32 ((a %. n) *. n);
  lemma_split_define a 64;
  lemma_shift_is_mul (a %. n) 64;
  lemma_shift_define (a %. n) 64;
  lemma_add_define_all ();
  lemma_reverse_define_all ();
  lemma_index_all ();
  lemma_zero_nth 32;
  lemma_quad32_vec_equal (Mkfour 0 0 q0 q1) (to_quad32 ((a %. n) *. n));
  lemma_quad32_vec_equal (Mkfour q2 q3 0 0) (to_quad32 (a /. n));
  ()

