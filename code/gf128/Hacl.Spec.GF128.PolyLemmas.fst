module Hacl.Spec.GF128.PolyLemmas

open FStar.Mul
open FStar.UInt
open FStar.Seq
open FStar.BitVector
open FStar.Math.Lemmas

open Lib.Sequence
open Lib.IntTypes
open Lib.IntVector

open Vale.Math.Poly2_s
open Vale.Math.Poly2
open Vale.Math.Poly2.Bits_s
open Vale.Math.Poly2.Bits
open Vale.Math.Poly2.Lemmas

module U = FStar.UInt
module T = Lib.IntTypes
module V = Lib.IntVector
module P = Vale.Math.Poly2_s

let lemma_of_to_uint_128 a =
  reveal_defs ();
  lemma_reverse_define_all ();
  lemma_equal a (of_uint 128 (to_uint 128 a))

let lemma_to_of_vec128 q =
  lemma_create_index_vec_w1 q

let lemma_of_to_vec128 a =
  ()

let lemma_vec128_zero () =
  lemma_bitwise_all ();
  Vale.Arch.TypesNative.lemma_zero_nth 128;
  lemma_equal P.zero (of_uint 128 0);
  ()

let lemma_vec128_ones () =
  lemma_bitwise_all ();
  lemma_equal (ones 128) (of_uint 128 0xffffffffffffffffffffffffffffffff);
  ()

let lemma_add128 a b =
  lemma_bitwise_all ();
  logxor_spec (mk_int #U128 #SEC (to_uint 128 a)) (mk_int #U128 #SEC (to_uint 128 b));
  assert (of_vec128 (to_vec128 a ^| to_vec128 b) ==
      of_uint 128 (U.logxor (to_uint 128 a) (to_uint 128 b))); //OBSERVE
  lemma_equal (P.add a b) (of_vec128 (to_vec128 a ^| to_vec128 b));
  ()

let lemma_add_vec128 a b =
  lemma_add128 (of_vec128 a) (of_vec128 b);
  ()

let lemma_and128 a b =
  lemma_bitwise_all ();
  logand_spec (mk_int #U128 #SEC (to_uint 128 a)) (mk_int #U128 #SEC (to_uint 128 b));
  assert (of_vec128 (to_vec128 a &| to_vec128 b) ==
      of_uint 128 (U.logand (to_uint 128 a) (to_uint 128 b))); //OBSERVE
  lemma_equal (poly_and a b) (of_vec128 (to_vec128 a &| to_vec128 b));
  ()

let lemma_and_vec128 a b =
  lemma_and128 (of_vec128 a) (of_vec128 b);
  ()

#push-options "--z3rlimit 20"
let lemma_vec128_double_shift a =
  lemma_bitwise_all ();
  assert (of_vec128 (to_vec128 a <<| 64ul) ==
      of_uint 128 (U.shift_left (to_uint 128 a) 64));
  lemma_equal (P.shift (mask a 64) 64) (of_vec128 (to_vec128 a <<| 64ul));
  lemma_mask_is_mod a 64;
  lemma_shift_is_mul (P.mod a (monomial 64)) 64;
  assert (of_vec128 (to_vec128 a >>| 64ul) ==
      of_uint 128 (U.shift_right (to_uint 128 a) 64));
  lemma_equal (P.shift a (-64)) (of_vec128 (to_vec128 a >>| 64ul));
  lemma_shift_is_div a 64;
  ()
#pop-options

val lemma_eq_poly_uint_mod_64 (a:poly) (p:FStar.UInt.uint_t 128) : Lemma
  (requires degree a <= 127 /\ a == of_uint 128 p)
  (ensures mod a (monomial 64) == of_uint 128 ((to_uint 128 a) % pow2 64))

#push-options "--z3rlimit 20"
let lemma_eq_poly_uint_mod_64 a p =
  let h = to_vec p in
  let l = U.shift_left p 64 in
  let l_h = to_vec l in
  let r = U.shift_right (U.shift_left p 64) 64 in
  let r_h = to_vec r in
  slice_right_lemma #128 h 64;
  eq_elim #bool #64 (slice #bool #128 l_h 0 64) (slice #bool #128 h 64 128);
  eq_elim #bool #64 (slice #bool #128 r_h 0 64) (zero_vec #64);
  eq_elim #bool #64 (slice #bool #128 r_h 64 128) (slice #bool #128 l_h 0 64);
  from_vec_propriety #128 r_h 64;
  assert (0 * pow2 64 == 0); // Speed up verifying process
  assert (r == p % pow2 64);
  lemma_bitwise_all ();
  lemma_mask_is_mod a 64;
  lemma_equal (P.mod a (monomial 64)) (of_uint 128 (p % pow2 64));
  ()
#pop-options

#push-options "--z3rlimit 50 --max_fuel 1"
val lemma_eq_poly_uint_shift_right (a:poly) (p:U.uint_t 128) (s:nat{s <= 64}) : Lemma
  (requires degree a <= 127 /\ a == of_uint 128 p)
  (ensures P.shift a (-s) == of_uint 128 (p / pow2 s))

let lemma_eq_poly_uint_shift_right a p s =
  reveal_defs ();
  lemma_bitwise_all ();
  lemma_equal (P.shift a (-s)) (of_uint 128 (U.shift_right p s));
  ()
#pop-options

val lemma_eq_poly_uint_shift_left (a:poly) (p:U.uint_t 128) (s:nat{s <= 64}) : Lemma
  (requires degree a <= 63 /\ a == of_uint 128 p)
  (ensures P.shift a s == of_uint 128 ((p * pow2 s) % pow2 128))

let lemma_eq_poly_uint_shift_left a p s =
  lemma_bitwise_all ();
  lemma_equal (P.shift a s) (of_uint 128 (U.shift_left p s));
  ()

val lemma_eq_poly_uint_add (a b:poly) (p1 p2:U.uint_t 128) : Lemma
  (requires degree a <= 127 /\ degree b <= 127 /\
    a == of_uint 128 p1 /\ b == of_uint 128 p2)
  (ensures P.add a b == of_uint 128 (U.logxor p1 p2))

let lemma_eq_poly_uint_add a b p1 p2 =
  lemma_bitwise_all ();
  lemma_equal (P.add a b) (of_uint 128 (U.logxor p1 p2));
  ()

val to_vec_mod_pow2: #n:size_nat -> a:U.uint_t n -> m:pos -> i:nat{n - m <= i /\ i < n} ->
  Lemma (requires (a % pow2 m == 0))
        (ensures  (index #bool #n (to_vec a) i == false))
        [SMTPat (index #bool #n (to_vec #n a) i); SMTPat (pow2 m)]
let rec to_vec_mod_pow2 #n a m i =
  if i = n - 1 then
    begin
    lemma_index_app2 (to_vec #(n - 1) (a / 2)) (Seq.create 1 (a % 2 = 1)) i;
    mod_mult_exact a 2 (pow2 (m - 1))
    end
  else
    begin
    lemma_index_app1 (to_vec #(n - 1) (a / 2)) (Seq.create 1 (a % 2 = 1)) i;
    assert (index #bool #n (to_vec a) i == index #bool #(n - 1) (to_vec #(n - 1) (a / 2)) i);
    mod_pow2_div2 a m;
    to_vec_mod_pow2 #(n - 1) (a / 2) (m - 1) i
    end

val to_vec_lt_pow2: #n:size_nat -> a:U.uint_t n -> m:nat -> i:nat{i < n - m} ->
  Lemma (requires (a < pow2 m))
        (ensures  (index #bool #n (to_vec a) i == false))
        [SMTPat (index #bool #n (to_vec #n a) i); SMTPat (pow2 m)]
let rec to_vec_lt_pow2 #n a m i =
  if n = 0 then ()
  else
    if m = 0 then
      assert (a == U.zero n)
    else
      begin
      lemma_index_app1 (to_vec #(n - 1) (a / 2)) (Seq.create 1 (a % 2 = 1)) i;
      assert (index #bool #n (to_vec a) i == index #bool #(n - 1) (to_vec #(n - 1) (a / 2)) i);
      to_vec_lt_pow2 #(n - 1) (a / 2) (m - 1) i
      end

val logxor_disjoint: #n:size_nat -> a:U.uint_t n -> b:U.uint_t n -> m:pos{m < n} ->
  Lemma (requires (a % pow2 m == 0 /\ b < pow2 m))
        (ensures  (U.logxor #n a b == a + b))

#push-options "--z3rlimit 20 --max_fuel 0"
let logxor_disjoint #n a b m =
  assert (forall (i:nat{n - m <= i /\ i < n}).{:pattern (index #bool #n (to_vec a) i)}
    index #bool #n (to_vec a) i == false);
  assert (forall (i:nat{i < n - m}).{:pattern (index #bool #n (to_vec b) i)}
    index #bool #n (to_vec b) i == false);
  Seq.lemma_split (logxor_vec (to_vec a) (to_vec b)) (n - m);
  assert (forall (i:nat). (n - m <= i /\ i < n) ==>
    index #bool #n (to_vec a) i == Seq.index (Lib.Sequence.to_seq #bool #n (to_vec a)) i);
  assert (forall (i:nat). (i < n - m) ==>
    index #bool #n (to_vec b) i == Seq.index (Lib.Sequence.to_seq #bool #n (to_vec b)) i);
  Seq.lemma_eq_intro
    (logxor_vec (to_vec a) (to_vec b))
    (append (slice #bool #n (to_vec a) 0 (n - m)) (slice #bool #n (to_vec b) (n - m) n));
  append_lemma #(n - m) #m (slice #bool #n (to_vec a) 0 (n - m)) (slice #bool #n (to_vec b) (n - m) n);
  slice_left_lemma #n (to_vec a) (n - m);
  div_exact_r a (pow2 m);
  assert (from_vec #(n - m) (slice #bool #n (to_vec a) 0 (n - m)) * pow2 m == a);
  slice_right_lemma #n (to_vec b) m;
  small_modulo_lemma_1 b (pow2 m);
  assert (from_vec #m (slice #bool #n (to_vec b) (n - m) n) == b)
#pop-options

#push-options "--z3rlimit 150 --max_fuel 1"
let lemma_vec128_shift_left_64 p s =
  vec_cast_uint128 p;
  vec_cast_2_uint64 (vec_shift_left (V.cast U64 2 p) s);
  eq_elim (map (shift_left_i s) (vec_v (V.cast U64 2 p))) (create2
    (shift_left_i s (to_u64 (index (vec_v p) 0)))
    (shift_left_i s (to_u64 (T.shift_right (index (vec_v p) 0) 64ul)))
  );
  reveal_vec_v_1 p;
  reveal_vec_v_1 (V.cast U128 1 (vec_shift_left (V.cast U64 2 p) s));

  let n = monomial 64 in
  let a = of_vec128 p in
  let a0 = P.mod (P.shift (P.mod a n) (v s)) n in
  let a1 = P.mod (P.shift (P.div a n) (v s)) n in
  let p0 = (((to_uint 128 a) % pow2 64) * pow2 (v s)) % pow2 64 in
  let p1 = ((((to_uint 128 a) / pow2 64) % pow2 64) * pow2 (v s)) % pow2 64 in
  let t = T.add
          (T.shift_left (to_u128 (shift_left_i s (to_u64 (T.shift_right #U128 #SEC p 64ul)))) 64ul)
          (to_u128 (shift_left_i s (to_u64 #U128 #SEC p))) in
  assert (t == V.cast U128 1 (vec_shift_left (V.cast U64 2 p) s));
  reveal_vec_v_1 #U128 t;
  assert (of_vec128 t == of_uint 128 (p1 * pow2 64 + p0));

  lemma_eq_poly_uint_shift_right a (to_uint 128 a) 64;
  lemma_div_lt (to_uint 128 a) 128 64;
  small_mod ((to_uint 128 a) / pow2 64) (pow2 64);
  lemma_shift_is_div a 64;
  lemma_eq_poly_uint_shift_left (P.div a n) (((to_uint 128 a) / pow2 64) % pow2 64) (v s);
  lemma_eq_poly_uint_mod_64 (P.shift (P.div a n) (v s)) 
    (((((to_uint 128 a) / pow2 64) % pow2 64) * pow2 (v s)) % pow2 128);
  pow2_modulo_modulo_lemma_1
    ((((to_uint 128 a) / pow2 64) % pow2 64) * pow2 (v s)) 64 128;
  lemma_eq_poly_uint_shift_left (P.mod (P.shift (P.div a n) (v s)) n) 
    (((((to_uint 128 a) / pow2 64) % pow2 64) * pow2 (v s)) % pow2 64) 64;
  pow2_multiplication_modulo_lemma_2
    (((((to_uint 128 a) / pow2 64) % pow2 64) * pow2 (v s)) % pow2 64) 128 64;
  pow2_modulo_modulo_lemma_1 ((((to_uint 128 a) / pow2 64) % pow2 64) * pow2 (v s)) 64 64;
  assert (P.shift a1 64 == of_uint 128 (p1 * pow2 64)); //OBSERVE

  lemma_eq_poly_uint_mod_64 a (to_uint 128 a);
  lemma_eq_poly_uint_shift_left (P.mod a n)
    ((to_uint 128 a) % pow2 64) (v s);
  lemma_eq_poly_uint_mod_64 (P.shift (P.mod a n) (v s))
    ((((to_uint 128 a) % pow2 64) * pow2 (v s)) % pow2 128);
  pow2_modulo_modulo_lemma_1
    (((to_uint 128 a) % pow2 64) * pow2 (v s)) 64 128;
  assert (a0 == of_uint 128 p0); //OBSERVE

  lemma_eq_poly_uint_add (P.shift a1 64) a0 (p1 * pow2 64) p0;
  lemma_mod_lt (((to_uint 128 a) % pow2 64) * pow2 (v s)) (pow2 64);
  multiple_modulo_lemma (((((to_uint 128 a) / pow2 64) % pow2 64) * pow2 (v s)) % pow2 64) (pow2 64);
  logxor_disjoint #128 (p1 * pow2 64) p0 64;
  assert (P.add (P.shift a1 64) a0 == of_uint 128 (p1 * pow2 64 + p0));
  ()
#pop-options

#push-options "--z3rlimit 150 --max_fuel 1"
let lemma_vec128_shift_right_64 p s =
  vec_cast_uint128 p;
  vec_cast_2_uint64 (vec_shift_right (V.cast U64 2 p) s);
  eq_elim (map (shift_right_i s) (vec_v (V.cast U64 2 p))) (create2
    (shift_right_i s (to_u64 (index (vec_v p) 0)))
    (shift_right_i s (to_u64 (T.shift_right (index (vec_v p) 0) 64ul)))
  );
  reveal_vec_v_1 p;
  reveal_vec_v_1 (V.cast U128 1 (vec_shift_right (V.cast U64 2 p) s));

  let n = monomial 64 in
  let a = of_vec128 p in
  let a0 = P.shift (P.mod a n) (-(v s)) in
  let a1 = P.shift (P.div a n) (-(v s)) in
  let p0 = ((to_uint 128 a) % pow2 64) / pow2 (v s) in
  let p1 = (((to_uint 128 a) / pow2 64) % pow2 64) / pow2 (v s) in
  let t = T.add
          (T.shift_left (to_u128 (shift_right_i s (to_u64 (T.shift_right #U128 #SEC p 64ul)))) 64ul)
          (to_u128 (shift_right_i s (to_u64 #U128 #SEC p))) in
  assert (t == V.cast U128 1 (vec_shift_right (V.cast U64 2 p) s));
  reveal_vec_v_1 #U128 t;
  assert (of_vec128 t == of_uint 128 (p1 * pow2 64 + p0));

  lemma_eq_poly_uint_shift_right a (to_uint 128 a) 64;
  lemma_div_lt (to_uint 128 a) 128 64;
  small_mod ((to_uint 128 a) / pow2 64) (pow2 64);
  lemma_shift_is_div a 64;
  lemma_eq_poly_uint_shift_right (P.div a n) (((to_uint 128 a) / pow2 64) % pow2 64) (v s);
  lemma_eq_poly_uint_shift_left (P.shift (P.div a n) (-(v s))) 
    ((((to_uint 128 a) / pow2 64) % pow2 64) / pow2 (v s)) 64;
  lemma_mod_lt ((to_uint 128 a) / pow2 64) (pow2 64);
  lemma_div_lt (((to_uint 128 a) / pow2 64) % pow2 64) 64 (v s);
  small_mod ((((to_uint 128 a) / pow2 64) % pow2 64) / pow2 (v s)) (pow2 (64 - (v s)));
  pow2_multiplication_modulo_lemma_2
    ((((to_uint 128 a) / pow2 64) % pow2 64) / pow2 (v s)) 128 64;
  pow2_modulo_modulo_lemma_2 ((((to_uint 128 a) / pow2 64) % pow2 64) / pow2 (v s)) 64 (64 - (v s));
  assert (P.shift a1 64 == of_uint 128 (p1 * pow2 64)); //OBSERVE

  lemma_eq_poly_uint_mod_64 a (to_uint 128 a);
  lemma_eq_poly_uint_shift_right (P.mod a n)
    ((to_uint 128 a) % pow2 64) (v s);
  assert (a0 == of_uint 128 p0); //OBSERVE

  lemma_eq_poly_uint_add (P.shift a1 64) a0 (p1 * pow2 64) p0;
  lemma_mod_lt (((to_uint 128 a) % pow2 64) / pow2 (v s)) (pow2 64);
  multiple_modulo_lemma ((((to_uint 128 a) / pow2 64) % pow2 64) / pow2 (v s)) (pow2 64);
  logxor_disjoint #128 (p1 * pow2 64) p0 64;
  assert (P.add (P.shift a1 64) a0 == of_uint 128 (p1 * pow2 64 + p0));
  ()
#pop-options
