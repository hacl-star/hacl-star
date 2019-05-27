module Hacl.Test.Bignum

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Bignum.Core
open Hacl.Impl.Bignum.Convert
open Hacl.Impl.Bignum.Comparison
open Hacl.Impl.Bignum.Addition


inline_for_extraction unfold noextract
val print_str: string -> ST unit (requires fun _ -> true) (ensures fun h0 _ h1 -> h0 == h1)
let print_str x = C.String.print (C.String.of_literal x)

inline_for_extraction unfold noextract
val print_strln: string -> ST unit (requires fun _ -> true) (ensures fun h0 _ h1 -> h0 == h1)
let print_strln x = print_str (x ^ "\n")

inline_for_extraction unfold noextract
val print_bool: b:bool -> ST unit (requires fun _ -> true) (ensures fun h0 _ h1 -> h0 == h1)
let print_bool b =
  C.String.print (if b then C.String.of_literal "true\n" else C.String.of_literal "false\n")



inline_for_extraction noextract
val test_comparison_gen:
     a:snat
  -> b:snat{b <= a}
  -> St unit
let test_comparison_gen a b =
  let less_exp = normalize_term (a < b) in
  let eq_exp = normalize_term (a = b) in

  admit();

  let bn_a: lbignum (nat_bytes_num a) = nat_to_bignum_exact a in
  let bn_b: lbignum (nat_bytes_num b) = nat_to_bignum_exact b in

  let less_res = bn_is_less bn_a bn_b in
  let eq_res = bn_is_equal bn_a bn_b in

  let res = (less_res = less_exp && eq_res = eq_exp) in
  if res then print_strln " * Success" else print_strln " * Failed"

inline_for_extraction noextract
val test_eq_representation:
     a:snat{v (nat_bytes_num a) + 5 < max_size_t}
  -> Stack unit (requires fun _ -> true) (ensures fun _ _ _ -> true)
let test_eq_representation a =
  push_frame();

  [@inline_let]
  let aLen = nat_bytes_num a in
  [@inline_let]
  let bLen = nat_bytes_num a +! 1ul in
  [@inline_let]
  let cLen = nat_bytes_num a +! 5ul in

  let bn_a: lbignum aLen = nat_to_bignum_exact a in
  let bn_b: lbignum bLen = nat_to_bignum a in
  let bn_c: lbignum bLen = nat_to_bignum a in

  assert_norm (v aLen > 0);
  assert_norm (v bLen > 0);
  assert_norm (v aLen <= v bLen);
  let res = bn_is_equal bn_b bn_a in
   if res then print_strln " * Success" else print_strln " * Failed";
  pop_frame()

val test_comparison: unit -> St unit
let test_comparison _ =
  C.String.print (C.String.of_literal "Testing comparison\n");
  push_frame();

  test_comparison_gen 0 0;
  test_comparison_gen 1 0;
  test_comparison_gen 12345 0;
  test_comparison_gen 12345 12345;
  test_comparison_gen 18446744073709551618 18446744073709551618;
  test_comparison_gen 18446744073709551618 18446744073709551617;

  C.String.print (C.String.of_literal "...leading zeroes tests:\n");

  test_eq_representation 0;
  test_eq_representation 1;
  test_eq_representation 100;
  test_eq_representation 10000000000000000000000000;

  pop_frame()

inline_for_extraction noextract
val test_addition_gen:
     a:snat
  -> b:snat{b <= a}
  -> St unit
let test_addition_gen a b =
  admit();
  let bn_a   = nat_to_bignum_exact a in
  let bn_b   = nat_to_bignum_exact b in
  let bn_res = nat_to_bignum_exact (normalize_term (b+a)) in
  let bn_c   = nat_to_bignum_exact (normalize_term (b+a)) in

  bn_add_full bn_a bn_b bn_res;
  let res = bn_is_equal bn_c bn_res in
  if res then print_strln " * Success" else print_strln " * Failed"


val test_addition: unit -> St unit
let test_addition _ =
  C.String.print (C.String.of_literal "Testing addition \n");
  push_frame();

  test_addition_gen 0 0;
  test_addition_gen 1 0;
  test_addition_gen 12345 0;
  test_addition_gen 10 5;
  test_addition_gen 10000000000 5;
  test_addition_gen
    111111111111111111111111111111
    18446744073709551618;

  pop_frame()

val testBignum: unit -> St unit
let testBignum _ =
  C.String.print (C.String.of_literal "Bignum tests: \n");
  test_comparison ();
  test_addition ();
  C.String.print (C.String.of_literal "Bignum tests are done \n\n")
