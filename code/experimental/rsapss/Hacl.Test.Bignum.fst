module Hacl.Test.Bignum

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.PrintBuffer
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.PrintSequence
open Lib.Loops
open Lib.Buffer

open Hacl.Impl.Bignum.Core
open Hacl.Impl.Bignum.Convert
open Hacl.Impl.Bignum.Comparison
open Hacl.Impl.Bignum.Addition
open Hacl.Impl.Bignum.Multiplication


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

// Prints in big endian, both with respect to uint64 chunks, and within them.
val print_lbignum:
     #aLen:bn_len
  -> a:lbignum aLen
  -> ST unit (requires fun h -> live h a) (ensures fun h0 _ h1 -> h0 == h1)
let print_lbignum #aLen a =
  assume (8 * v aLen < max_size_t);
  push_frame ();
  let bytes_n = aLen *! 8ul in
  let bytes = create bytes_n (uint 0) in
  assume (8 * v aLen < max_size_t);
  let a' = bignum_to_bytes a bytes in
  print_bytes bytes_n bytes;
  pop_frame ();
  admit()

val test_printing: unit -> St unit
let test_printing _ =
  admit();
  [@inline_let]
  let l:list uint8 = normalize_term (List.Tot.map u8 [0x01; 0x05; 0x10]) in
  let x:lbuffer uint8 3ul = createL l in
  print_bytes 3 x;
  let a = nat_to_bignum_exact 5 in
  print_lbignum a;
  let b = nat_to_bignum_exact (normalize_term (pow2 64 - 1)) in
  print_lbignum b;
  let c = nat_to_bignum_exact (normalize_term (pow2 64 * 2)) in
  print_lbignum c

inline_for_extraction noextract
val test_comp_gen:
     a:snat
  -> b:snat{b <= a}
  -> St unit
let test_comp_gen a b =
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
val test_eq_repr:
     a:snat{v (nat_bytes_num a) + 5 < max_size_t}
  -> Stack unit (requires fun _ -> true) (ensures fun _ _ _ -> true)
let test_eq_repr a =
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

val test_comp: unit -> St unit
let test_comp _ =
  C.String.print (C.String.of_literal "Testing comp\n");
  push_frame();

  test_comp_gen 0 0;
  test_comp_gen 1 0;
  test_comp_gen 12345 0;
  test_comp_gen 12345 12345;
  test_comp_gen 18446744073709551618 18446744073709551618;
  test_comp_gen 18446744073709551618 18446744073709551617;

  C.String.print (C.String.of_literal "...leading zeroes tests:\n");

  test_eq_repr 0;
  test_eq_repr 1;
  test_eq_repr 100;
  test_eq_repr 10000000000000000000000000;

  pop_frame()

#reset-options

inline_for_extraction noextract
val test_add_gen:
     a:snat
  -> b:snat{b <= a /\ issnat (a+b)}
  -> Stack unit (requires fun _ -> true) (ensures fun _ _ _ -> true)
let test_add_gen a b =
  push_frame();

  let a_len: size_t = normalize_term (nat_bytes_num a) in
  let b_len: size_t = normalize_term (nat_bytes_num b) in
  assume (v a_len + 1 <= max_size_t);
  assume (v b_len <= v a_len);
  let res_len: size_t = a_len +. 1ul in
  assume (v (a_len +. 1ul) > 0);
  let c_len: size_t = normalize_term (nat_bytes_num (a+b)) in

  let bn_a:lbignum a_len     = nat_to_bignum_exact a in
  let bn_b:lbignum b_len     = nat_to_bignum_exact b in
  let bn_c:lbignum c_len     = nat_to_bignum_exact (normalize_term (a+b)) in
  let bn_res:lbignum res_len = create res_len (uint 0) in

  admit();
  bn_add_full bn_a bn_b bn_res;
  let res = bn_is_equal bn_c bn_res in
  if res
  then print_strln " * Success"
  else begin
    print_strln " * Failed";
    print_lbignum bn_res;
    print_lbignum bn_c
  end;
  pop_frame()

val test_add: unit -> St unit
let test_add _ =
  C.String.print (C.String.of_literal "Testing add \n");
  push_frame();

  test_add_gen 0 0;
  test_add_gen 1 0;
  test_add_gen 12345 0;
  test_add_gen 10 5;
  test_add_gen 10000000000 5;
  test_add_gen
    111111111111111111111111111111
    18446744073709551618;
  test_add_gen
    111111111111123123123111111111111111111
    184467440737095553212351618;
  test_add_gen
    111111111111123123123111111111111111111
    1;
  test_add_gen
    111111111111123123123111111111111111111
    0;

  pop_frame()


inline_for_extraction noextract
val test_mult_gen:
     a:snat
  -> b:snat{b <= a /\ issnat (a+b)}
  -> Stack unit (requires fun _ -> true) (ensures fun _ _ _ -> true)
let test_mult_gen a b =
  push_frame();

  let a_len: size_t = normalize_term (nat_bytes_num a) in
  let b_len: size_t = normalize_term (nat_bytes_num b) in
  assume (v a_len + v b_len <= max_size_t);
  assume (v (a_len +. b_len) > 0);
  let res_len: size_t = (a_len +. b_len +. 1ul) in

  let bn_a:lbignum a_len     = nat_to_bignum_exact a in
  let bn_b:lbignum b_len     = nat_to_bignum_exact b in
  admit();
  let bn_c:lbignum res_len   = nat_to_bignum #res_len (normalize_term (a * b)) in
  let bn_res:lbignum res_len = create res_len (uint 0) in


  bn_mul bn_a bn_b bn_res;
  let res = bn_is_equal bn_c bn_res in
  if res
  then print_strln " * Success"
  else begin
    print_strln " * Failed";
    print_lbignum bn_res;
    print_lbignum bn_c
  end;
  pop_frame()

val test_mult: unit -> St unit
let test_mult _ =
  C.String.print (C.String.of_literal "Testing mult\n");
  push_frame();

  admit();
  test_mult_gen 0 0;
  test_mult_gen 1 0;
  test_mult_gen 12345 0;
  test_mult_gen 10 5;
  test_mult_gen 10000000000 5;
  test_mult_gen 1234123432165873264969873219648712 1;
  test_mult_gen 1234123432165873264969873219648712 0;
  test_mult_gen 1234123432165873264969873219648712 2;
  test_mult_gen 1234123432165873264969873219648712 3;
  test_mult_gen 1234123432165873264969873219648712 4;
  test_mult_gen 1234123432165873264969873219648712 5;
  test_mult_gen
    111111111111111111111111111111
    18446744073709551618;
  test_mult_gen
    111111111111123123123111111111111111111
    184467440737095553212351618;
  test_mult_gen
    11111111111112312312311111114973210598732098407321111111111111
    18446744073709555321235160918327501928374098320749182318;
  test_mult_gen (normalize_term (pow2 128 * 5)) (normalize_term (pow2 64 * 3));
  test_mult_gen (normalize_term (pow2 128 * 5)) (normalize_term (pow2 128 * 3));
  test_mult_gen (normalize_term (pow2 128 - 1)) (normalize_term (pow2 128 * 3));
  test_mult_gen (normalize_term (pow2 128 + 1)) (normalize_term (pow2 128 * 3));
  test_mult_gen (normalize_term (pow2 128)) (normalize_term (pow2 128 * 3));
  test_mult_gen (normalize_term (pow2 128)) 2;
  test_mult_gen (normalize_term (pow2 128)) 1;
  test_mult_gen (normalize_term (pow2 128)) 0;

  pop_frame()

val testBignum: unit -> St unit
let testBignum _ =
  C.String.print (C.String.of_literal "Bignum tests: \n");
  test_printing ();
  test_comp ();
  test_add ();
  test_mult ();
  C.String.print (C.String.of_literal "Bignum tests are done \n\n")
