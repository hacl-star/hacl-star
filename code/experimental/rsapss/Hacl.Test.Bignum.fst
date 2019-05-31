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
open Lib.Math.Algebra

open Hacl.Impl.Bignum.Core
open Hacl.Impl.Bignum.Convert
open Hacl.Impl.Bignum.Comparison
open Hacl.Impl.Bignum.Division
open Hacl.Impl.Bignum.Addition
open Hacl.Impl.Bignum.Multiplication
open Hacl.Impl.Bignum.Exponentiation
open Hacl.Impl.Bignum.Shift


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
  -> b:snat{issnat (a+b)}
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
  admit();
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

#reset-options "--z3rlimit 30"


inline_for_extraction noextract
val test_lshift_gen:
     a:snat
  -> p:nat{p < max_size_t}
  -> Stack unit (requires fun _ -> true) (ensures fun _ _ _ -> true)
let test_lshift_gen a p =
  push_frame();

  let p' = normalize_term (size p) in
  let aLen = normalize_term (nat_bytes_num a) in
  assume (v 64ul > 0);
  let resLen = aLen +. (p' /. 64ul) +. 1ul in
  assume (v aLen + (v p' / 64) + 1 < max_size_t);
  assume (v resLen < max_size_t /\ v resLen > 0);

  let bn_a:lbignum aLen = nat_to_bignum a in
  let bn_res:lbignum resLen = create resLen (uint 0) in
  assume (pow2 p * a > 0 /\ issnat (pow2 p * a));
  assume (v (nat_bytes_num (pow2 p * a)) <= v resLen);
  let bn_expected:lbignum resLen =
        nat_to_bignum (normalize_term (pow2 p * a)) in

  bn_lshift bn_a p' bn_res;
  let res = bn_is_equal bn_expected bn_res in
  if res
  then print_strln " * Success"
  else begin
    print_strln " * Failed";
    print_lbignum bn_res;
    print_lbignum bn_expected
  end;
  pop_frame()

val test_lshift: unit -> St unit
let test_lshift _ =
  C.String.print (C.String.of_literal "Testing lshift\n");
  push_frame();

  test_lshift_gen 3 0;
  test_lshift_gen 3 1;
  test_lshift_gen 3 2;
  test_lshift_gen 3 3;
  test_lshift_gen 3 63;
  test_lshift_gen 3 64;
  test_lshift_gen 3 65;
  test_lshift_gen 3 100;
  test_lshift_gen 3 1024;
  test_lshift_gen 3 511;
  test_lshift_gen 3 512;
  test_lshift_gen 3 513;
  test_lshift_gen 1000000000000000000000000 0;
  test_lshift_gen 1000000000000000000000000 1;
  test_lshift_gen 1000000000000000000000000 2;
  test_lshift_gen 1000000000000000000000000 3;
  test_lshift_gen 1000000000000000000000000 63;
  test_lshift_gen 1000000000000000000000000 64;
  test_lshift_gen 1000000000000000000000000 65;
  test_lshift_gen 1000000000000000000000000 100;
  test_lshift_gen 1000000000000000000000000 256;
  test_lshift_gen 1000000000000000000000000 511;
  test_lshift_gen 1000000000000000000000000 512;
  test_lshift_gen 1000000000000000000000000 513;


  pop_frame ()

inline_for_extraction noextract
val test_rshift1_gen:
     a:snat{a>1}
  -> Stack unit (requires fun _ -> true) (ensures fun _ _ _ -> true)
let test_rshift1_gen a =
  push_frame();

  let aLen = normalize_term (nat_bytes_num a) in

  let bn_a:lbignum aLen = nat_to_bignum a in
  let bn_res:lbignum aLen = create aLen (uint 0) in
  assume (a / 2 > 0 /\ issnat (a / 2) /\ v (nat_bytes_num (a / 2)) <= v aLen);
  let bn_expected:lbignum aLen = nat_to_bignum (normalize_term (a / 2)) in

  bn_rshift1 bn_a bn_res;
  let res = bn_is_equal bn_expected bn_res in
  if res
  then print_strln " * Success"
  else begin
    print_strln " * Failed";
    print_lbignum bn_res;
    print_lbignum bn_expected
  end;
  pop_frame()

val test_rshift1: unit -> St unit
let test_rshift1 _ =
  C.String.print (C.String.of_literal "Testing rshift1\n");
  push_frame();

  test_rshift1_gen 2;
  test_rshift1_gen 3;
  test_rshift1_gen 63;
  test_rshift1_gen 64;
  test_rshift1_gen 65;
  test_rshift1_gen 100;
  test_rshift1_gen 511;
  test_rshift1_gen 512;
  test_rshift1_gen 513;
  test_rshift1_gen 1024;
  test_rshift1_gen 1000000000000000000000000;
  test_rshift1_gen 1000000000000000000000000132123812391;

  pop_frame ()


inline_for_extraction noextract
val test_pow2_gen:
     a:snat{a > 2}
  -> p:nat{p < max_size_t}
  -> Stack unit (requires fun _ -> true) (ensures fun _ _ _ -> true)
let test_pow2_gen a p =
  push_frame();

  let p' = normalize_term (size p) in
  let aLen = normalize_term (nat_bytes_num a) in
  assume (v aLen + 1 < max_size_t);
  let aBits = aLen *. 64ul in

  let bn_a:lbignum aLen = nat_to_bignum a in
  let bn_res:lbignum aLen = create aLen (uint 0) in
  assume (issnat (fexp #a 2 p));
  assume (v (nat_bytes_num (fexp #a 2 p)) <= v aLen);
  let bn_expected:lbignum aLen = nat_to_bignum (normalize_term (fexp #a 2 p)) in

  assume (v aBits / 64 <= v aLen);

  bn_pow2_mod_n aBits bn_a p' bn_res;
  let res = bn_is_equal bn_expected bn_res in
  if res
  then print_strln " * Success"
  else begin
    print_strln " * Failed";
    print_lbignum bn_res;
    print_lbignum bn_expected
  end;
  pop_frame()

val test_pow2: unit -> St unit
let test_pow2 _ =
  C.String.print (C.String.of_literal "Testing pow2 modulo\n");
  push_frame();

  test_pow2_gen 3 0;
  test_pow2_gen 3 1;
  test_pow2_gen 3 2;
  test_pow2_gen 3 3;
  test_pow2_gen 3 100;
  test_pow2_gen 3 1024;
  test_pow2_gen 3 511;
  test_pow2_gen 3 512;
  test_pow2_gen 3 513;
  test_pow2_gen 3 1000000;
  test_pow2_gen 1000000000000000000000000 0;
  test_pow2_gen 1000000000000000000000000 1;
  test_pow2_gen 1000000000000000000000000 2;
  test_pow2_gen 1000000000000000000000000 3;
  test_pow2_gen 1000000000000000000000000 100;
  test_pow2_gen 1000000000000000000000000 256;
  test_pow2_gen 1000000000000000000000000 511;
  test_pow2_gen 1000000000000000000000000 512;
  test_pow2_gen 1000000000000000000000000 513;
  test_pow2_gen 1000000000000000000000000 1024;
  test_pow2_gen 1000000000000000000000000 1000000;


  pop_frame ()


inline_for_extraction noextract
val test_mod_gen:
     n:snat{n > 2}
  -> a:snat
  -> Stack unit (requires fun _ -> true) (ensures fun _ _ _ -> true)
let test_mod_gen n a =
  push_frame();

  let nLen = normalize_term (nat_bytes_num n) in
  let aLen = normalize_term (nat_bytes_num a) in
  let xLen = if nLen >=. aLen then nLen else aLen in

  let bn_n:lbignum xLen = nat_to_bignum n in
  let bn_a:lbignum xLen = nat_to_bignum a in
  let bn_res:lbignum xLen = create xLen (uint 0) in
  assume (issnat (a % n) /\ v (nat_bytes_num (a % n)) <= v xLen);
  let bn_expected:lbignum xLen = nat_to_bignum (normalize_term (a % n)) in

  assume (v xLen + 1 < max_size_t);
  bn_remainder bn_a bn_n bn_res;
  let res = bn_is_equal bn_expected bn_res in
  if res
  then print_strln " * Success"
  else begin
    print_strln " * Failed";
    print_lbignum bn_res;
    print_lbignum bn_expected
  end;
  pop_frame()

val test_mod: unit -> St unit
let test_mod _ =
  C.String.print (C.String.of_literal "Testing mod reduction\n");
  push_frame();

  test_mod_gen 3 0;
  test_mod_gen 3 1;
  test_mod_gen 3 2;
  test_mod_gen 3 3;
  test_mod_gen 3 100;
  test_mod_gen 3 1024;
  test_mod_gen 3 511;
  test_mod_gen 3 512;
  test_mod_gen 3 513;
  test_mod_gen 3 1000000;

  test_mod_gen 256 1024;
  test_mod_gen 256 511;
  test_mod_gen 256 512;
  test_mod_gen 256 513;
  test_mod_gen 256 1000000;

  test_mod_gen 1000000000000000000000000 0;
  test_mod_gen 1000000000000000000000000 1;
  test_mod_gen 1000000000000000000000000 2;
  test_mod_gen 1000000000000000000000000 3;
  test_mod_gen 1000000000000000000000000 100;
  test_mod_gen 1000000000000000000000000 256;
  test_mod_gen 1000000000000000000000000 511;
  test_mod_gen 1000000000000000000000000 512;
  test_mod_gen 1000000000000000000000000 513;
  test_mod_gen 1000000000000000000000000 1024;
  test_mod_gen 1000000000000000000000000 1000000;
  test_mod_gen 1000000000000000000000000
      10000001234912034981720349871029834701928374019823401;


  pop_frame ()



inline_for_extraction noextract
val test_exp_gen:
     n:snat{ n > 1 }
  -> a:snat{ a < n }
  -> b:snat
  -> Stack unit (requires fun _ -> true) (ensures fun _ _ _ -> true)
let test_exp_gen n a b =
  push_frame();

  //let nLen = normalize_term (nat_bytes_num n) in
  let nLen = 4ul in
  let pow2_i = 4ul in

  assume (v (nat_bytes_num a) <= v nLen);
  assume (v (nat_bytes_num b) <= v nLen);
  assume (v (nat_bytes_num n) <= v nLen);
  [@inline_let]
  let r =  fexp #n a b in
  assume (issnat r);
  assume (v (nat_bytes_num r) <= v nLen);

  let bn_a:lbignum nLen = nat_to_bignum a in
  let bn_b:lbignum nLen = nat_to_bignum b in
  let bn_n:lbignum nLen = nat_to_bignum n in
  let bn_res:lbignum nLen = create nLen (uint 0) in

  let bn_expected:lbignum nLen = nat_to_bignum (normalize_term (fexp #n a b)) in

  admit();
  mod_exp_compact pow2_i bn_n bn_a bn_b bn_res;
  let res = bn_is_equal bn_expected bn_res in
  if res
  then print_strln " * Success"
  else begin
    print_strln " * Failed";
    print_lbignum bn_res;
    print_lbignum bn_expected
  end;
  pop_frame()


val test_exp: unit -> St unit
let test_exp _ =
  C.String.print (C.String.of_literal "Testing exp\n");
  push_frame();

  test_exp_gen 100000000000 0 0;
  test_exp_gen 100000000000 1 0;
  test_exp_gen 100000000000 12345 0;
  test_exp_gen 100000000000 10 1;
  test_exp_gen 100000000000 10 5;
  test_exp_gen 100000000000 100000 5;
//  test_exp_gen 1234123432165873264969873219648712 1;
//  test_exp_gen 1234123432165873264969873219648712 0;
//  test_exp_gen 1234123432165873264969873219648712 2;
//  test_exp_gen 1234123432165873264969873219648712 3;
//  test_exp_gen 1234123432165873264969873219648712 4;
//  test_exp_gen 1234123432165873264969873219648712 5;
//  admit();
//  test_exp_gen
//    111111111111111111111111111111
//    18446744073709551618;
//  test_exp_gen
//    111111111111123123123111111111111111111
//    184467440737095553212351618;
//  test_exp_gen
//    11111111111112312312311111114973210598732098407321111111111111
//    18446744073709555321235160918327501928374098320749182318;

  pop_frame ()


val testBignum: unit -> St unit
let testBignum _ =
  C.String.print (C.String.of_literal "Bignum tests: \n");
  test_printing ();
  test_comp ();
  test_add ();
  test_mult ();
  test_lshift ();
  test_rshift1 ();
  test_pow2 ();
  test_mod ();
  test_exp ();
  C.String.print (C.String.of_literal "Bignum tests are done \n\n")
