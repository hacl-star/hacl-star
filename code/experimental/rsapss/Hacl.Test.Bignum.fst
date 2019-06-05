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

open Hacl.Impl.Bignum

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

val print_verdict:
     #aLen:bn_len
  -> #bLen:bn_len
  -> exp:lbignum aLen
  -> got:lbignum bLen
  -> r:bool
  -> ST unit (requires fun h -> live h exp /\ live h got) (ensures fun h0 _ h1 -> h0 == h1)
let print_verdict #aLen #bLen exp got r =
  if r
  then print_strln " * Success"
  else begin
    print_strln " * Failed";
    print_str "  exp: ";
    print_lbignum exp;
    print_str "  got: ";
    print_lbignum got
  end

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
  -> b:snat
  -> St unit
let test_comp_gen a b =
  push_frame();
  let less_exp = normalize_term (a < b) in
  let eq_exp = normalize_term (a = b) in
  let greater_exp = normalize_term (a > b) in

  let bn_a: lbignum (nat_bytes_num a) = nat_to_bignum_exact a in
  let bn_b: lbignum (nat_bytes_num b) = nat_to_bignum_exact b in

  let less_res = bn_is_less bn_a bn_b in
  let eq_res = bn_is_equal bn_a bn_b in
  let greater_res = bn_is_greater bn_a bn_b in


  let res = (less_res = less_exp && eq_res = eq_exp && greater_res = greater_exp) in
  if res then print_strln " * Success" else print_strln " * Failed";
  pop_frame()

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
  test_comp_gen 0 1;
  test_comp_gen 12345 0;
  test_comp_gen 0 12345;
  test_comp_gen 12345 12345;
  test_comp_gen 100000000000000000000000 100000000000000000000000;
  test_comp_gen 100000000000000000000000 100000000000000000000001;
  test_comp_gen 100000000000000000000001 100000000000000000000000;

  C.String.print (C.String.of_literal "...leading zeroes tests:\n");

  test_eq_repr 0;
  test_eq_repr 1;
  test_eq_repr 100;
  test_eq_repr 10000000000000000000000000;

  pop_frame()

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
val test_add_gen:
     a:snat{issnat (2*a)}
  -> b:snat{b <= a}
  -> Stack unit (requires fun _ -> true) (ensures fun _ _ _ -> true)
let test_add_gen a b =
  push_frame();

  let a_len: size_t = normalize_term (nat_bytes_num a) in
  let b_len: size_t = normalize_term (nat_bytes_num b) in
  nat_bytes_num_range a;
  nat_bytes_num_fit b a;
  let res_len: size_t = a_len +. 1ul in
  snat_order (a+b) (2*a);
  let c_len: size_t = normalize_term (nat_bytes_num (a+b)) in

  let bn_a:lbignum a_len     = nat_to_bignum_exact a in
  let bn_b:lbignum b_len     = nat_to_bignum_exact b in
  let bn_c:lbignum c_len     = nat_to_bignum_exact (normalize_term (a+b)) in
  let bn_res:lbignum res_len = create res_len (uint 0) in

  bn_add_full bn_a bn_b bn_res;
  let res = bn_is_equal bn_c bn_res in
  print_verdict bn_c bn_res res;
  pop_frame()

#reset-options "--z3rlimit 100 --max_fuel 2 --max_ifuel 0"

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

  test_add_gen 0 0;
  test_add_gen 1 0;
  test_add_gen 12345 0;
  test_add_gen 10 1;
  test_add_gen 10 2;
  test_add_gen 25 10;
  test_add_gen 1000 10;
  test_add_gen 100000000000 1;
  test_add_gen 100000000000 2;
  test_add_gen 100000000000 100000000000;


  test_add_gen 18446744073709551615 0;
  test_add_gen 18446744073709551615 1;
  test_add_gen 18446744073709551615 2;
  test_add_gen 18446744073709551615 18446744073709551614;
  test_add_gen 18446744073709551615 18446744073709551615;
  test_add_gen 18446744073709551616 0;
  test_add_gen 18446744073709551616 1;
  test_add_gen 18446744073709551616 2;
  test_add_gen 18446744073709551616 18446744073709551614;
  test_add_gen 18446744073709551616 18446744073709551615;
  test_add_gen 18446744073709551616 18446744073709551616;
  test_add_gen 18446744073709551617 0;
  test_add_gen 18446744073709551617 1;
  test_add_gen 18446744073709551617 2;
  test_add_gen 18446744073709551617 18446744073709551614;
  test_add_gen 18446744073709551617 18446744073709551615;
  test_add_gen 18446744073709551617 18446744073709551616;
  test_add_gen 18446744073709551617 18446744073709551617;


  test_add_gen 1234123432165873264969873219648712 0;
  test_add_gen 1234123432165873264969873219648712 1;
  test_add_gen 1234123432165873264969873219648712 2;
  test_add_gen 1234123432165873264969873219648712 10;
  test_add_gen 1234123432165873264969873219648712 100000;
  test_add_gen 1234123432165873264969873219648712 100000000000;
  test_add_gen 1234123432165873264969873219648712 1000000000000000;
  test_add_gen 1234123432165873264969873219648712 1000000000000000000;
  test_add_gen 1234123432165873264969873219648712 1000000000000000000000;

  pop_frame()

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
val test_mult_gen:
     a:snat
  -> b:snat{issnat (a*b)}
  -> Stack unit (requires fun _ -> true) (ensures fun _ _ _ -> true)
let test_mult_gen a b =
  push_frame();

  let a_len: size_t = normalize_term (nat_bytes_num a) in
  let b_len: size_t = normalize_term (nat_bytes_num b) in
  nat_bytes_num_range a;
  nat_bytes_num_range b;
  let res_len: size_t = (a_len +. b_len) in

  let bn_a:lbignum a_len     = nat_to_bignum_exact a in
  let bn_b:lbignum b_len     = nat_to_bignum_exact b in
  assume (v (nat_bytes_num (a*b)) <= v res_len);
  let bn_c:lbignum res_len   = nat_to_bignum #res_len (normalize_term (a * b)) in
  let bn_res:lbignum res_len = create res_len (uint 0) in

  bn_mul bn_a bn_b bn_res;
  let res = bn_is_equal bn_c bn_res in
  print_verdict bn_c bn_res res;

  pop_frame()

#reset-options

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

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
val test_lshift_gen:
     a:snat
  -> p:nat{p < max_size_t}
  -> Stack unit (requires fun _ -> true) (ensures fun _ _ _ -> true)
let test_lshift_gen a p =
  push_frame();

  let p' = normalize_term (size p) in
  let aLen = normalize_term (nat_bytes_num a) in
  let resLen = aLen +. (p' /. 64ul) +. 1ul in
  assume (v resLen < max_size_t /\ v resLen > 0);

  let bn_a:lbignum aLen = nat_to_bignum a in
  let bn_res:lbignum resLen = create resLen (uint 0) in
  assume (pow2 p * a > 0 /\ issnat (pow2 p * a));
  assume (v (nat_bytes_num (pow2 p * a)) <= v resLen);
  let bn_expected:lbignum resLen =
        nat_to_bignum (normalize_term (pow2 p * a)) in

  bn_lshift bn_a p' bn_res;
  let res = bn_is_equal bn_expected bn_res in
  print_verdict bn_expected bn_res res;
  pop_frame ()

#reset-options

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

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
val test_rshift1_gen:
     a:snat{a>1}
  -> Stack unit (requires fun _ -> true) (ensures fun _ _ _ -> true)
let test_rshift1_gen a =
  push_frame();

  nat_bytes_num_range a;
  let aLen = normalize_term (nat_bytes_num a) in

  let bn_a:lbignum aLen = nat_to_bignum a in
  let bn_res:lbignum aLen = create aLen (uint 0) in
  assert (a/2 > 0 /\ a/2 < a);
  snat_order (a/2) a;
  nat_bytes_num_fit (a/2) a;
  let bn_expected:lbignum aLen = nat_to_bignum (normalize_term (a / 2)) in

  bn_rshift1 bn_a bn_res;
  let res = bn_is_equal bn_expected bn_res in
  print_verdict bn_expected bn_res res;
  pop_frame()

#reset-options

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


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
val test_pow2_gen:
     a:snat{a > 2}
  -> p:nat{p < max_size_t}
  -> Stack unit (requires fun _ -> true) (ensures fun _ _ _ -> true)
let test_pow2_gen a p =
  push_frame();

  let p' = normalize_term (size p) in
  let aLen = normalize_term (nat_bytes_num a) in
  nat_bytes_num_range a;
  let aBits = aLen *. 64ul in

  let bn_a:lbignum aLen = nat_to_bignum a in
  let bn_res:lbignum aLen = create aLen (uint 0) in
  snat_order (fexp #a 2 p) a;
  nat_bytes_num_fit (fexp #a 2 p) a;
  let bn_expected:lbignum aLen = nat_to_bignum (normalize_term (fexp #a 2 p)) in

  assume (v aBits / 64 <= v aLen);

  bn_pow2_mod_n aBits bn_a p' bn_res;
  let res = bn_is_equal bn_expected bn_res in
  print_verdict bn_expected bn_res res;
  pop_frame()

#reset-options

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

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"


inline_for_extraction noextract
val test_mod_gen:
     n:snat{n > 2}
  -> a:snat
  -> Stack unit (requires fun _ -> true) (ensures fun _ _ _ -> true)
let test_mod_gen n (a:nat{issnat a}) =
  push_frame();

  nat_bytes_num_range n;
  nat_bytes_num_range a;
  let aLen:bn_len_strict = normalize_term (nat_bytes_num a) in
  let nLen:bn_len_strict = normalize_term (nat_bytes_num n) in

  let bn_n:lbignum nLen = nat_to_bignum n in
  let bn_a:lbignum aLen = nat_to_bignum a in
  let bn_res:lbignum nLen = create nLen (uint 0) in

  Math.Lemmas.lemma_mod_lt a n;
  assert (a % n < n);
  snat_order (a % n) n;
  nat_bytes_num_fit (a % n) n;
  let bn_expected:lbignum nLen = nat_to_bignum (normalize_term (a % n)) in

  bn_remainder bn_a bn_n bn_res;
  let res = bn_is_equal bn_expected bn_res in
  print_verdict bn_expected bn_res res;
  pop_frame()

#reset-options "--z3rlimit 50 --max_fuel 2 --max_ifuel 0"

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

  test_mod_gen 256 256;
  test_mod_gen 256 511;
  test_mod_gen 256 512;
  test_mod_gen 256 513;
  test_mod_gen 256 1024;
  test_mod_gen 256 1000000;

  test_mod_gen 100000000001 100000000001;

  test_mod_gen 1000000000000000000000000 0;
  test_mod_gen 1000000000000000000000000 1;
  test_mod_gen 1000000000000000000000000 2;
  test_mod_gen 1000000000000000000000000 256;
  test_mod_gen 1000000000000000000000000 1000000000000000000000000;
  test_mod_gen 1000000000000000000000000
      10000001234912034981720349871029834701928374019823401;

  // modulo 2^64-1
  test_mod_gen 18446744073709551615 18446744073709551616;
  test_mod_gen 18446744073709551615 18446744073709551617;
  test_mod_gen 18446744073709551615 18446744073709551615;

  // modulo 2^64
  test_mod_gen 18446744073709551616 18446744073709551616;
  test_mod_gen 18446744073709551616 18446744073709551617;
  test_mod_gen 18446744073709551616 18446744073709551615;

  // modulo 2^64+1
  test_mod_gen 18446744073709551617 18446744073709551616;
  test_mod_gen 18446744073709551617 18446744073709551617;
  test_mod_gen 18446744073709551617 18446744073709551615;


  test_mod_gen 1234123432165873264969873219648712
     243241359213059132408213100000;

  pop_frame ()

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"


inline_for_extraction noextract
val test_mod_ops_gen:
     n:snat{ n > 1 }
  -> a:snat{ a <= n }
  -> b:snat{ b <= n }
  -> Stack unit (requires fun _ -> true) (ensures fun _ _ _ -> true)
let test_mod_ops_gen n a b =
  push_frame();

  nat_bytes_num_range n;
  let nLen:bn_len_strict = normalize_term (nat_bytes_num n) in

  nat_bytes_num_fit a n;
  nat_bytes_num_fit b n;

  let bn_a:lbignum nLen = nat_to_bignum a in
  let bn_b:lbignum nLen = nat_to_bignum b in
  let bn_n:lbignum nLen = nat_to_bignum n in

  let bn_add_res:lbignum nLen = create nLen (uint 0) in
  let bn_mul_res:lbignum nLen = create nLen (uint 0) in

  Math.Lemmas.lemma_mod_lt (a+b) n;
  snat_order ((a+b) % n) n;
  nat_bytes_num_fit ((a+b) % n) n;
  let bn_add_exp:lbignum nLen = nat_to_bignum (normalize_term ((a + b) % n)) in

  Math.Lemmas.lemma_mod_lt (a*b) n;
  snat_order ((a*b) % n) n;
  nat_bytes_num_fit ((a*b) % n) n;
  let bn_mul_exp:lbignum nLen = nat_to_bignum (normalize_term ((a * b) % n)) in


  bn_modular_add bn_n bn_a bn_b bn_add_res;
  bn_modular_mul bn_n bn_a bn_b bn_mul_res;

  let res_add = bn_is_equal bn_add_exp bn_add_res in
  print_verdict bn_add_exp bn_add_res res_add;

  let res_mul = bn_is_equal bn_mul_exp bn_mul_res in
  print_verdict bn_mul_exp bn_mul_res res_mul;

  pop_frame()

#reset-options "--z3rlimit 100 --max_fuel 2 --max_ifuel 0"

val test_mod_ops: unit -> St unit
let test_mod_ops _ =
  C.String.print (C.String.of_literal "Testing mod_ops\n");
  push_frame();

  test_mod_ops_gen 100000000001 0 0;
  test_mod_ops_gen 100000000001 1 0;
  test_mod_ops_gen 100000000001 12345 0;
  test_mod_ops_gen 100000000001 10 1;
  test_mod_ops_gen 100000000001 10 2;
  test_mod_ops_gen 100000000001 10 25;
  test_mod_ops_gen 100000000001 10 1000;
  test_mod_ops_gen 100000000001 100000000000 1; //broken one
  test_mod_ops_gen 100000000001 100000000000 2;
  test_mod_ops_gen 100000000001 100000000000 100000000000;


  test_mod_ops_gen 18446744073709551615 18446744073709551614 0;
  test_mod_ops_gen 18446744073709551615 18446744073709551614 1;
  test_mod_ops_gen 18446744073709551615 18446744073709551614 2;
  test_mod_ops_gen 18446744073709551615 18446744073709551614 18446744073709551614;

  test_mod_ops_gen 18446744073709551616 18446744073709551615 0;
  test_mod_ops_gen 18446744073709551616 18446744073709551615 1;
  test_mod_ops_gen 18446744073709551616 18446744073709551615 2;
  test_mod_ops_gen 18446744073709551616 18446744073709551615 18446744073709551616;
  test_mod_ops_gen 18446744073709551616 18446744073709551616 0;
  test_mod_ops_gen 18446744073709551616 18446744073709551616 1;
  test_mod_ops_gen 18446744073709551616 18446744073709551616 2;
  test_mod_ops_gen 18446744073709551616 18446744073709551616 18446744073709551616;

  test_mod_ops_gen 18446744073709551617 18446744073709551615 0;
  test_mod_ops_gen 18446744073709551617 18446744073709551615 1;
  test_mod_ops_gen 18446744073709551617 18446744073709551615 2;
  test_mod_ops_gen 18446744073709551617 18446744073709551615 18446744073709551615;
  test_mod_ops_gen 18446744073709551617 18446744073709551616 0;
  test_mod_ops_gen 18446744073709551617 18446744073709551616 1;
  test_mod_ops_gen 18446744073709551617 18446744073709551616 2;
  test_mod_ops_gen 18446744073709551617 18446744073709551616 18446744073709551615;
  test_mod_ops_gen 18446744073709551617 18446744073709551616 18446744073709551616;
  test_mod_ops_gen 18446744073709551617 18446744073709551617 0;
  test_mod_ops_gen 18446744073709551617 18446744073709551617 1;
  test_mod_ops_gen 18446744073709551617 18446744073709551617 2;
  test_mod_ops_gen 18446744073709551617 18446744073709551617 18446744073709551617;

  test_mod_ops_gen 1234123432165873264969873219648712 0 0;
  test_mod_ops_gen 1234123432165873264969873219648712 1 0;
  test_mod_ops_gen 1234123432165873264969873219648712 12345 0;
  test_mod_ops_gen 1234123432165873264969873219648712 10 1;
  test_mod_ops_gen 1234123432165873264969873219648712 10 2;
  test_mod_ops_gen 1234123432165873264969873219648712 10 25;
  test_mod_ops_gen 1234123432165873264969873219648712 10 1000;
  test_mod_ops_gen 1234123432165873264969873219648712 100000 10000000000000000000;


  test_mod_ops_gen 1234123432165873264969873219648712
     243241359213059132408213100000 2;
  test_mod_ops_gen 1234123432165873264969873219648712
     243241359213059132408213100000 10;
  test_mod_ops_gen 1234123432165873264969873219648712
     243241359213059132408213100000 100000;
  test_mod_ops_gen 1234123432165873264969873219648712
     243241359213059132408213100000 100000000000;
  test_mod_ops_gen 1234123432165873264969873219648712
     243241359213059132408213100000 1000000000000000;
  test_mod_ops_gen 1234123432165873264969873219648712
     243241359213059132408213100000 1000000000000000000;
  test_mod_ops_gen 1234123432165873264969873219648712
     243241359213059132408213100000 10000000000000000000;

  pop_frame ()


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
val test_exp_gen:
     n:snat{ n > 1 }
  -> a:snat{ a < n }
  -> exp:snat
  -> Stack unit (requires fun _ -> true) (ensures fun _ _ _ -> true)
let test_exp_gen n a exp =
  push_frame();

  nat_bytes_num_range n;
  let nLen:bn_len_strict = normalize_term (nat_bytes_num n) in
  let expLen:bn_len_strict = normalize_term (nat_bytes_num exp) in

  nat_bytes_num_fit a n;

  let bn_a:lbignum nLen = nat_to_bignum a in
  let bn_n:lbignum nLen = nat_to_bignum n in
  let bn_exp:lbignum expLen = nat_to_bignum exp in
  let bn_res:lbignum nLen = create nLen (uint 0) in

  snat_order (fexp #n a exp) n;
  nat_bytes_num_fit (fexp #n a exp) n;
  let bn_expected:lbignum nLen = nat_to_bignum (normalize_term (fexp #n a exp)) in

  let h = FStar.HyperStack.ST.get () in
  nat_bytes_num_range n;
  bn_modular_exp bn_n bn_a bn_exp bn_res;
  let res = bn_is_equal bn_expected bn_res in
  print_verdict bn_expected bn_res res;
  pop_frame()

#reset-options "--z3rlimit 100 --max_fuel 2 --max_ifuel 0"

val test_exp: unit -> St unit
let test_exp _ =
  C.String.print (C.String.of_literal "Testing exp\n");
  push_frame();

  test_exp_gen 100000000000 0 0;
  test_exp_gen 100000000000 1 0;
  test_exp_gen 100000000000 12345 0;
  test_exp_gen 100000000000 10 1;
  test_exp_gen 100000000000 10 2;
  test_exp_gen 100000000000 10 25;
  test_exp_gen 100000000000 10 1000;
  test_exp_gen 100000000000 100000 10000000000000000000;
  test_exp_gen 100000000001 100000000000 1;
  test_exp_gen 100000000001 100000000000 2;
  test_exp_gen 100000000001 100000000000 10000000000000000000;


  test_exp_gen 1234123432165873264969873219648712 0 0;
  test_exp_gen 1234123432165873264969873219648712 1 0;
  test_exp_gen 1234123432165873264969873219648712 12345 0;
  test_exp_gen 1234123432165873264969873219648712 10 1;
  test_exp_gen 1234123432165873264969873219648712 10 2;
  test_exp_gen 1234123432165873264969873219648712 10 25;
  test_exp_gen 1234123432165873264969873219648712 10 1000;
  test_exp_gen 1234123432165873264969873219648712 100000 10000000000000000000;


  test_exp_gen 1234123432165873264969873219648712
     243241359213059132408213100000 1;
  test_exp_gen 1234123432165873264969873219648712
     243241359213059132408213100000 2;
  test_exp_gen 1234123432165873264969873219648712
     243241359213059132408213100000 10;
  test_exp_gen 1234123432165873264969873219648712
     243241359213059132408213100000 100000;
  test_exp_gen 1234123432165873264969873219648712
     243241359213059132408213100000 100000000000;
  test_exp_gen 1234123432165873264969873219648712
     243241359213059132408213100000 1000000000000000;
  test_exp_gen 1234123432165873264969873219648712
     243241359213059132408213100000 1000000000000000000;
  test_exp_gen 1234123432165873264969873219648712
     243241359213059132408213100000 10000000000000000000;
  test_exp_gen 12341234321658128370192373264969873219648712
     2432413592130591324082131012038720000 100000000000000000170987102983470918200;

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
  test_mod_ops ();
  test_exp ();
  C.String.print (C.String.of_literal "Bignum tests are done \n\n")
