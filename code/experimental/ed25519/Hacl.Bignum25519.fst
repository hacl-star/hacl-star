module Hacl.Bignum25519

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

module BN = Hacl.Impl.Curve25519.Field51

#reset-options "--max_fuel 0"

inline_for_extraction noextract
let mask_51 = u64 0x7ffffffffffff

let make_u64_5 b s0 s1 s2 s3 s4 =
  b.(0ul) <- s0;
  b.(1ul) <- s1;
  b.(2ul) <- s2;
  b.(3ul) <- s3;
  b.(4ul) <- s4

let make_u64_10 b s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 =
  b.(0ul) <- s0;
  b.(1ul) <- s1;
  b.(2ul) <- s2;
  b.(3ul) <- s3;
  b.(4ul) <- s4;
  b.(5ul) <- s5;
  b.(6ul) <- s6;
  b.(7ul) <- s7;
  b.(8ul) <- s8;
  b.(9ul) <- s9

let make_u128_9 b s0 s1 s2 s3 s4 s5 s6 s7 s8 =
  b.(0ul) <- s0;
  b.(1ul) <- s1;
  b.(2ul) <- s2;
  b.(3ul) <- s3;
  b.(4ul) <- s4;
  b.(5ul) <- s5;
  b.(6ul) <- s6;
  b.(7ul) <- s7;
  b.(8ul) <- s8

let make_zero b =
  b.(0ul) <- u64 0;
  b.(1ul) <- u64 0;
  b.(2ul) <- u64 0;
  b.(3ul) <- u64 0;
  b.(4ul) <- u64 0

let make_one b =
  b.(0ul) <- u64 1;
  b.(1ul) <- u64 0;
  b.(2ul) <- u64 0;
  b.(3ul) <- u64 0;
  b.(4ul) <- u64 0

let fsum a b = admit();
  BN.fadd a a b

let fdifference a b = admit();
  BN.fsub a b a

inline_for_extraction noextract
val fcontract_first_carry_pass:
  input:felem ->
  Stack unit
    (requires fun h -> live h input)
    (ensures  fun h0 _ h1 -> modifies (loc input) h0 h1)
let fcontract_first_carry_pass input =
  let t0 = input.(0ul) in
  let t1 = input.(1ul) in
  let t2 = input.(2ul) in
  let t3 = input.(3ul) in
  let t4 = input.(4ul) in
  let t1' = t1 +. (t0 >>. 51ul) in
  let t0' = t0 &. mask_51 in
  let t2' = t2 +. (t1' >>. 51ul) in
  let t1'' = t1' &. mask_51 in
  let t3' = t3 +. (t2' >>. 51ul) in
  let t2'' = t2' &. mask_51 in
  let t4' = t4 +. (t3' >>. 51ul) in
  let t3'' = t3' &. mask_51 in
  make_u64_5 input  t0' t1'' t2'' t3'' t4'

inline_for_extraction noextract
val carry_top:
  b:felem ->
  Stack unit
  (requires fun h -> live h b)
  (ensures  fun h0 _ h1 -> modifies (loc b) h0 h1)
let carry_top b =
  let b4 = b.(4ul) in
  let b0 = b.(0ul) in
  let b4' = b4 &. mask_51 in
  let b0' = b0 +. u64 19 *. (b4 >>. 51ul) in
  b.(4ul) <- b4';
  b.(0ul) <- b0'

inline_for_extraction noextract
val carry_0_to_1:
  output:felem ->
  Stack unit
    (requires fun h -> live h output)
    (ensures  fun h0 _ h1 -> modifies (loc output) h0 h1)
let carry_0_to_1 output =
  let i0 = output.(0ul) in
  let i1 = output.(1ul) in
  let i0' = i0 &. mask_51 in
  let i1' = i1 +. (i0 >>. 51ul) in
  output.(0ul) <- i0';
  output.(1ul) <- i1'

inline_for_extraction noextract
val reduce_513_:
  a:felem ->
  Stack unit
    (requires fun h -> live h a)
    (ensures  fun h0 _ h1 -> modifies (loc a) h0 h1)
let reduce_513_ a =
  fcontract_first_carry_pass a;
  carry_top a;
  carry_0_to_1 a

let reduce_513 a =
  reduce_513_ a

let fdifference_reduced a b =
  fdifference a b;
  reduce_513 a

inline_for_extraction noextract
val fcontract_first_carry_full:
  input:felem ->
  Stack unit
    (requires fun h -> live h input)
    (ensures  fun h0 _ h1 -> modifies (loc input) h0 h1)
let fcontract_first_carry_full input =
  fcontract_first_carry_pass input;
  carry_top input

inline_for_extraction noextract
val fcontract_second_carry_pass:
  input:felem ->
  Stack unit
    (requires fun h -> live h input)
    (ensures  fun h0 _ h1 -> modifies (loc input) h0 h1)
let fcontract_second_carry_pass input =
  let t0 = input.(0ul) in
  let t1 = input.(1ul) in
  let t2 = input.(2ul) in
  let t3 = input.(3ul) in
  let t4 = input.(4ul) in
  let t1' = t1 +. (t0 >>. 51ul) in
  let t0' = t0 &. mask_51 in
  let t2' = t2 +. (t1' >>. 51ul) in
  let t1'' = t1' &. mask_51 in
  let t3' = t3 +. (t2' >>. 51ul) in
  let t2'' = t2' &. mask_51 in
  let t4' = t4 +. (t3' >>. 51ul) in
  let t3'' = t3' &. mask_51 in
  make_u64_5 input t0' t1'' t2'' t3'' t4'

inline_for_extraction noextract
val fcontract_second_carry_full:
  input:felem ->
  Stack unit
    (requires fun h -> live h input)
    (ensures fun h0 _ h1 -> modifies (loc input) h0 h1)
let fcontract_second_carry_full input =
  fcontract_second_carry_pass input;
  carry_top input;
  carry_0_to_1 input

inline_for_extraction noextract
val fcontract_trim:
  input:felem ->
  Stack unit
    (requires fun h -> live h input)
    (ensures  fun h0 _ h1 -> modifies (loc input) h0 h1)
let fcontract_trim input =
  let a0 = input.(0ul) in
  let a1 = input.(1ul) in
  let a2 = input.(2ul) in
  let a3 = input.(3ul) in
  let a4 = input.(4ul) in
  let m0 = gte_mask a0 (u64 0x7ffffffffffed) in
  let m1 = eq_mask a1 (u64 0x7ffffffffffff) in
  let m2 = eq_mask a2 (u64 0x7ffffffffffff) in
  let m3 = eq_mask a3 (u64 0x7ffffffffffff) in
  let m4 = eq_mask a4 (u64 0x7ffffffffffff) in
  let mask = m0 &. m1 &. m2 &. m3 &. m4 in
  let a0' = a0 -. (mask &. u64 0x7ffffffffffed) in
  let a1' = a1 -. (mask &. u64 0x7ffffffffffff) in
  let a2' = a2 -. (mask &. u64 0x7ffffffffffff) in
  let a3' = a3 -. (mask &. u64 0x7ffffffffffff) in
  let a4' = a4 -. (mask &. u64 0x7ffffffffffff) in
  make_u64_5 input a0' a1' a2' a3' a4'

inline_for_extraction noextract
val reduce_:
  input:felem ->
  Stack unit
    (requires fun h -> live h input)
    (ensures  fun h0 _ h1 -> modifies (loc input) h0 h1)
let reduce_ out =
  fcontract_first_carry_full out;
  fcontract_second_carry_full out;
  fcontract_trim out

let fmul output input input2 = admit();
  BN.fmul output input input2

let times_2 out a =
  let a0 = a.(0ul) in
  let a1 = a.(1ul) in
  let a2 = a.(2ul) in
  let a3 = a.(3ul) in
  let a4 = a.(4ul) in
  let o0 = u64 2 *. a0 in
  let o1 = u64 2 *. a1 in
  let o2 = u64 2 *. a2 in
  let o3 = u64 2 *. a3 in
  let o4 = u64 2 *. a4 in
  make_u64_5 out o0 o1 o2 o3 o4

let times_d out a =
  push_frame();
  let d = create 5ul (u64 0) in
  d.(0ul) <- u64 0x00034dca135978a3;
  d.(1ul) <- u64 0x0001a8283b156ebd;
  d.(2ul) <- u64 0x0005e7a26001c029;
  d.(3ul) <- u64 0x000739c663a03cbb;
  d.(4ul) <- u64 0x00052036cee2b6ff;
  fmul out d a;
  pop_frame()

let times_2d out a =
  push_frame();
  let d2 = create 5ul (u64 0) in
  d2.(0ul) <- u64 0x00069b9426b2f159;
  d2.(1ul) <- u64 0x00035050762add7a;
  d2.(2ul) <- u64 0x0003cf44c0038052;
  d2.(3ul) <- u64 0x0006738cc7407977;
  d2.(4ul) <- u64 0x0002406d9dc56dff;
  fmul out a d2;
  pop_frame()

let fsquare out a = admit();
  BN.fsqr out a

inline_for_extraction noextract
val fsquare_times_:
    output:felem
  -> input:felem
  -> tmp:lbuffer uint128 5ul
  -> count:size_t{v count > 0} ->
  Stack unit
    (requires fun h ->
      live h output /\ live h input /\ live h tmp /\
      disjoint input tmp /\ disjoint output tmp)
    (ensures  fun h0 _ h1 -> modifies (loc output |+| loc tmp) h0 h1)
let fsquare_times_ output input tmp count = admit();
  Hacl.Curve25519.Finv.Field51.fsquare_times_51 output input tmp count

let fsquare_times output input count =
  push_frame();
  let tmp = create 5ul (u128 0) in
  fsquare_times_ output input tmp count;
  pop_frame()

let fsquare_times_inplace output count =
  push_frame();
  let tmp = create 5ul (u128 0) in
  fsquare_times_ output output tmp count;
  pop_frame()

let inverse out a =
  push_frame();
  let tmp = create 10ul (u128 0) in
  admit();
  Hacl.Curve25519.Finv.Field51.finv_51 out a tmp;
  pop_frame()

let reduce out = reduce_ out

let load_51 output input =
  let i0 = uint_from_bytes_le (sub input 0ul 8ul) in
  let i1 = uint_from_bytes_le (sub input 6ul 8ul) in
  let i2 = uint_from_bytes_le (sub input 12ul 8ul) in
  let i3 = uint_from_bytes_le (sub input 19ul 8ul) in
  let i4 = uint_from_bytes_le (sub input 24ul 8ul) in
  let output0 = (i0         ) &. mask_51 in
  let output1 = (i1 >>. 3ul ) &. mask_51 in
  let output2 = (i2 >>. 6ul ) &. mask_51 in
  let output3 = (i3 >>. 1ul ) &. mask_51 in
  let output4 = (i4 >>. 12ul) &. mask_51 in
  make_u64_5 output output0 output1 output2 output3 output4

val store_4:
  output:lbuffer uint8 32ul ->
  v1:uint64 -> v2:uint64 -> v3:uint64 -> v4:uint64 ->
  Stack unit
    (requires fun h -> live h output)
    (ensures  fun h0 _ h1 -> modifies (loc output) h0 h1)
let store_4 output v0 v1 v2 v3 =
  let b0 = sub output 0ul  8ul in
  let b1 = sub output 8ul  8ul in
  let b2 = sub output 16ul 8ul in
  let b3 = sub output 24ul 8ul in
  uint_to_bytes_le b0 v0;
  uint_to_bytes_le b1 v1;
  uint_to_bytes_le b2 v2;
  uint_to_bytes_le b3 v3

let store_51 output input =
  let t0 = input.(0ul) in
  let t1 = input.(1ul) in
  let t2 = input.(2ul) in
  let t3 = input.(3ul) in
  let t4 = input.(4ul) in
  let o0 = (t1 <<. 51ul) |. t0 in
  let o1 = (t2 <<. 38ul) |. (t1 >>. 13ul) in
  let o2 = (t3 <<. 25ul) |. (t2 >>. 26ul) in
  let o3 = (t4 <<. 12ul) |. (t3 >>. 39ul) in
  store_4 output o0 o1 o2 o3
