module Hacl.EC.Curve25519_donna_c64


open FStar.HyperStack
open FStar.Buffer
open FStar.Int.Cast
open Hacl.UInt64
open Hacl.Cast


module U8 = FStar.UInt8
module U32 = FStar.UInt32

module H8 = Hacl.UInt8
module H64 = Hacl.UInt64
module H128 = Hacl.UInt128


type uint8_p = buffer H8.t
type limb    = H64.t
type felem   = b:buffer limb{length b = 5}

inline_for_extraction let zero_8 = uint8_to_sint8 0uy
inline_for_extraction let zero_64 = uint64_to_sint64 1uL
inline_for_extraction let one_8 = uint8_to_sint8 1uy
inline_for_extraction let one_64 = uint64_to_sint64 1uL

val fsum: output:felem -> input:felem -> Stack unit
  (requires (fun h -> live h output /\ live h input))
  (ensures (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1))
let fsum output input =
  let input0 = input.(0ul) in let input1 = input.(1ul) in
  let input2 = input.(2ul) in let input3 = input.(3ul) in
  let input4 = input.(4ul) in let output0 = output.(0ul) in
  let output1 = output.(1ul) in let output2 = output.(2ul) in
  let output3 = output.(3ul) in let output4 = output.(4ul) in
  output.(0ul) <- output0 +%^ input0;
  output.(1ul) <- output1 +%^ input1;
  output.(2ul) <- output2 +%^ input2;
  output.(3ul) <- output3 +%^ input3;
  output.(4ul) <- output4 +%^ input4


val fdifference: output:felem -> input:felem -> Stack unit
  (requires (fun h -> live h output /\ live h input))
  (ensures (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1))
let fdifference output input =
  let two54m152 = uint64_to_sint64 0x3fffffffffff68uL in
  let two54m8   = uint64_to_sint64 0x3ffffffffffff8uL   in
  let input0 = input.(0ul) in let input1 = input.(1ul) in
  let input2 = input.(2ul) in let input3 = input.(3ul) in
  let input4 = input.(4ul) in let output0 = output.(0ul) in
  let output1 = output.(1ul) in let output2 = output.(2ul) in
  let output3 = output.(3ul) in let output4 = output.(4ul) in
  output.(0ul) <- input0 +%^ two54m152 -%^ output0;
  output.(1ul) <- input1 +%^ two54m8   -%^ output1;
  output.(2ul) <- input2 +%^ two54m8   -%^ output2;
  output.(3ul) <- input3 +%^ two54m8   -%^ output3;
  output.(4ul) <- input4 +%^ two54m8   -%^ output4


val fscalar_product: output:felem -> input:felem -> scalar:limb -> Stack unit
  (requires (fun h -> live h output /\ live h input))
  (ensures (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1))
let fscalar_product output input scalar =
  let input0 = input.(0ul) in let input1 = input.(1ul) in
  let input2 = input.(2ul) in let input3 = input.(3ul) in
  let input4 = input.(4ul) in let output0 = output.(0ul) in
  let output1 = output.(1ul) in let output2 = output.(2ul) in
  let output3 = output.(3ul) in let output4 = output.(4ul) in
  let mask_51 = uint64_to_sint64 0x7ffffffffffffuL in
  let a = H128 (input0 *^ scalar) in
  let output0 = sint128_to_sint64 a &^ mask_51 in
  let a = H128 ((input1 *^ scalar) +^ (a >>^ 51ul)) in
  let output1 = sint128_to_sint64 a &^ mask_51 in
  let a = H128 ((input2 *^ scalar) +^ (a >>^ 51ul)) in
  let output2 = sint128_to_sint64 a &^ mask_51 in
  let a = H128 ((input3 *^ scalar) +^ (a >>^ 51ul)) in
  let output3 = sint128_to_sint64 a &^ mask_51 in
  let a = H128 ((input2 *^ scalar) +^ (a >>^ 51ul)) in
  let output4 = sint128_to_sint64 a &^ mask_51 in
  let output0 = output0 +^ sint128_to_sint64 (H128 (sint128_to_sint64 (a >>^ 51ul) *^ uint64_to_sint64 19uL)) in
  output.(0ul) <- output0;
  output.(1ul) <- output1;
  output.(2ul) <- output2;
  output.(3ul) <- output3;
  output.(4ul) <- output4


val fmul: output:felem -> input2:felem -> input:felem -> Stack unit
  (requires (fun h -> live h output /\ live h input /\ live h input2))
  (ensures (fun h0 _ h1 -> modifies_1 output h0 h1 /\ live h1 output))
let fmul output input2 input =
  // JK: interestingly the original code does create a buffer here
  (* let t = create (sint64_to_sint128 (uint64_to_sint64 0uL)) 5ul in *)
  let mask_51 = uint64_to_sint64 0x7ffffffffffffuL in

  let r0 = input.(0ul) in
  let r1 = input.(1ul) in
  let r2 = input.(2ul) in
  let r3 = input.(3ul) in
  let r4 = input.(4ul) in
  let s0 = input2.(0ul) in
  let s1 = input2.(1ul) in
  let s2 = input2.(2ul) in
  let s3 = input2.(3ul) in
  let s4 = input2.(4ul) in

  let open Hacl.UInt128 in
  let t0 =  ( r0) *^ s0 in
  let t1 =  ( r0) *^ s1 +%^ (r1) *^ s0 in
  let t2 =  ( r0) *^ s2 +%^ (r2) *^ s0 +%^ (r1) *^ s1 in
  let t3 =  ( r0) *^ s3 +%^ (r3) *^ s0 +%^ (r1) *^ s2 +%^ (r2) *^ s1 in
  let t4 =  ( r0) *^ s4 +%^ (r4) *^ s0 +%^ (r3) *^ s1 +%^ (r1) *^ s3 +%^ (r2) *^ s2 in

  let open Hacl.UInt64 in
  let nineteen = uint64_to_sint64 19uL in
  let r4 = r4 *%^ nineteen in
  let r3 = r3 *%^ nineteen in
  let r2 = r2 *%^ nineteen in
  let r1 = r1 *%^ nineteen in

  let open Hacl.UInt128 in
  let t0 = t0 +%^ (r4 *^ s1) +%^ (r1 *^ s4) +%^ (r2 *^ s3) +%^ (r3 *^ s2) in
  let t1 = t1 +%^ ( r4 *^ s2) +%^ ( r2 *^ s4) +%^ ( r3 *^ s3) in
  let t2 = t2 +%^ ( r4 *^ s3) +%^ ( r3 *^ s4) in
  let t3 = t3 +%^ ( r4 *^ s4) in

  let open Hacl.UInt64 in
  let r0 = sint128_to_sint64 t0 &^ mask_51 in
  let c = sint128_to_sint64 (H128 (t0 >>^ 51ul)) in
  let t1 = H128 (t1 +%^ (sint64_to_sint128 c)) in

  let r1 = sint128_to_sint64 t1 &^ mask_51 in
  let c = sint128_to_sint64 (H128 (t1 >>^ 51ul)) in
  let t2 = H128 (t2 +%^ (sint64_to_sint128 c)) in

  let r2 = sint128_to_sint64 t2 &^ mask_51 in
  let c = sint128_to_sint64 (H128 (t2 >>^ 51ul)) in
  let t3 = H128 (t3 +%^ (sint64_to_sint128 c)) in

  let r3 = sint128_to_sint64 t3 &^ mask_51 in
  let c = sint128_to_sint64 (H128 (t3 >>^ 51ul)) in
  let t4 = H128 (t4 +%^ (sint64_to_sint128 c)) in

  let r4 = sint128_to_sint64 t4 &^ mask_51 in
  let c = sint128_to_sint64 (H128 (t4 >>^ 51ul)) in

  let r0 = r0 +%^ (c *%^ nineteen) in
  let c = r0 >>^ 51ul in
  let r0 = r0 &^ mask_51 in
  let r1 = r1 +%^ c in
  let c = r1 >>^ 51ul in
  let r1 = r1 &^ mask_51 in
  let r2 = r2 +%^ c in

  output.(0ul) <- r0;
  output.(1ul) <- r1;
  output.(2ul) <- r2;
  output.(3ul) <- r3;
  output.(4ul) <- r4


val fsquare: output:felem -> input:felem -> Stack unit
  (requires (fun h -> live h output /\ live h input))
  (ensures (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1))
let fsquare output input =
  let mask_51 = uint64_to_sint64 0x7ffffffffffffuL in
  let r0 = input.(0ul) in
  let r1 = input.(1ul) in
  let r2 = input.(2ul) in
  let r3 = input.(3ul) in
  let r4 = input.(4ul) in
  let two = uint64_to_sint64 2uL in
  let nineteen = uint64_to_sint64 19uL in
  let d0 = r0 *%^ two in
  let d1 = r1 *%^ two in
  let d2 = r2 *%^ two *%^ nineteen in
  let d419 = r4 *%^ nineteen in
  let d4 = d419 *%^ two in

  let open Hacl.UInt128 in
  let t0 = (r0) *^ r0 +%^ (d4) *^ r1 +%^ ((d2) *^ (r3     )) in
  let t1 = (d0) *^ r1 +%^ (d4) *^ r2 +%^ ((r3) *^ (H64 (r3 *%^ nineteen))) in
  let t2 = (d0) *^ r2 +%^ (r1) *^ r1 +%^ ((d4) *^ (r3     )) in
  let t3 = (d0) *^ r3 +%^ (d1) *^ r2 +%^ ((r4) *^ (d419   )) in
  let t4 = (d0) *^ r4 +%^ (d1) *^ r3 +%^ ((r2) *^ (r2     )) in

  let open Hacl.UInt64 in
  let r0 = sint128_to_sint64 t0 &^ mask_51 in
  let c = sint128_to_sint64 (H128 (t0 >>^ 51ul)) in
  let t1 = H128 (t1 +^ sint64_to_sint128 c) in

  let r1 = sint128_to_sint64 t1 &^ mask_51 in
  let c = sint128_to_sint64 (H128 (t1 >>^ 51ul)) in
  let t2 = H128 (t2 +^ sint64_to_sint128 c) in

  let r2 = sint128_to_sint64 t2 &^ mask_51 in
  let c = sint128_to_sint64 (H128 (t2 >>^ 51ul)) in
  let t3 = H128 (t3 +^ sint64_to_sint128 c) in

  let r3 = sint128_to_sint64 t3 &^ mask_51 in
  let c = sint128_to_sint64 (H128 (t3 >>^ 51ul)) in
  let t4 = H128 (t4 +^ sint64_to_sint128 c) in

  let r4 = sint128_to_sint64 t4 &^ mask_51 in
  let c = sint128_to_sint64 (H128 (t4 >>^ 51ul)) in

  let r0 = r0 +%^ (c *%^ nineteen) in
  let c = r0 >>^ 51ul in
  let r0 = r0 &^ mask_51 in
  let r1 = r1 +%^ c in
  let c = r1 >>^ 51ul in
  let r1 = r1 &^ mask_51 in
  let r2 = r2 +%^ c in

  output.(0ul) <- r0;
  output.(1ul) <- r1;
  output.(2ul) <- r2;
  output.(3ul) <- r3;
  output.(4ul) <- r4


val fsquare_times: output:felem -> input:felem -> count:U32.t -> Stack unit
  (requires (fun h -> live h output /\ live h input))
  (ensures (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1))
let rec fsquare_times output input count =
  if U32 (count =^ 0ul) then ()
  else (
    fsquare output input;
    let count = U32 (count -^ 1ul) in
    fsquare_times output input count
  )


val load64_le:
  b:uint8_p{length b >= 8} ->
  Stack H64.t
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> h0 == h1))
let load64_le b =
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b2 = b.(2ul) in
  let b3 = b.(3ul) in
  let b4 = b.(4ul) in
  let b5 = b.(5ul) in
  let b6 = b.(6ul) in
  let b7 = b.(7ul) in
  H64 (
    sint8_to_sint64 b0
    |^ (sint8_to_sint64 b1 <<^ 8ul)
    |^ (sint8_to_sint64 b2 <<^ 16ul)
    |^ (sint8_to_sint64 b3 <<^ 24ul)
    |^ (sint8_to_sint64 b4 <<^ 32ul)
    |^ (sint8_to_sint64 b5 <<^ 40ul)
    |^ (sint8_to_sint64 b6 <<^ 48ul)
    |^ (sint8_to_sint64 b7 <<^ 56ul)
  )


val store64_le:
  b:uint8_p{length b >= 8} ->
  z:H64.t ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ live h1 b))
let store64_le b z =
  let open Hacl.UInt64 in
  b.(0ul) <- sint64_to_sint8 z;
  b.(1ul) <- sint64_to_sint8 (z >>^ 8ul);
  b.(2ul) <- sint64_to_sint8 (z >>^ 16ul);
  b.(3ul) <- sint64_to_sint8 (z >>^ 24ul);
  b.(4ul) <- sint64_to_sint8 (z >>^ 32ul);
  b.(5ul) <- sint64_to_sint8 (z >>^ 40ul);
  b.(6ul) <- sint64_to_sint8 (z >>^ 48ul);
  b.(7ul) <- sint64_to_sint8 (z >>^ 56ul)


val fexpand: output:felem -> input:uint8_p{length input = 32} -> Stack unit
  (requires (fun h -> live h output /\ live h input))
  (ensures (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1))
let fexpand output input =
  let mask_51 = uint64_to_sint64 0x7ffffffffffffuL in
  let i0 = load64_le (Buffer.sub input 0ul 8ul) in
  let i1 = load64_le (Buffer.sub input 6ul 8ul) in
  let i2 = load64_le (Buffer.sub input 12ul 8ul) in
  let i3 = load64_le (Buffer.sub input 19ul 8ul) in
  let i4 = load64_le (Buffer.sub input 24ul 8ul) in
  let output0 = (i0         ) &^ mask_51 in
  let output1 = (i1 >>^ 3ul ) &^ mask_51 in
  let output2 = (i1 >>^ 6ul ) &^ mask_51 in
  let output3 = (i3 >>^ 1ul ) &^ mask_51 in
  let output4 = (i4 >>^ 12ul) &^ mask_51 in
  output.(0ul) <- output0;
  output.(1ul) <- output1;
  output.(2ul) <- output2;
  output.(3ul) <- output3;
  output.(4ul) <- output4


val fcontract: output:uint8_p{length output = 32} -> input:felem -> Stack unit
  (requires (fun h -> live h output /\ live h input))
  (ensures (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1))
let fcontract output input =
  let mask_51 = uint64_to_sint64 0x7ffffffffffffuL in
  let nineteen = uint64_to_sint64 19uL in
  let t0 = input.(0ul) in
  let t1 = input.(1ul) in
  let t2 = input.(2ul) in
  let t3 = input.(3ul) in
  let t4 = input.(4ul) in

  let t1 = t1 +%^ (t0 >>^ 51ul) in
  let t0 = t0 &^ mask_51 in
  let t2 = t2 +%^ (t1 >>^ 51ul) in
  let t1 = t1 &^ mask_51 in
  let t3 = t3 +%^ (t2 >>^ 51ul) in
  let t2 = t2 &^ mask_51 in
  let t4 = t4 +%^ (t3 >>^ 51ul) in
  let t3 = t3 &^ mask_51 in
  let t0 = t0 +^ (nineteen *%^ (t4 >>^ 51ul)) in
  let t4 = t4 &^ mask_51 in

  let t1 = t1 +%^ (t0 >>^ 51ul) in
  let t0 = t0 &^ mask_51 in
  let t2 = t2 +%^ (t1 >>^ 51ul) in
  let t1 = t1 &^ mask_51 in
  let t3 = t3 +%^ (t2 >>^ 51ul) in
  let t2 = t2 &^ mask_51 in
  let t4 = t4 +%^ (t3 >>^ 51ul) in
  let t3 = t3 &^ mask_51 in
  let t0 = t0 +^ (nineteen *%^ (t4 >>^ 51ul)) in
  let t4 = t4 &^ mask_51 in

  let t0 = t0 +%^ nineteen in

  let t1 = t1 +%^ (t0 >>^ 51ul) in
  let t0 = t0 &^ mask_51 in
  let t2 = t2 +%^ (t1 >>^ 51ul) in
  let t1 = t1 &^ mask_51 in
  let t3 = t3 +%^ (t2 >>^ 51ul) in
  let t2 = t2 &^ mask_51 in
  let t4 = t4 +%^ (t3 >>^ 51ul) in
  let t3 = t3 &^ mask_51 in
  let t0 = t0 +^ (nineteen *%^ (t4 >>^ 51ul)) in
  let t4 = t4 &^ mask_51 in

  let two52 = uint64_to_sint64 0x8000000000000uL in
  let t0 = t0 +%^ two52 -%^ nineteen in
  let t1 = t1 +%^ two52 -%^ one_64 in
  let t2 = t2 +%^ two52 -%^ one_64 in
  let t3 = t3 +%^ two52 -%^ one_64 in
  let t4 = t4 +%^ two52 -%^ one_64 in

  let t1 = t1 +%^ (t0 >>^ 51ul) in
  let t0 = t0 &^ mask_51 in
  let t2 = t2 +%^ (t1 >>^ 51ul) in
  let t1 = t1 &^ mask_51 in
  let t3 = t3 +%^ (t2 >>^ 51ul) in
  let t2 = t2 &^ mask_51 in
  let t4 = t4 +%^ (t3 >>^ 51ul) in
  let t3 = t3 &^ mask_51 in
  let t4 = t4 &^ mask_51 in

  let o0 = t0 |^ (t1 <<^ 51ul) in
  let o1 = (t1 >>^ 13ul) |^ (t2 <<^ 38ul) in
  let o2 = (t2 >>^ 26ul) |^ (t3 <<^ 25ul) in
  let o3 = (t3 >>^ 39ul) |^ (t4 <<^ 12ul) in

  store64_le (Buffer.sub output 0ul  8ul) o0;
  store64_le (Buffer.sub output 8ul  8ul) o1;
  store64_le (Buffer.sub output 16ul 8ul) o2;
  store64_le (Buffer.sub output 24ul 8ul) o3


val fmonty: x2:felem -> z2:felem ->
  x3:felem -> z3:felem ->
  x:felem -> z:felem ->
  xprime:felem -> zprime:felem ->
  qmqp:felem ->
  Stack unit
    (requires (fun h -> live h x2 /\ live h z2 /\ live h x3 /\ live h z3
      /\ live h x /\ live h z /\ live h xprime /\ live h zprime /\ live h qmqp))
    (ensures (fun h0 _ h1 -> true))
let fmonty x2 z2 x3 z3 x z xprime zprime qmqp =
  push_frame();
  let buf = create zero_64 40ul in
  let origx      = Buffer.sub buf 0ul  5ul in
  let origxprime = Buffer.sub buf 5ul  5ul in
  let zzz        = Buffer.sub buf 10ul 5ul in
  let xx         = Buffer.sub buf 15ul 5ul in
  let zz         = Buffer.sub buf 20ul 5ul in
  let xxprime    = Buffer.sub buf 25ul 5ul in
  let zzprime    = Buffer.sub buf 30ul 5ul in
  let zzzprime   = Buffer.sub buf 35ul 5ul in
  blit x 0ul origx 0ul 5ul;
  fsum x z;
  fdifference z origx;
  blit xprime 0ul origxprime 0ul 5ul;
  fsum xprime zprime;
  fdifference zprime origxprime;
  fmul xxprime xprime z;
  fmul zzprime x zprime;
  blit xxprime 0ul origxprime 0ul 5ul;
  fsum xxprime zzprime;
  fdifference zzprime origxprime;
  fsquare_times x3 xxprime 1ul;
  fsquare_times zzzprime zzprime 1ul;
  fmul z3 zzzprime qmqp;

  fsquare_times xx x 1ul;
  fsquare_times zz z 1ul;
  fmul x2 xx zz;
  fdifference zz xx;
  fscalar_product zzz zz (uint64_to_sint64 121665uL);
  fsum zzz xx;
  fmul z2 zz zzz;
  pop_frame()


val swap_conditional: a:felem -> b:felem -> iswap:limb ->
  Stack unit
    (requires (fun h -> live h a /\ live h b))
    (ensures (fun h0 _ h1 -> modifies_2 a b h0 h1 /\ live h1 a /\ live h1 b))
let swap_conditional a b iswap =
  let a0 = a.(0ul) in
  let a1 = a.(1ul) in
  let a2 = a.(2ul) in
  let a3 = a.(3ul) in
  let a4 = a.(4ul) in
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b2 = b.(2ul) in
  let b3 = b.(3ul) in
  let b4 = b.(4ul) in
  let swap = zero_64 -^ iswap in
  let x = swap &^ (a0 ^^ b0) in
  let a0 = a0 ^^ x in
  let b0 = b0 ^^ x in
  let x = swap &^ (a1 ^^ b1) in
  let a1 = a1 ^^ x in
  let b1 = b1 ^^ x in
  let x = swap &^ (a2 ^^ b2) in
  let a2 = a2 ^^ x in
  let b2 = b2 ^^ x in
  let x = swap &^ (a3 ^^ b3) in
  let a3 = a3 ^^ x in
  let b3 = b3 ^^ x in
  let x = swap &^ (a4 ^^ b4) in
  let a4 = a4 ^^ x in
  let b4 = b4 ^^ x in
  a.(0ul) <- a0;
  a.(1ul) <- a1;
  a.(2ul) <- a2;
  a.(3ul) <- a3;
  a.(4ul) <- a4;
  b.(0ul) <- b0;
  b.(1ul) <- b1;
  b.(2ul) <- b2;
  b.(3ul) <- b3;
  b.(4ul) <- b4


val cmult_small_loop: nqx:felem -> nqz:felem -> nqpqx:felem -> nqpqz:felem ->
  nqx2:felem -> nqz2:felem -> nqpqx2:felem -> nqpqz2:felem -> q:felem -> byte:H8.t ->
  i:U32.t ->
  Stack unit
    (requires (fun h -> true))
    (ensures (fun h0 _ h1 -> true))
let rec cmult_small_loop nqx nqz nqpqx nqpqz nqx2 nqz2 nqpqx2 nqpqz2 q byte i =
  if (U32 (i =^ 0ul)) then ()
  else (
    let bit = sint8_to_sint64 (H8 (byte >>^ 7ul)) in
    swap_conditional nqx nqpqx bit;
    swap_conditional nqz nqpqz bit;
    fmonty nqx2 nqz2 nqpqx2 nqpqz2 nqx nqz nqpqx nqpqz q;
    swap_conditional nqx2 nqpqx2 bit;
    swap_conditional nqz2 nqpqz2 bit;
    let t = nqx in
    let nqx = nqx2 in
    let nqx2 = t in
    let t = nqz in
    let nqz = nqz2 in
    let nqz2 = t in
    let t = nqpqx in
    let nqpqx = nqpqx2 in
    let nqpqx2 = t in
    let t = nqpqz in
    let nqpqz = nqpqz2 in
    let nqpqz2 = t in
    let byte = H8 (byte <<^ 1ul) in
    cmult_small_loop nqx nqz nqpqx nqpqz nqx2 nqz2 nqpqx2 nqpqz2 q byte (U32 (i -^ 1ul))
  )


val cmult_big_loop: n:uint8_p{length n = 32} ->
  nqx:felem -> nqz:felem -> nqpqx:felem -> nqpqz:felem ->
  nqx2:felem -> nqz2:felem -> nqpqx2:felem -> nqpqz2:felem -> q:felem -> i:U32.t ->
  Stack unit
    (requires (fun h -> true))
    (ensures (fun h0 _ h1 -> true))
let rec cmult_big_loop n nqx nqz nqpqx nqpqz nqx2 nqz2 nqpqx2 nqpqz2 q i =
  if (U32 (i =^ 0ul)) then ()
  else (
    let byte = n.(U32 (31ul -^ i)) in
    cmult_small_loop nqx nqz nqpqx nqpqz nqx2 nqz2 nqpqx2 nqpqz2 q byte 8ul;
    cmult_big_loop n nqx nqz nqpqx nqpqz nqx2 nqz2 nqpqx2 nqpqz2 q (U32 (i -^ 1ul))
  )


val cmult: resultx:felem -> resultz:felem -> n:uint8_p{length n = 32} -> q:felem ->
  Stack unit
    (requires (fun h -> live h resultx /\ live h resultz /\ live h n /\ live h q))
    (ensures (fun h0 _ h1 -> modifies_2 resultx resultz h0 h1 /\ live h1 resultx /\ live h1 resultz))
let cmult resultx resultz n q =
  push_frame();
  let buf = create zero_64 40ul in
  let nqpqx  = Buffer.sub buf 0ul  5ul in
  let nqpqz  = Buffer.sub buf 5ul  5ul in
  let nqx    = Buffer.sub buf 10ul 5ul in
  let nqz    = Buffer.sub buf 15ul 5ul in
  let nqpqx2 = Buffer.sub buf 20ul 5ul in
  let nqpqz2 = Buffer.sub buf 25ul 5ul in
  let nqx2   = Buffer.sub buf 30ul 5ul in
  let nqz2   = Buffer.sub buf 35ul 5ul in

  blit q 0ul nqpqx 0ul 5ul;

  cmult_big_loop n nqx nqz nqpqx nqpqz nqx2 nqz2 nqpqx2 nqpqz2 q 32ul;
  blit nqx 0ul resultx 0ul 5ul;
  blit nqz 0ul resultz 0ul 5ul;
  pop_frame()


val crecip: out:felem -> z:felem -> Stack unit
  (requires (fun h -> live h out /\ live h z))
  (ensures (fun h0 _ h1 -> live h1 out /\ modifies_1 out h0 h1))
let crecip out z =
  push_frame();
  let buf = create zero_64 20ul in
  let a  = Buffer.sub buf 0ul  5ul in
  let t0 = Buffer.sub buf 5ul  5ul in
  let b  = Buffer.sub buf 10ul 5ul in
  let c  = Buffer.sub buf 15ul 5ul in
  fsquare_times a z 1ul;
  fsquare_times t0 a 2ul;
  fmul b t0 z;
  fmul a b a;
  fsquare_times t0 a 1ul;
  fmul b t0 b;
  fsquare_times t0 b 5ul;
  fmul b t0 b;
  fsquare_times t0 b 10ul;
  fmul c t0 b;
  fsquare_times t0 c 20ul;
  fmul t0 t0 c;
  fsquare_times t0 t0 10ul;
  fmul b t0 b;
  fsquare_times t0 b 50ul;
  fmul c t0 b;
  fsquare_times t0 c 100ul;
  fmul t0 t0 c;
  fsquare_times t0 t0 50ul;
  fmul t0 t0 b;
  fsquare_times t0 t0 5ul;
  fmul out t0 a;
  pop_frame()


val crypto_scalarmult_curve25519_donna_c64:
  mypublic:uint8_p{length mypublic = 32} ->
  secret:uint8_p{length secret = 32} ->
  basepoint:uint8_p{length basepoint = 32} ->
  Stack unit
    (requires (fun h -> live h mypublic /\ live h secret /\ live h basepoint))
    (ensures (fun h0 _ h1 -> live h1 mypublic /\ modifies_1 mypublic h0 h1))
let crypto_scalarmult_curve25519_donna_c64 mypublic secret basepoint =
  push_frame();
  let buf = create zero_64 20ul in
  let e   = create zero_8 32ul in
  let bp    = Buffer.sub buf 0ul  5ul in
  let x     = Buffer.sub buf 5ul  5ul in
  let z     = Buffer.sub buf 10ul 5ul in
  let zmone = Buffer.sub buf 15ul 5ul in
  blit secret 0ul e 0ul 32ul;
  let e0  = e.(0ul) in
  let e31 = e.(31ul) in
  let open Hacl.UInt8 in
  let e0  = e0 &^ (uint8_to_sint8 248uy) in
  let e31 = e31 &^ (uint8_to_sint8 127uy) in
  let e31 = e31 |^ (uint8_to_sint8 64uy) in
  e.(0ul) <- e0;
  e.(31ul) <- e31;
  fexpand bp basepoint;
  cmult x z e bp;
  crecip zmone z;
  fmul z x zmone;
  fcontract mypublic z;
  pop_frame()
