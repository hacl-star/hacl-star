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

(*

/* Take a fully reduced polynomial form number and contract it into a
 * little-endian, 32-byte array
 */
static void
fcontract(u8 *output, const felem input) {
  uint128_t t[5];

  t[0] = input[0];
  t[1] = input[1];
  t[2] = input[2];
  t[3] = input[3];
  t[4] = input[4];

  t[1] += t[0] >> 51; t[0] &= 0x7ffffffffffff;
  t[2] += t[1] >> 51; t[1] &= 0x7ffffffffffff;
  t[3] += t[2] >> 51; t[2] &= 0x7ffffffffffff;
  t[4] += t[3] >> 51; t[3] &= 0x7ffffffffffff;
  t[0] += 19 * (t[4] >> 51); t[4] &= 0x7ffffffffffff;

  t[1] += t[0] >> 51; t[0] &= 0x7ffffffffffff;
  t[2] += t[1] >> 51; t[1] &= 0x7ffffffffffff;
  t[3] += t[2] >> 51; t[2] &= 0x7ffffffffffff;
  t[4] += t[3] >> 51; t[3] &= 0x7ffffffffffff;
  t[0] += 19 * (t[4] >> 51); t[4] &= 0x7ffffffffffff;

  /* now t is between 0 and 2^255-1, properly carried. */
  /* case 1: between 0 and 2^255-20. case 2: between 2^255-19 and 2^255-1. */

  t[0] += 19;

  t[1] += t[0] >> 51; t[0] &= 0x7ffffffffffff;
  t[2] += t[1] >> 51; t[1] &= 0x7ffffffffffff;
  t[3] += t[2] >> 51; t[2] &= 0x7ffffffffffff;
  t[4] += t[3] >> 51; t[3] &= 0x7ffffffffffff;
  t[0] += 19 * (t[4] >> 51); t[4] &= 0x7ffffffffffff;

  /* now between 19 and 2^255-1 in both cases, and offset by 19. */

  t[0] += 0x8000000000000 - 19;
  t[1] += 0x8000000000000 - 1;
  t[2] += 0x8000000000000 - 1;
  t[3] += 0x8000000000000 - 1;
  t[4] += 0x8000000000000 - 1;

  /* now between 2^255 and 2^256-20, and offset by 2^255. */

  t[1] += t[0] >> 51; t[0] &= 0x7ffffffffffff;
  t[2] += t[1] >> 51; t[1] &= 0x7ffffffffffff;
  t[3] += t[2] >> 51; t[2] &= 0x7ffffffffffff;
  t[4] += t[3] >> 51; t[3] &= 0x7ffffffffffff;
  t[4] &= 0x7ffffffffffff;

  store_limb(output, t[0] | (t[1] << 51));
  store_limb(output + 8, (t[1] >> 13) | (t[2] << 38));
  store_limb(output + 16, (t[2] >> 26) | (t[3] << 25));
  store_limb(output + 24, (t[3] >> 39) | (t[4] << 12));
}

/* Input: Q, Q', Q-Q'
 * Output: 2Q, Q+Q'
 *
 *   x2 z2: long form
 *   x3 z3: long form
 *   x z: short form, destroyed
 *   xprime zprime: short form, destroyed
 *   qmqp: short form, preserved
 */
static void
fmonty(limb *x2, limb *z2, /* output 2Q */
       limb *x3, limb *z3, /* output Q + Q' */
       limb *x, limb *z,   /* input Q */
       limb *xprime, limb *zprime, /* input Q' */
       const limb *qmqp /* input Q - Q' */) {
  limb origx[5], origxprime[5], zzz[5], xx[5], zz[5], xxprime[5],
        zzprime[5], zzzprime[5];

  memcpy(origx, x, 5 * sizeof(limb));
  fsum(x, z);
  fdifference_backwards(z, origx); /* does x - z */

  memcpy(origxprime, xprime, sizeof(limb) * 5);
  fsum(xprime, zprime);
  fdifference_backwards(zprime, origxprime);
  fmul(xxprime, xprime, z);
  fmul(zzprime, x, zprime);
  memcpy(origxprime, xxprime, sizeof(limb) * 5);
  fsum(xxprime, zzprime);
  fdifference_backwards(zzprime, origxprime);
  fsquare_times(x3, xxprime, 1);
  fsquare_times(zzzprime, zzprime, 1);
  fmul(z3, zzzprime, qmqp);

  fsquare_times(xx, x, 1);
  fsquare_times(zz, z, 1);
  fmul(x2, xx, zz);
  fdifference_backwards(zz, xx); /* does zz = xx - zz */
  fscalar_product(zzz, zz, 121665);
  fsum(zzz, xx);
  fmul(z2, zz, zzz);
}

/* -----------------------------------------------------------------------------
   Maybe swap the contents of two limb arrays (@a and @b), each @len elements
   long. Perform the swap iff @swap is non-zero.

   This function performs the swap without leaking any side-channel
   information.
   ----------------------------------------------------------------------------- */
static void
swap_conditional(limb a[5], limb b[5], limb iswap) {
  unsigned i;
  const limb swap = -iswap;

  for (i = 0; i < 5; ++i) {
    const limb x = swap & (a[i] ^ b[i]);
    a[i] ^= x;
    b[i] ^= x;
  }
}

/* Calculates nQ where Q is the x-coordinate of a point on the curve
 *
 *   resultx/resultz: the x coordinate of the resulting curve point (short form)
 *   n: a little endian, 32-byte number
 *   q: a point of the curve (short form)
 */
static void
cmult(limb *resultx, limb *resultz, const u8 *n, const limb *q) {
  limb a[5] = {0}, b[5] = {1}, c[5] = {1}, d[5] = {0};
  limb *nqpqx = a, *nqpqz = b, *nqx = c, *nqz = d, *t;
  limb e[5] = {0}, f[5] = {1}, g[5] = {0}, h[5] = {1};
  limb *nqpqx2 = e, *nqpqz2 = f, *nqx2 = g, *nqz2 = h;

  unsigned i, j;

  memcpy(nqpqx, q, sizeof(limb) * 5);

  for (i = 0; i < 32; ++i) {
    u8 byte = n[31 - i];
    for (j = 0; j < 8; ++j) {
      const limb bit = byte >> 7;

      swap_conditional(nqx, nqpqx, bit);
      swap_conditional(nqz, nqpqz, bit);
      fmonty(nqx2, nqz2,
             nqpqx2, nqpqz2,
             nqx, nqz,
             nqpqx, nqpqz,
             q);
      swap_conditional(nqx2, nqpqx2, bit);
      swap_conditional(nqz2, nqpqz2, bit);

      t = nqx;
      nqx = nqx2;
      nqx2 = t;
      t = nqz;
      nqz = nqz2;
      nqz2 = t;
      t = nqpqx;
      nqpqx = nqpqx2;
      nqpqx2 = t;
      t = nqpqz;
      nqpqz = nqpqz2;
      nqpqz2 = t;

      byte <<= 1;
    }
  }

  memcpy(resultx, nqx, sizeof(limb) * 5);
  memcpy(resultz, nqz, sizeof(limb) * 5);
}


/* -----------------------------------------------------------------------------
   Shamelessly copied from djb's code, tightened a little
   ----------------------------------------------------------------------------- */
static void
crecip(felem out, const felem z) {
  felem a,t0,b,c;

  /* 2 */ fsquare_times(a, z, 1); /* a = 2 */
  /* 8 */ fsquare_times(t0, a, 2);
  /* 9 */ fmul(b, t0, z); /* b = 9 */
  /* 11 */ fmul(a, b, a); /* a = 11 */
  /* 22 */ fsquare_times(t0, a, 1);
  /* 2^5 - 2^0 = 31 */ fmul(b, t0, b);
  /* 2^10 - 2^5 */ fsquare_times(t0, b, 5);
  /* 2^10 - 2^0 */ fmul(b, t0, b);
  /* 2^20 - 2^10 */ fsquare_times(t0, b, 10);
  /* 2^20 - 2^0 */ fmul(c, t0, b);
  /* 2^40 - 2^20 */ fsquare_times(t0, c, 20);
  /* 2^40 - 2^0 */ fmul(t0, t0, c);
  /* 2^50 - 2^10 */ fsquare_times(t0, t0, 10);
  /* 2^50 - 2^0 */ fmul(b, t0, b);
  /* 2^100 - 2^50 */ fsquare_times(t0, b, 50);
  /* 2^100 - 2^0 */ fmul(c, t0, b);
  /* 2^200 - 2^100 */ fsquare_times(t0, c, 100);
  /* 2^200 - 2^0 */ fmul(t0, t0, c);
  /* 2^250 - 2^50 */ fsquare_times(t0, t0, 50);
  /* 2^250 - 2^0 */ fmul(t0, t0, b);
  /* 2^255 - 2^5 */ fsquare_times(t0, t0, 5);
  /* 2^255 - 21 */ fmul(out, t0, a);
}

static const unsigned char basepoint[32] = {9};

static int
crypto_scalarmult_curve25519_donna_c64(unsigned char *mypublic,
                                       const unsigned char *secret,
                                       const unsigned char *basepoint) {
  limb bp[5], x[5], z[5], zmone[5];
  uint8_t e[32];
  int i;

  for (i = 0;i < 32;++i) e[i] = secret[i];
  e[0] &= 248;
  e[31] &= 127;
  e[31] |= 64;

  fexpand(bp, basepoint);
  cmult(x, z, e, bp);
  crecip(zmone, z);
  fmul(z, x, zmone);
  fcontract(mypublic, z);
  return 0;
}

static int
crypto_scalarmult_curve25519_donna_c64_base(unsigned char *q,
                                            const unsigned char *n)
{
  return crypto_scalarmult_curve25519_donna_c64(q, n, basepoint);
}

struct crypto_scalarmult_curve25519_implementation
crypto_scalarmult_curve25519_donna_c64_implementation = {
    SODIUM_C99(.mult = ) crypto_scalarmult_curve25519_donna_c64,
    SODIUM_C99(.mult_base = ) crypto_scalarmult_curve25519_donna_c64_base
};
*)
