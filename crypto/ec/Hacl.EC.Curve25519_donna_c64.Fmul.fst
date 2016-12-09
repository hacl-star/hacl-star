module Hacl.EC.Curve25519_donna_c64.Fmul


open FStar.Mul
open FStar.HyperStack
open FStar.Buffer
open FStar.Int.Cast
open Hacl.UInt64
open Hacl.Cast

open Hacl.EC.Curve25519_donna_c64.Bigint


module U8 = FStar.UInt8
module U32 = FStar.UInt32

module H8 = Hacl.UInt8
module H64 = Hacl.UInt64
module H128 = Hacl.UInt128


inline_for_extraction let zero_8 = uint8_to_sint8 0uy
inline_for_extraction let zero_64 = uint64_to_sint64 0uL
inline_for_extraction let one_8 = uint8_to_sint8 1uy
inline_for_extraction let one_64 = uint64_to_sint64 1uL


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 5"


(* Ouput: x_i < 2^52 *)
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
  (* let t8 =  ( r0) *^ s0 in *)
  (* let t7 =  ( r0) *^ s1 +%^ (r1) *^ s0 in *)
  (* let t6 =  ( r0) *^ s2 +%^ (r2) *^ s0 +%^ (r1) *^ s1 in *)
  (* let t5 =  ( r0) *^ s3 +%^ (r3) *^ s0 +%^ (r1) *^ s2 +%^ (r2) *^ s1 in *)

  (* t.(0ul) <- t.(5ul) + 19 * t(5ul); *)
  (* t.(1ul) <- t.(6ul) + 19 * t(5ul); *)
  (* t.(2ul) <- t.(7ul) + 19 * t(5ul); *)
  (* t.(3ul) <- t.(8ul) + 19 * t(5ul); *)
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


val fsquare: output:felem -> Stack unit
  (requires (fun h -> live h output))
  (ensures (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1))
let fsquare output =
  let mask_51 = uint64_to_sint64 0x7ffffffffffffuL in
  let r0 = output.(0ul) in
  let r1 = output.(1ul) in
  let r2 = output.(2ul) in
  let r3 = output.(3ul) in
  let r4 = output.(4ul) in
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


val fsquare_times_: output:felem -> count:U32.t -> Stack unit
  (requires (fun h -> live h output))
  (ensures (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1))
let rec fsquare_times_ output count =
  if U32 (count =^ 0ul) then ()
  else (
    fsquare output;
    let count = U32 (count -^ 1ul) in
    fsquare_times_ output count
  )


val fsquare_times: output:felem -> input:felem -> count:U32.t -> Stack unit
  (requires (fun h -> live h output /\ live h input))
  (ensures (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1))
let fsquare_times output input count =
  blit input 0ul output 0ul 5ul;
  fsquare_times_ output count
