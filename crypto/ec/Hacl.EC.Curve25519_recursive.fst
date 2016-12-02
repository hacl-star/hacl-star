module Hacl.EC.Curve25519_recursive

open FStar.Buffer
open FStar.HyperStack
open FStar.Int.Cast

open Hacl.UInt64
open Hacl.Cast

module U64  = FStar.UInt64
module U32  = FStar.UInt32
module H8   = Hacl.UInt8
module H64  = Hacl.UInt64
module H128 = Hacl.UInt128


inline_for_extraction let zero_8 = uint8_to_sint8 0uy
inline_for_extraction let zero_64 = uint64_to_sint64 0uL
inline_for_extraction let zero_128 = sint64_to_sint128 (uint64_to_sint64 0uL)
inline_for_extraction let one_8 = uint8_to_sint8 1uy
inline_for_extraction let one_64 = uint64_to_sint64 1uL


type limb = H64.t
type wide_limb = H128.t
type felem = buffer limb
type felem_wide = buffer wide_limb
type uint8_p = buffer H8.t


inline_for_extraction let len = 5ul
inline_for_extraction let limb_size = 51ul

inline_for_extraction let two54m152 = uint64_to_sint64 0x3fffffffffff68uL
inline_for_extraction let two54m8   = uint64_to_sint64 0x3ffffffffffff8uL
inline_for_extraction let nineteen  = uint64_to_sint64 19uL
inline_for_extraction let mask_51    = uint64_to_sint64 0x7ffffffffffffuL

(* val fsum_: *)
(*   a:felem -> *)
(*   b:felem -> *)
(*   ctr:U32.t -> *)
(*   Stack unit *)
(*     (requires (fun _ -> true)) *)
(*     (ensures (fun _ _ _ -> true)) *)
(* let rec fsum_ a b ctr = *)
(*   if U32 (ctr =^ 0ul) then () *)
(*   else ( *)
(*     let i = U32 (ctr -^ 1ul) in *)
(*     let ai = a.(i) in let bi = b.(i) in *)
(*     a.(i) <- ai +^ bi; *)
(*     fsum_ a b i *)
(*   ) *)


(* val fsum: *)
(*   a:felem -> *)
(*   b:felem -> *)
(*   Stack unit *)
(*     (requires (fun _ -> true)) *)
(*     (ensures (fun _ _ _ -> true)) *)
(* let fsum a b = fsum_ a b len *)

private val fsum:
  a:felem ->
  b:felem ->
  Stack unit
    (requires (fun _ -> true))
    (ensures (fun _ _ _ -> true))
private let fsum a b =
  let a0 = a.(0ul) in let b0 = b.(0ul) in
  let a1 = a.(1ul) in let b1 = b.(1ul) in
  let a2 = a.(2ul) in let b2 = b.(2ul) in
  let a3 = a.(3ul) in let b3 = b.(3ul) in
  let a4 = a.(4ul) in let b4 = b.(4ul) in
  a.(0ul) <- a0 +^ b0;
  a.(1ul) <- a1 +^ b1;
  a.(2ul) <- a2 +^ b2;
  a.(3ul) <- a3 +^ b3;
  a.(4ul) <- a4 +^ b4


(* val fdifference_: *)
(*   a:felem -> *)
(*   b:felem -> *)
(*   ctr:U32.t -> *)
(*   Stack unit *)
(*     (requires (fun _ -> true)) *)
(*     (ensures (fun _ _ _ -> true)) *)
(* let rec fdifference_ a b ctr = *)
(*   if U32 (ctr =^ 0ul) then () *)
(*   else ( *)
(*     let i = U32 (ctr -^ 1ul) in *)
(*     let ai = a.(i) in let bi = b.(i) in *)
(*     a.(i) <- bi -^ ai; *)
(*     fdifference_ a b i *)
(*   ) *)


(* val fdifference: *)
(*   a:felem -> *)
(*   b:felem -> *)
(*   Stack unit *)
(*     (requires (fun _ -> true)) *)
(*     (ensures (fun _ _ _ -> true)) *)
(* let fdifference a b = *)
(*   push_frame(); *)
(*   let zero_prime = createL [two54m152; two54m8; two54m8; two54m8; two54m8] in *)
(*   fsum  b zero_prime; *)
(*   fdifference_ a b len; *)
(*   pop_frame() *)


private val fdifference:
  a:felem ->
  b:felem ->
  Stack unit
    (requires (fun _ -> true))
    (ensures (fun _ _ _ -> true))
private let fdifference a b =
  let a0 = a.(0ul) in let b0 = b.(0ul) in
  let a1 = a.(1ul) in let b1 = b.(1ul) in
  let a2 = a.(2ul) in let b2 = b.(2ul) in
  let a3 = a.(3ul) in let b3 = b.(3ul) in
  let a4 = a.(4ul) in let b4 = b.(4ul) in
  a.(0ul) <- b0 +^ two54m152 -^ a0;
  a.(1ul) <- b1 +^ two54m8   -^ a1;
  a.(2ul) <- b2 +^ two54m8   -^ a2;
  a.(3ul) <- b3 +^ two54m8   -^ a3;
  a.(4ul) <- b4 +^ two54m8   -^ a4



private val fscalar_:
  output:felem_wide ->
  a:felem ->
  s:limb ->
  ctr:U32.t ->
  Stack unit
    (requires (fun _ -> true))
    (ensures (fun _ _ _ -> true))
private let rec fscalar_ output a s ctr =
  if U32 (ctr =^ 0ul) then ()
  else (
    let i = U32 (ctr -^ 1ul) in
    let ai = a.(i) in
    output.(i) <- H128 (ai *^ s);
    fscalar_ output a s i
  )


private val carry_wide_:
  t:felem_wide ->
  ctr:U32.t ->
  Stack unit
    (requires (fun _ -> true))
    (ensures (fun _ _ _ -> true))
private let rec carry_wide_ t ctr =
  if U32 (ctr =^ len -^ 1ul) then ()
  else (
    let tctr = t.(ctr) in
    let tctrp1 = t.(U32 (ctr+^1ul)) in
    let r0 = sint128_to_sint64 (tctr) &^ mask_51 in
    let c  = sint128_to_sint64 (H128 (tctr >>^ limb_size)) in
    t.(ctr) <- sint64_to_sint128 r0;
    t.(U32 (ctr +^ 1ul)) <- H128 (tctrp1 +^ sint64_to_sint128 c);
    carry_wide_ t (U32 (ctr +^ 1ul))
  )


private val copy_from_wide_:
  output:felem ->
  input:felem_wide ->
  ctr:U32.t ->
  Stack unit
    (requires (fun _ -> true))
    (ensures (fun _ _ _ -> true))
let rec copy_from_wide_ output input ctr =
  if U32 (ctr =^ 0ul) then ()
  else (
    let i = U32 (ctr -^ 1ul) in
    let inputi = input.(i) in
    output.(i) <- sint128_to_sint64 inputi;
    copy_from_wide_ output input i
  )


private val fscalar_product:
  output:felem ->
  a:felem ->
  s:limb ->
  Stack unit
    (requires (fun _ -> true))
    (ensures (fun _ _ _ -> true))
private let fscalar_product output a s =
  push_frame();
  let t = create zero_128 len in
  fscalar_ t a s len;
  carry_wide_ t 0ul;
  let tnm1 = t.(U32 (len -^ 1ul)) in
  let t0   = t.(0ul) in
  let c = sint128_to_sint64 (H128 (tnm1 >>^ limb_size)) in
  t.(U32 (len -^ 1ul)) <- H128 (tnm1 &^ sint64_to_sint128 mask_51);
  t.(0ul) <- H128 (t0 +^ (c *^ nineteen));
  copy_from_wide_ output t len;
  pop_frame()


private val shift_:
  output:felem ->
  tmp:limb ->
  ctr:U32.t ->
  Stack unit
    (requires (fun _ -> true))
    (ensures (fun _ _ _ -> true))
private let rec shift_ output tmp ctr =
  let open FStar.UInt32 in
  let tmp = if (ctr =^ len) then output.(0ul) else tmp in
  if (ctr =^ 1ul) then output.(1ul) <- tmp
  else (
    let z = output.(ctr -^ 1ul) in
    output.((ctr %^ len)) <- z;
    shift_ output tmp (ctr -^ 1ul)
  )


private val shift_reduce:
  output:felem ->
  Stack unit
    (requires (fun _ -> true))
    (ensures (fun _ _ _ -> true))
private let shift_reduce output =
  shift_ output zero_64 len;
  let o0 = output.(0ul) in
  output.(0ul) <- o0 *^ nineteen


private val sum_scalar_multiplication_:
  output:felem_wide ->
  input:felem ->
  s:limb ->
  ctr:U32.t ->
  Stack unit
    (requires (fun _ -> true))
    (ensures (fun _ _ _ -> true))
private let rec sum_scalar_multiplication_ output input s ctr =
  if U32 (ctr =^ 0ul) then ()
  else (
    let i = U32 (ctr -^ 1ul) in
    let oi = output.(i) in let ii = input.(i) in
    output.(i) <- H128 (oi +^ (ii *^ s));
    sum_scalar_multiplication_ output input s i
  )


private val mul_shift_reduce_:
  output:felem_wide ->
  input:felem ->
  input2:felem ->
  ctr:U32.t ->
  Stack unit
    (requires (fun _ -> true))
    (ensures (fun _ _ _ -> true))
private let rec mul_shift_reduce_ output input input2 ctr =
  let open FStar.UInt32 in
  if (ctr =^ 0ul) then ()
  else (
    let i = ctr -^ 1ul in
    let input2i = input2.(len -^ 1ul -^ i) in
    sum_scalar_multiplication_ output input input2i len;
    if (ctr >^ 1ul) then shift_reduce input;
    mul_shift_reduce_ output input input2 i
  )



private val fmul:
  output:felem ->
  input:felem ->
  input2:felem ->
  Stack unit
    (requires (fun _ -> true))
    (ensures (fun _ _ _ -> true))
private let fmul output input input2 =
  push_frame();
  let tmp = create zero_64 len in
  let t   = create zero_128 len in
  blit input 0ul tmp 0ul len;
  mul_shift_reduce_ t tmp input2 len;
  carry_wide_ t 0ul;
  let tnm1 = t.(U32 (len -^ 1ul)) in
  let t0   = t.(0ul) in
  let c = sint128_to_sint64 (H128 (tnm1 >>^ limb_size)) in
  t.(U32 (len -^ 1ul)) <- H128 (tnm1 &^ sint64_to_sint128 mask_51);
  t.(0ul) <- H128 (t0 +^ (c *^ nineteen));
  copy_from_wide_ output t len;
  let output0 = output.(0ul) in
  let output1 = output.(1ul) in
  let c = output0 >>^ limb_size in
  output.(0ul) <- output0 &^ mask_51;
  output.(1ul) <- output1 +^ c;
  pop_frame()


private val fsquare_:
  output:felem ->
  tmp:felem_wide ->
  Stack unit
    (requires (fun _ -> true))
    (ensures (fun _ _ _ -> true))
private let fsquare_ output t =
  let r0 = output.(0ul) in
  let r1 = output.(1ul) in
  let r2 = output.(2ul) in
  let r3 = output.(3ul) in
  let r4 = output.(4ul) in
  let d0 = r0 *^ (uint64_to_sint64 2uL) in
  let d1 = r1 *^ (uint64_to_sint64 2uL) in
  let d2 = r2 *^ (uint64_to_sint64 2uL) *^ (uint64_to_sint64 19uL) in
  let d419 = r4 *^ (uint64_to_sint64 19uL) in
  let d4 = d419 *^ (uint64_to_sint64 2uL) in
  let open Hacl.UInt128 in
  t.(0ul) <- ( r0) *^ r0 +^ ( d4) *^ r1 +^ (( d2) *^ (r3     ));
  t.(1ul) <- ( d0) *^ r1 +^ ( d4) *^ r2 +^ (( r3) *^ (H64 (r3 *^ (uint64_to_sint64 19uL))));
  t.(2ul) <- ( d0) *^ r2 +^ ( r1) *^ r1 +^ (( d4) *^ (r3     ));
  t.(3ul) <- ( d0) *^ r3 +^ ( d1) *^ r2 +^ (( r4) *^ (d419   ));
  t.(4ul) <- ( d0) *^ r4 +^ ( d1) *^ r3 +^ (( r2) *^ (r2     ));
  carry_wide_ t 0ul;
  let tnm1 = t.(U32 (len -^ 1ul)) in
  let t0   = t.(0ul) in
  let c = sint128_to_sint64 (H128 (tnm1 >>^ limb_size)) in
  t.(U32 (len -^ 1ul)) <- H128 (tnm1 &^ sint64_to_sint128 mask_51);
  t.(0ul) <- H128 (t0 +^ (c *^ nineteen));
  copy_from_wide_ output t len;
  let output0 = output.(0ul) in
  let output1 = output.(1ul) in
  let open Hacl.UInt64 in
  let c = output0 >>^ limb_size in
  output.(0ul) <- output0 &^ mask_51;
  output.(1ul) <- output1 +^ c


(* val fsquare_times_: *)
(*   input:felem -> *)
(*   count:U32.t -> *)
(*   Stack unit *)
(*     (requires (fun _ -> true)) *)
(*     (ensures (fun _ _ _ -> true)) *)
(* let rec fsquare_times_ tmp count = *)
(*   if U32 (count =^ 0ul) then () *)
(*   else ( *)
(*     fmul tmp tmp tmp; *)
(*     fsquare_times_ tmp (U32 (count -^ 1ul)) *)
(*   ) *)

private val fsquare_times_:
  input:felem ->
  tmp:felem_wide ->
  count:U32.t ->
  Stack unit
    (requires (fun _ -> true))
    (ensures (fun _ _ _ -> true))
private let rec fsquare_times_ output tmp count =
  if U32 (count =^ 0ul) then ()
  else (
    fsquare_ output tmp;
    fsquare_times_ output tmp (U32 (count -^ 1ul))
  )


private val fsquare_times:
  output:felem ->
  input:felem ->
  count:U32.t ->
  Stack unit
    (requires (fun _ -> true))
    (ensures (fun _ _ _ -> true))
private let fsquare_times output input count =
  push_frame();
  let tmp = create zero_64 len in
  let t   = create zero_128 len in
  blit input 0ul tmp 0ul len;
  fsquare_times_ tmp t count;
  blit tmp 0ul output 0ul len;
  pop_frame()


#reset-options "--initial_fuel 0 --max_fuel 0"

private val load64_le:
  b:uint8_p{length b >= 8} ->
  Stack H64.t
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> h0 == h1))
private let load64_le b =
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


private val store64_le:
  b:uint8_p{length b >= 8} ->
  z:H64.t ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ live h1 b))
private let store64_le b z =
  let open Hacl.UInt64 in
  b.(0ul) <- sint64_to_sint8 z;
  b.(1ul) <- sint64_to_sint8 (z >>^ 8ul);
  b.(2ul) <- sint64_to_sint8 (z >>^ 16ul);
  b.(3ul) <- sint64_to_sint8 (z >>^ 24ul);
  b.(4ul) <- sint64_to_sint8 (z >>^ 32ul);
  b.(5ul) <- sint64_to_sint8 (z >>^ 40ul);
  b.(6ul) <- sint64_to_sint8 (z >>^ 48ul);
  b.(7ul) <- sint64_to_sint8 (z >>^ 56ul)


private val fexpand: output:felem -> input:uint8_p{length input = 32} -> Stack unit
  (requires (fun h -> live h output /\ live h input))
  (ensures (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1))
private let fexpand output input =
  let mask_51 = uint64_to_sint64 0x7ffffffffffffuL in
  let i0 = load64_le (Buffer.sub input 0ul 8ul) in
  let i1 = load64_le (Buffer.sub input 6ul 8ul) in
  let i2 = load64_le (Buffer.sub input 12ul 8ul) in
  let i3 = load64_le (Buffer.sub input 19ul 8ul) in
  let i4 = load64_le (Buffer.sub input 24ul 8ul) in
  let output0 = (i0         ) &^ mask_51 in
  let output1 = (i1 >>^ 3ul ) &^ mask_51 in
  let output2 = (i2 >>^ 6ul ) &^ mask_51 in
  let output3 = (i3 >>^ 1ul ) &^ mask_51 in
  let output4 = (i4 >>^ 12ul) &^ mask_51 in
  output.(0ul) <- output0;
  output.(1ul) <- output1;
  output.(2ul) <- output2;
  output.(3ul) <- output3;
  output.(4ul) <- output4


private val fcontract: output:uint8_p{length output = 32} -> input:felem -> Stack unit
  (requires (fun h -> live h output /\ live h input))
  (ensures (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1))
private let fcontract output input =
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


private val fmonty: x2:felem -> z2:felem ->
  x3:felem -> z3:felem ->
  x:felem -> z:felem ->
  xprime:felem -> zprime:felem ->
  qmqp:felem ->
  Stack unit
    (requires (fun h -> live h x2 /\ live h z2 /\ live h x3 /\ live h z3
      /\ live h x /\ live h z /\ live h xprime /\ live h zprime /\ live h qmqp))
    (ensures (fun h0 _ h1 -> true))
private let fmonty x2 z2 x3 z3 x z xprime zprime qmqp =
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


(* private val swap_conditional: a:felem -> b:felem -> iswap:limb -> *)
(*   Stack unit *)
(*     (requires (fun h -> live h a /\ live h b)) *)
(*     (ensures (fun h0 _ h1 -> modifies_2 a b h0 h1 /\ live h1 a /\ live h1 b)) *)
(* private let swap_conditional a b iswap = *)
(*   let a0 = a.(0ul) in *)
(*   let a1 = a.(1ul) in *)
(*   let a2 = a.(2ul) in *)
(*   let a3 = a.(3ul) in *)
(*   let a4 = a.(4ul) in *)
(*   let b0 = b.(0ul) in *)
(*   let b1 = b.(1ul) in *)
(*   let b2 = b.(2ul) in *)
(*   let b3 = b.(3ul) in *)
(*   let b4 = b.(4ul) in *)
(*   let swap = zero_64 -^ iswap in *)
(*   let x = swap &^ (a0 ^^ b0) in *)
(*   let a0 = a0 ^^ x in *)
(*   let b0 = b0 ^^ x in *)
(*   let x = swap &^ (a1 ^^ b1) in *)
(*   let a1 = a1 ^^ x in *)
(*   let b1 = b1 ^^ x in *)
(*   let x = swap &^ (a2 ^^ b2) in *)
(*   let a2 = a2 ^^ x in *)
(*   let b2 = b2 ^^ x in *)
(*   let x = swap &^ (a3 ^^ b3) in *)
(*   let a3 = a3 ^^ x in *)
(*   let b3 = b3 ^^ x in *)
(*   let x = swap &^ (a4 ^^ b4) in *)
(*   let a4 = a4 ^^ x in *)
(*   let b4 = b4 ^^ x in *)
(*   a.(0ul) <- a0; *)
(*   a.(1ul) <- a1; *)
(*   a.(2ul) <- a2; *)
(*   a.(3ul) <- a3; *)
(*   a.(4ul) <- a4; *)
(*   b.(0ul) <- b0; *)
(*   b.(1ul) <- b1; *)
(*   b.(2ul) <- b2; *)
(*   b.(3ul) <- b3; *)
(*   b.(4ul) <- b4 *)

private val swap_conditional_: a:felem -> b:felem -> swap:limb -> ctr:U32.t ->
  Stack unit
    (requires (fun h -> live h a /\ live h b))
    (ensures (fun h0 _ h1 -> modifies_2 a b h0 h1 /\ live h1 a /\ live h1 b))
private let rec swap_conditional_ a b swap ctr =
  if U32 (ctr =^ 0ul) then ()
  else (
    let i = U32 (ctr -^ 1ul) in
    let ai = a.(i) in
    let bi = b.(i) in
    let x = swap &^ (ai ^^ bi) in
    let ai = ai ^^ x in
    let bi = bi ^^ x in
    a.(i) <- ai;
    b.(i) <- bi;
    swap_conditional_ a b swap i
  )

private val swap_conditional: a:felem -> b:felem -> iswap:limb ->
  Stack unit
    (requires (fun h -> live h a /\ live h b))
    (ensures (fun h0 _ h1 -> modifies_2 a b h0 h1 /\ live h1 a /\ live h1 b))
private let rec swap_conditional a b iswap =
  let swap = zero_64 -^ iswap in
  swap_conditional_ a b swap len


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
    let i = U32 (i -^ 1ul) in
    let byte = n.(i) in
    cmult_small_loop nqx nqz nqpqx nqpqz nqx2 nqz2 nqpqx2 nqpqz2 q byte 8ul;
    cmult_big_loop n nqx nqz nqpqx nqpqz nqx2 nqz2 nqpqx2 nqpqz2 q i
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

  nqpqz.(0ul) <- one_64;
  nqx.(0ul) <- one_64;
  nqpqz2.(0ul) <- one_64;
  nqz2.(0ul) <- one_64;

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
