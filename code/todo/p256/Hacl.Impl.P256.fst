module Hacl.Impl.P256

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.Buffer
open Lib.Buffer.Lemmas

module ST = FStar.HyperStack.ST
module S = Lib.Sequence
module BB = Lib.ByteBuffer

(* Taken straight from the OpenSSL github code *)


let to_shiftval x = size_to_uint32 (size x)

(* Constants *)
let nlimbs : size_nat = 4
let nlimbs' = u32 nlimbs

(* Type aliases *)
type limb = uint128
type felem = lbuffer limb nlimbs
type longfelem = lbuffer limb (2 * nlimbs)
type smallfelem = lbuffer uint64 nlimbs
type bin32 = lbuffer uint8 32


val create_felem:
  unit -> StackInline felem
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let create_felem () =
  create (size 4) (u128 0)


val create_longfelem:
  unit -> StackInline longfelem
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let create_longfelem () =
  create (size 8) (u128 0)


val create_smallfelem:
  unit -> StackInline smallfelem
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let create_smallfelem () =
  create (size 4) (u64 0)


val kPrime: unit ->
  StackInline smallfelem
    (requires (fun h -> True))
    (ensures (fun h0 b h1 -> True))
let kPrime () =
  let b = createL [u64 0xffffffffffffffff; u64 0xffffffff; u64 0; u64 0xffffffff00000001] in
  b


val bin32_to_felem:
  output:felem -> input:bin32 ->
  Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let bin32_to_felem output input =
  let h0 = ST.get () in
  alloc #h0 #uint64 #unit #limb (size 1) (u64 0) output
  (fun h -> (fun _ sv -> True))
  (fun w ->
    let in0 = sub input (size 0) (size 8) in
    let in1 = sub input (size 8)  (size 8) in
    let in2 = sub input (size 16) (size 8) in
    let in3 = sub input (size 24) (size 8) in
    let w0 : uint64 = index #uint64 #1 w (size 0) in
    BB.uints_from_bytes_le w (size 8) in0;
    output.(size 0) <- to_u128 w0;
    BB.uints_from_bytes_le w (size 8) in1;
    output.(size 1) <- to_u128 w0;
    BB.uints_from_bytes_le w (size 8) in2;
    output.(size 2) <- to_u128 w0;
    BB.uints_from_bytes_le w (size 8) in3;
    output.(size 3) <- to_u128 w0
  )


val smallfelem_to_bin32:
  output:bin32 -> input:smallfelem ->
  Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let smallfelem_to_bin32 output input = BB.uints_to_bytes_le output (size 8) input
  (* let o0 : lbuffer uint8 8 = sub output (size 0) (size 8) in *)
  (* let o1 : lbuffer uint8 8 = sub output (size 8) (size 8) in *)
  (* let o2 : lbuffer uint8 8 = sub output (size 16) (size 8) in *)
  (* let o3 : lbuffer uint8 8 = sub output (size 24) (size 8) in *)
  (* let in0 : uint64 = input.(size 0) in *)
  (* let in1 : uint64 = input.(size 1) in *)
  (* let in2 : uint64 = input.(size 2) in *)
  (* let in3 : uint64 = input.(size 3) in *)
  (* BB.uint_to_bytes_le o0 in0; *)
  (* BB.uint_to_bytes_le o1 in1; *)
  (* BB.uint_to_bytes_le o2 in2; *)
  (* BB.uint_to_bytes_le o3 in3 *)


val flip_endian:
  output:bin32 -> input:bin32 -> len:size_t ->
  Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let flip_endian output input len =
  (**) let h0 = ST.get () in
  loop_nospec #h0 len output
  (fun i ->
    let idx = len -. (size 1) -. i in
    let inputim1 = input.(idx) in
    output.(i) <- inputim1)


(* Field operations *)
val smallfelem_one: out:smallfelem ->
  Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let smallfelem_one out =
  out.(size 0) <- u64 1;
  out.(size 1) <- u64 0;
  out.(size 2) <- u64 0;
  out.(size 3) <- u64 0

val smallfelem_assign: out:smallfelem -> input:smallfelem ->
  Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let smallfelem_assign out input =
  let in0 = input.(size 0) in
  let in1 = input.(size 1) in
  let in2 = input.(size 2) in
  let in3 = input.(size 3) in
  out.(size 0) <- in0;
  out.(size 1) <- in1;
  out.(size 2) <- in2;
  out.(size 3) <- in3

val felem_assign: out:felem -> input:felem ->
  Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let felem_assign out input =
  let in0 = input.(size 0) in
  let in1 = input.(size 1) in
  let in2 = input.(size 2) in
  let in3 = input.(size 3) in
  out.(size 0) <- in0;
  out.(size 1) <- in1;
  out.(size 2) <- in2;
  out.(size 3) <- in3

val felem_sum: out:felem -> input:felem ->
  Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let felem_sum out input =
  let in0 = input.(size 0) in
  let in1 = input.(size 1) in
  let in2 = input.(size 2) in
  let in3 = input.(size 3) in
  let o0 = out.(size 0) in
  let o1 = out.(size 1) in
  let o2 = out.(size 2) in
  let o3 = out.(size 3) in
  out.(size 0) <- o0 +. in0;
  out.(size 1) <- o1 +. in1;
  out.(size 2) <- o2 +. in2;
  out.(size 3) <- o3 +. in3


val felem_small_sum: out:felem -> input:smallfelem ->
  Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let felem_small_sum out input =
  let in0 = input.(size 0) in
  let in1 = input.(size 1) in
  let in2 = input.(size 2) in
  let in3 = input.(size 3) in
  let o0 = out.(size 0) in
  let o1 = out.(size 1) in
  let o2 = out.(size 2) in
  let o3 = out.(size 3) in
  let open FStar.UInt128 in
  out.(size 0) <- o0 +. to_u128 in0;
  out.(size 1) <- o1 +. to_u128 in1;
  out.(size 2) <- o2 +. to_u128 in2;
  out.(size 3) <- o3 +. to_u128 in3


// TODO: check that the downcast to u64 is indeed correct, otherwise this
// requires a special implementation of the multiplication
val felem_scalar: out:felem -> scalar:shiftval U128 ->
  Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let felem_scalar out scalar =
  let o0 = out.(size 0) in
  let o1 = out.(size 1) in
  let o2 = out.(size 2) in
  let o3 = out.(size 3) in
  // let o0 = uint128_to_uint64 o0 in
  // let o1 = uint128_to_uint64 o1 in
  // let o2 = uint128_to_uint64 o2 in
  // let o3 = uint128_to_uint64 o3 in
  (* let scalar = scalar in *)
  out.(size 0) <- shift_left o0 scalar;
  out.(size 1) <- shift_left o1 scalar;
  out.(size 2) <- shift_left o2 scalar;
  out.(size 3) <- shift_left o3 scalar


// TODO: check that the downcast to u64 is indeed correct, otherwise this
// requires a special implementation of the multiplication
val longfelem_scalar: out:longfelem -> scalar:shiftval U128 ->
  Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let longfelem_scalar out scalar =
  let o0 = out.(size 0) in
  let o1 = out.(size 1) in
  let o2 = out.(size 2) in
  let o3 = out.(size 3) in
  let o4 = out.(size 4) in
  let o5 = out.(size 5) in
  let o6 = out.(size 6) in
  let o7 = out.(size 7) in
  out.(size 0) <- shift_left o0 scalar;
  out.(size 1) <- shift_left o1 scalar;
  out.(size 2) <- shift_left o2 scalar;
  out.(size 3) <- shift_left o3 scalar;
  out.(size 4) <- shift_left o4 scalar;
  out.(size 5) <- shift_left o5 scalar;
  out.(size 6) <- shift_left o6 scalar;
  out.(size 7) <- shift_left o7 scalar
  // out.(0) <- mul_wide o0 scalar;
  // out.(1) <- mul_wide o1 scalar;
  // out.(2) <- mul_wide o2 scalar;
  // out.(3) <- mul_wide o3 scalar;
  // out.(4) <- mul_wide o4 scalar;
  // out.(5) <- mul_wide o5 scalar;
  // out.(6) <- mul_wide o6 scalar;
  // out.(7) <- mul_wide o7 scalar

inline_for_extraction
val load128: high:uint64 -> low:uint64 -> Tot (z:uint128{uint_v z = pow2 64 * (uint_v high) + (uint_v low)})
let load128 h l =
  let hs = to_u128 h <<. (size_to_uint32 (size 64)) in
  let ls = to_u128 l in
  (* Math.Lemmas.modulo_lemma (UInt64.v h * pow2 64) (pow2 128); *)
  (* UInt.logor_disjoint #128 (v hs) (v ls) 64; *)
  hs |. ls


(* Put in uint128 form*)
let two105m41m9 = load128 (u64 0x1ffffffffff) (u64 0xfffffdfffffffe00)
let two105      = load128 (u64 0x20000000000) (u64 0)
let two105m41p9 = load128 (u64 0x1ffffffffff) (u64 0xfffffe0000000200)

let two107m43m11 = load128 (u64 0x7ffffffffff) (u64 0xfffff7fffffff800)
let two107       = load128 (u64 0x80000000000) (u64 0)
let two107m43p11 = load128 (u64 0x7ffffffffff) (u64 0xfffff80000000800)

let two64m0     = to_u128 (u64 0xffffffffffffffff)
let two110p32m0 = load128 (u64 0x400000000000) (u64 0x00000000ffffffff)
let two64m46    = to_u128 (u64 0xffffc00000000000)
let two64m32    = to_u128 (u64 0xffffffff00000000)

let two70m8p6     = load128 (u64 0x3f) (u64 0xffffffffffffff40)
let two70p40      = load128 (u64 0x40) (u64 0x0000010000000000)
let two70         = load128 (u64 0x40) (u64 0x0000000000000000)
let two70m40m38p6 = load128 (u64 0x3f) (u64 0xfffffec000000040)
let two70m6       = load128 (u64 0x3f) (u64 0xffffffffffffffc0)

let two100m36m4 = load128 (u64 0xfffffffff) (u64 0xffffffeffffffff0)
let two100      = load128 (u64 0x1000000000) (u64 0x0)
let two100m36p4 = load128 (u64 0xfffffffff) (u64 0xfffffff000000010)


val zero105: unit -> StackInline felem
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))
let zero105 () = createL [two105m41m9; two105; two105m41p9; two105m41p9]


val zero107: unit -> StackInline felem
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))
let zero107 () = createL [two107m43m11; two107; two107m43p11; two107m43p11]

val zero110: unit -> StackInline felem
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))
let zero110 () = createL [two64m0; two110p32m0; two64m46; two64m32]

val zero100: unit -> StackInline felem
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))
let zero100 () = createL [two100m36m4; two100; two100m36p4; two100m36p4]

val smallfelem_neg: out:felem -> small:smallfelem -> Stack unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))
let smallfelem_neg out small =
  let zero105 = zero105 () in
  let small0 = small.(size 0) in
  let small1 = small.(size 1) in
  let small2 = small.(size 2) in
  let small3 = small.(size 3) in
  let zero0  = zero105.(size 0) in
  let zero1  = zero105.(size 1) in
  let zero2  = zero105.(size 2) in
  let zero3  = zero105.(size 3) in
  out.(size 0) <- zero0 -. (to_u128 small0);
  out.(size 1) <- zero1 -. (to_u128 small1);
  out.(size 2) <- zero2 -. (to_u128 small2);
  out.(size 3) <- zero3 -. (to_u128 small3)

val felem_diff:
  out:felem -> input:felem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let felem_diff out input =
  push_frame();
  let zero105 = zero105 () in
  let open FStar.UInt128 in
  let input0 = input.(size 0) in
  let input1 = input.(size 1) in
  let input2 = input.(size 2) in
  let input3 = input.(size 3) in
  let out0 = out.(size 0) in
  let out1 = out.(size 1) in
  let out2 = out.(size 2) in
  let out3 = out.(size 3) in
  let zero0  = zero105.(size 0) in
  let zero1  = zero105.(size 1) in
  let zero2  = zero105.(size 2) in
  let zero3  = zero105.(size 3) in
  let out0 = zero0 +. out0 in
  let out1 = zero1 +. out1 in
  let out2 = zero2 +. out2 in
  let out3 = zero3 +. out3 in
  out.(size 0) <- out0 -. input0;
  out.(size 1) <- out1 -. input1;
  out.(size 2) <- out2 -. input2;
  out.(size 3) <- out3 -. input3;
  pop_frame()


val felem_diff_zero107:
  out:felem -> input:felem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let felem_diff_zero107 out input =
  push_frame();
  let zero107 = zero107 () in
  let input0 = input.(size 0) in
  let input1 = input.(size 1) in
  let input2 = input.(size 2) in
  let input3 = input.(size 3) in
  let out0 = out.(size 0) in
  let out1 = out.(size 1) in
  let out2 = out.(size 2) in
  let out3 = out.(size 3) in
  let zero0  = zero107.(size 0) in
  let zero1  = zero107.(size 1) in
  let zero2  = zero107.(size 2) in
  let zero3  = zero107.(size 3) in
  let out0 = zero0 +. out0 in
  let out1 = zero1 +. out1 in
  let out2 = zero2 +. out2 in
  let out3 = zero3 +. out3 in
  out.(size 0) <- out0 -. input0;
  out.(size 1) <- out1 -. input1;
  out.(size 2) <- out2 -. input2;
  out.(size 3) <- out3 -. input3;
  pop_frame()


val longfelem_diff:
  out:longfelem -> input:longfelem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let longfelem_diff out input =
  push_frame();
  let input0 = input.(size 0) in
  let input1 = input.(size 1) in
  let input2 = input.(size 2) in
  let input3 = input.(size 3) in
  let input4 = input.(size 4) in
  let input5 = input.(size 5) in
  let input6 = input.(size 6) in
  let input7 = input.(size 7) in
  let out0 = out.(size 0) in
  let out1 = out.(size 1) in
  let out2 = out.(size 2) in
  let out3 = out.(size 3) in
  let out4 = out.(size 4) in
  let out5 = out.(size 5) in
  let out6 = out.(size 6) in
  let out7 = out.(size 7) in
  let out0 =  two70m8p6 +. out0 in
  let out1 = two70p40 +. out1 in
  let out2 = two70 +. out2 in
  let out3 = two70m40m38p6 +. out3 in
  let out4 = two70m6 +. out4 in
  let out5 = two70m6 +. out5 in
  let out6 = two70m6 +. out6 in
  let out7 = two70m6 +. out7 in
  out.(size 0) <- out0 -. input0;
  out.(size 1) <- out1 -. input1;
  out.(size 2) <- out2 -. input2;
  out.(size 3) <- out3 -. input3;
  out.(size 4) <- out4 -. input4;
  out.(size 5) <- out5 -. input5;
  out.(size 6) <- out6 -. input6;
  out.(size 7) <- out7 -. input7;
  pop_frame()


// TODO: This function (at least) is bugged, FIXME
val felem_shrink:
  out:smallfelem -> input:felem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let felem_shrink out input =
  push_frame();
  let tmp = create #uint128 #4 (size 4) (u128 0) in
  let zero110 = zero110 () in
  let kPrime  = kPrime () in
  let kPrime3Test = (u64 0x7fffffff00000001) in
  let input0 = input.(size 0) in
  let input1 = input.(size 1) in
  let input2 = input.(size 2) in
  let input3 = input.(size 3) in
  let zero0  = zero110.(size 0) in
  let zero1  = zero110.(size 1) in
  let zero2  = zero110.(size 2) in
  let zero3  = zero110.(size 3) in
  let kPrime0 = kPrime.(size 0) in
  let kPrime1 = kPrime.(size 1) in
  let kPrime2 = kPrime.(size 2) in
  let kPrime3 = kPrime.(size 3) in
  // TODO: replace with a primitive to call the high word only
  let tmp3 = zero3 +. input3 +. (input2 >>. (size_to_uint32 (size 64))) in
  // tmp.(3ul) <- zero3 +. input3 +. (input2 >>^ 64ul);
  let tmp2 = zero2 +. (to_u128 (to_u64 input2)) in
// BB.  let tmp2 = zero2 +. (uint64_to_uint128 (uint128_to_uint64 input2)) in
  // tmp.(2ul) <- zero2 +. (uint64_to_uint128 (uint128_to_uint64 input2));
  let tmp0 = zero0 +. input0 in
  // tmp.(0ul) <- zero0 +. input0;
  let tmp1 = zero1 +. input1 in
  // tmp.(1ul) <- zero1 +. input1;

  // let tmp2 = tmp.(2ul) in
  // let tmp3 = tmp.(3ul) in
  let a = tmp3 >>. (size_to_uint32 (size 64)) in
  let tmp3 = to_u128 (to_u64 tmp3) in
// BB.  (* let tmp3 = uint64_to_uint128 (uint128_to_uint64 tmp3) in *)
  let tmp3 = tmp3 -. a in
  let tmp3 = tmp3 +. (a <<. (size_to_uint32 (size 32))) in

  let b = a in
  let a = tmp3 >>. (size_to_uint32 (size 64)) in
  let b = b +. a in
  let tmp3 = to_u128 (to_u64 tmp3) in
  let tmp3 = tmp3 -. a in
  let tmp3 = tmp3 +. (a <<. (size_to_uint32 (size 32))) in

  // let tmp0 = tmp.(0ul) in
  let tmp0 = tmp0 +. b in
  // let tmp1 = tmp.(1ul) in
  let tmp1 = tmp1 -. (b <<. (size_to_uint32 (size 32))) in

  // TODO: better implementation
  // let high = tmp3 >>^ 64ul in
  let high = to_u64 (gte_mask tmp3 (load128 (u64 0x1) (u64 0x0))) in

  // TODO: better implementation
  let low = to_u64 tmp3 in
  let mask = gte_mask low (u64 0x8000000000000000) in

  let low = low &. (u64 0x7fffffffffffffff) in
  let low = gte_mask kPrime3Test low in
  let low = lognot low in

  let mask = ((mask &. low) |. high) in

  let tmp0 = tmp0 -. to_u128 (mask &. kPrime0) in
  let tmp1 = tmp1 -. to_u128 (mask &. kPrime1) in
  let tmp3 = tmp3 -. to_u128 (mask &. kPrime3) in

  let tmp1 = tmp1 +. (tmp0 >>. (size_to_uint32 (size 64))) in
  let tmp0 = to_u64 tmp0 in
  let tmp2 = tmp2 +. (tmp1 >>. (to_shiftval 64)) in
  let tmp1 = to_u64 tmp1 in
  let tmp3 = tmp3 +. (tmp2 >>. (to_shiftval 64)) in
  let tmp2 = to_u64 tmp2 in

  out.(size 0) <- tmp0;
  out.(size 1) <- tmp1;
  out.(size 2) <- tmp2;
  out.(size 3) <- to_u64 tmp3;
  pop_frame ()


val smallfelem_expand:
  out:felem -> input:smallfelem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let smallfelem_expand out input =
  let input0 = input.(size 0) in
  let input1 = input.(size 1) in
  let input2 = input.(size 2) in
  let input3 = input.(size 3) in
  out.(size 0) <- to_u128 input0;
  out.(size 1) <- to_u128 input1;
  out.(size 2) <- to_u128 input2;
  out.(size 3) <- to_u128 input3

val smallfelem_square:
  out:longfelem -> small:smallfelem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let smallfelem_square out small =
  let small0 = small.(size 0) in
  let small1 = small.(size 1) in
  let small2 = small.(size 2) in
  let small3 = small.(size 3) in

  let a = mul_wide small0 small0 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. to_shiftval 64 in
  let out0 = low in
  let out1 = high in

  let a = mul_wide small0 small1 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. (to_shiftval 64) in
  let out1 = out1 +. low in
  let out1 = out1 +. low in
  let out2 = high in

  let a = mul_wide small0 small2 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. to_shiftval 64 in
  let out2 = out2 +. low in
  let out2 = out2 <<. to_shiftval 1 in
  let out3 = high in

  let a = mul_wide small0 small3 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. to_shiftval 64 in
  let out3 = out3 +. low in
  let out4 = high in

  let a = mul_wide small1 small2 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. to_shiftval 64 in
  let out3 = out3 +. low in
  let out3 = out3 <<. to_shiftval 1 in
  let out4 = out4 +. high in

  let a = mul_wide small1 small1 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. to_shiftval 64 in
  let out2 = out2 +. low in
  let out3 = out3 +. high in

  let a = mul_wide small1 small3 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. to_shiftval 64 in
  let out4 = out4 +. low in
  let out4 = out4 <<. to_shiftval 1 in
  let out5 = high in

  let a = mul_wide small2 small3 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. to_shiftval 64 in
  let out5 = out5 +. low in
  let out5 = out5 <<. to_shiftval 1 in
  let out6 = high in
  let out6 = out6 +. high in

  let a = mul_wide small2 small2 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. to_shiftval 64 in
  let out4 = out4 +. low in
  let out5 = out5 +. high in

  let a = mul_wide small3 small3 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. to_shiftval 64 in
  let out6 = out6 +. low in
  let out7 = high in

  out.(size 0) <- out0;
  out.(size 1) <- out1;
  out.(size 2) <- out2;
  out.(size 3) <- out3;
  out.(size 4) <- out4;
  out.(size 5) <- out5;
  out.(size 6) <- out6;
  out.(size 7) <- out7


val felem_square:
  out:longfelem -> input:felem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let felem_square out input =
  push_frame();
  let small = create (size 4) (u64 0) in
  felem_shrink small input;
  smallfelem_square out small;
  pop_frame()


val smallfelem_mul:
  out:longfelem -> small1:smallfelem -> small2:smallfelem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let smallfelem_mul out small1 small2 =
  let small10 = small1.(size 0) in
  let small11 = small1.(size 1) in
  let small12 = small1.(size 2) in
  let small13 = small1.(size 3) in
  let small20 = small2.(size 0) in
  let small21 = small2.(size 1) in
  let small22 = small2.(size 2) in
  let small23 = small2.(size 3) in

  let a = mul_wide small10 small20 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. to_shiftval 64 in
  let out0 = low in
  let out1 = high in

  let a = mul_wide small10 small21 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. to_shiftval 64 in
  let out1 = out1 +. low in
  let out2 = high in

  let a = mul_wide small11 small20 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. to_shiftval 64 in
  let out1 = out1 +. low in
  let out2 = out2 +. high in

  let a = mul_wide small10 small22 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. to_shiftval 64 in
  let out2 = out2 +. low in
  let out3 = high in

  let a = mul_wide small11 small21 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. to_shiftval 64 in
  let out2 = out2 +. low in
  let out3 = out3 +. high in

  let a = mul_wide small12 small20 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. to_shiftval 64 in
  let out2 = out2 +. low in
  let out3 = out3 +. high in

  let a = mul_wide small10 small23 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. to_shiftval 64 in
  let out3 = out3 +. low in
  let out4 = high in

  let a = mul_wide small11 small22 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. to_shiftval 64 in
  let out3 = out3 +. low in
  let out4 = out4 +. high in

  let a = mul_wide small12 small21 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. to_shiftval 64 in
  let out3 = out3 +. low in
  let out4 = out4 +. high in

  let a = mul_wide small13 small20 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. to_shiftval 64 in
  let out3 = out3 +. low in
  let out4 = out4 +. high in

  let a = mul_wide small11 small23 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. to_shiftval 64 in
  let out4 = out4 +. low in
  let out5 = high in

  let a = mul_wide small12 small22 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. to_shiftval 64 in
  let out4 = out4 +. low in
  let out5 = out5 +. high in

  let a = mul_wide small13 small21 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. to_shiftval 64 in
  let out4 = out4 +. low in
  let out5 = out5 +. high in

  let a = mul_wide small12 small23 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. to_shiftval 64 in
  let out5 = out5 +. low in
  let out6 = high in

  let a = mul_wide small13 small22 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. to_shiftval 64 in
  let out5 = out5 +. low in
  let out6 = out6 +. high in

  let a = mul_wide small13 small23 in
  let low = to_u128 (to_u64 a) in
  let high = a >>. to_shiftval 64 in
  let out6 = out6 +. low in
  let out7 = high in

  out.(size 0) <- out0;
  out.(size 1) <- out1;
  out.(size 2) <- out2;
  out.(size 3) <- out3;
  out.(size 4) <- out4;
  out.(size 5) <- out5;
  out.(size 6) <- out6;
  out.(size 7) <- out7

val felem_mul:
  out:longfelem -> in1:felem -> in2:felem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let felem_mul out in1 in2 =
  push_frame();
  let small1 = create (size 4) (u64 0) in
  let small2 = create (size 4) (u64 0) in
  felem_shrink small1 in1;
  felem_shrink small2 in2;
  smallfelem_mul out small1 small2;
  pop_frame()

val felem_small_mul:
  out:longfelem -> small1:smallfelem -> in2:felem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let felem_small_mul out small1 in2 =
  push_frame();
  let small2 = create (size 4) (u64 0) in
  felem_shrink small2 in2;
  smallfelem_mul out small1 small2;
  pop_frame()

val felem_reduce_:
  out:felem -> input:longfelem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let felem_reduce_ out input =
  let out0 = out.(size 0) in
  let out1 = out.(size 1) in
  let out2 = out.(size 2) in
  let out3 = out.(size 3) in
  let input0 = input.(size 0) in
  let input1 = input.(size 1) in
  let input2 = input.(size 2) in
  let input3 = input.(size 3) in
  let input4 = input.(size 4) in
  let input5 = input.(size 5) in
  let input6 = input.(size 6) in
  let input7 = input.(size 7) in
  let open FStar.UInt128 in
  let c = input4 +. (input5 <<. to_shiftval 32) in
  let out0 = out0 +. c in
  let out3 = out3 -. c in
  // let c = input5 -. input7 in
  let out1 = out1 +. input5 -. input7 in
  let out2 = out2 +. input7 -. input5 in
  // let out1 = out1 +. c in
  // let out2 = out2 -. c in
  let out1 = out1 -. (input4 <<. to_shiftval 32) in
  let out3 = out3 +. (input4 <<. to_shiftval 32) in
  let out2 = out2 -. (input5 <<. to_shiftval 32) in
  let out0 = out0 -. input6 in
  let out0 = out0 -. (input6 <<. to_shiftval 32) in
  let out1 = out1 +. (input6 <<. to_shiftval 33) in
  let out2 = out2 +. (input6 <<. to_shiftval 1)  in
  let out3 = out3 -. (input6 <<. to_shiftval 32) in
  let out0 = out0 -. input7 in
  let out0 = out0 -. (input7 <<. to_shiftval 32) in
  let out2 = out2 +. (input7 <<. to_shiftval 33) in
  let out3 = out3 +. ((input7 <<. to_shiftval 1) +. input7) in
  out.(size 0) <- out0;
  out.(size 1) <- out1;
  out.(size 2) <- out2;
  out.(size 3) <- out3

val felem_reduce:
  out:felem -> input:longfelem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let felem_reduce out input =
  let open FStar.UInt128 in
  push_frame();
  let zero100 = zero100() in
  let zero0 = zero100.(size 0) in
  let zero1 = zero100.(size 1) in
  let zero2 = zero100.(size 2) in
  let zero3 = zero100.(size 3) in
  let input0 = input.(size 0) in
  let input1 = input.(size 1) in
  let input2 = input.(size 2) in
  let input3 = input.(size 3) in
  out.(size 0) <- input0 +. zero0;
  out.(size 1) <- input1 +. zero1;
  out.(size 2) <- input2 +. zero2;
  out.(size 3) <- input3 +. zero3;
  felem_reduce_ out input;
  pop_frame()

val felem_reduce_zero105:
  out:felem -> input:longfelem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let felem_reduce_zero105 out input =
  let open FStar.UInt128 in
  push_frame();
  let zero105 = zero105() in
  let zero0 = zero105.(size 0) in
  let zero1 = zero105.(size 1) in
  let zero2 = zero105.(size 2) in
  let zero3 = zero105.(size 3) in
  let input0 = input.(size 0) in
  let input1 = input.(size 1) in
  let input2 = input.(size 2) in
  let input3 = input.(size 3) in
  out.(size 0) <- input0 +. zero0;
  out.(size 1) <- input1 +. zero1;
  out.(size 2) <- input2 +. zero2;
  out.(size 3) <- input3 +. zero3;
  felem_reduce_ out input;
  pop_frame()

val subtract_u64:
  result:uint64 -> v:uint64 -> Tot (tuple2 uint64 uint64)
let subtract_u64 result v' =
  let r = to_u128 result in
  let r = r -. to_u128 v' in
  (* WAS let r = (r -%^ to_u128 v') in *)
  let carry = (to_u64 (r >>. to_shiftval 64)) &. (u64 1) in
  let result = to_u64 r in
  result, carry

val felem_contract:
  out:smallfelem -> input:felem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let felem_contract out input =
  push_frame();
  let all_equal_so_far = u64 0 in
  let result = u64 0 in
  felem_shrink out input;
  let all_equal_so_far = all_equal_so_far -. (u64 1) in
  (* WAS let all_equal_so_far = FStar.UInt64.(all_equal_so_far -%^ 1uL) in *)

  let kPrime = kPrime() in
  let kPrime0 = kPrime.(size 0) in
  let kPrime1 = kPrime.(size 1) in
  let kPrime2 = kPrime.(size 2) in
  let kPrime3 = kPrime.(size 3) in
  let out0 = out.(size 0) in
  let out1 = out.(size 1) in
  let out2 = out.(size 2) in
  let out3 = out.(size 3) in
  let a = to_u128 kPrime0 -. to_u128 out0 in
  let result = (result |. (all_equal_so_far &. (to_u64 (a >>. to_shiftval 64)))) in

  let equal = kPrime3 ^. out3 in
  let equal = equal -. (u64 1) in
  let equal = equal &. (equal <<. to_shiftval 32) in
  let equal = equal &. (equal <<. to_shiftval 16) in
  let equal = equal &. (equal <<. to_shiftval 8) in
  let equal = equal &. (equal <<. to_shiftval 4) in
  let equal = equal &. (equal <<. to_shiftval 2) in
  let equal = equal &. (equal <<. to_shiftval 1) in
  let equal = gte_mask equal (u64 0x1000000000000000) in
  let all_equal_so_far = all_equal_so_far &. equal in


  let equal = kPrime2 ^. out2 in
  let equal = equal -. (u64 1) in
  let equal = equal &. (equal <<. to_shiftval 32) in
  let equal = equal &. (equal <<. to_shiftval 16) in
  let equal = equal &. (equal <<. to_shiftval 8) in
  let equal = equal &. (equal <<. to_shiftval 4) in
  let equal = equal &. (equal <<. to_shiftval 2) in
  let equal = equal &. (equal <<. to_shiftval 1) in
  let equal = gte_mask equal (u64 0x1000000000000000) in
  let all_equal_so_far = all_equal_so_far &. equal in

  let equal = kPrime1 ^. out1 in
  let equal = equal -. (u64 1) in
  let equal = equal &. (equal <<. to_shiftval 32) in
  let equal = equal &. (equal <<. to_shiftval 16) in
  let equal = equal &. (equal <<. to_shiftval 8) in
  let equal = equal &. (equal <<. to_shiftval 4) in
  let equal = equal &. (equal <<. to_shiftval 2) in
  let equal = equal &. (equal <<. to_shiftval 1) in
  let equal = gte_mask equal (u64 0x1000000000000000) in
  let all_equal_so_far = all_equal_so_far &. equal in

  let equal = kPrime0 ^. out0 in
  let equal = equal -. (u64 1) in
  let equal = equal &. (equal <<. to_shiftval 32) in
  let equal = equal &. (equal <<. to_shiftval 16) in
  let equal = equal &. (equal <<. to_shiftval 8) in
  let equal = equal &. (equal <<. to_shiftval 4) in
  let equal = equal &. (equal <<. to_shiftval 2) in
  let equal = equal &. (equal <<. to_shiftval 1) in
  let equal = gte_mask equal (u64 0x1000000000000000) in
  let all_equal_so_far = all_equal_so_far &. equal in

  let result = result |. all_equal_so_far in

  let out0, carry = subtract_u64 out0 (result &. kPrime0) in
  let out1, carry = subtract_u64 out1 carry in
  let out2, carry = subtract_u64 out2 carry in
  let out3, carry = subtract_u64 out3 carry in

  let out1, carry = subtract_u64 out1 (result &. kPrime1) in
  let out2, carry = subtract_u64 out2 carry in
  let out3, carry = subtract_u64 out3 carry in

  let out2, carry = subtract_u64 out2 (result &. kPrime2) in
  let out3, carry = subtract_u64 out3 carry in

  let out3, carry = subtract_u64 out3 (result &. kPrime3) in
  pop_frame()

val smallfelem_mul_contract:
  out:smallfelem -> in1:smallfelem -> in2:smallfelem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let smallfelem_mul_contract out in1 in2 =
  push_frame();
  let longtmp = create (size 8) (u128 0) in
  let tmp     = create (size 4) (u128 0) in
  smallfelem_mul longtmp in1 in2;
  felem_reduce tmp longtmp;
  felem_contract out tmp;
  pop_frame()

val smallfelem_is_zero:
  small:smallfelem -> Stack limb
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let smallfelem_is_zero small =
  push_frame();
  let kPrime = kPrime() in
  let kPrime0 = kPrime.(size 0) in
  let kPrime1 = kPrime.(size 1) in
  let kPrime2 = kPrime.(size 2) in
  let kPrime3 = kPrime.(size 3) in
  let small0 = small.(size 0) in
  let small1 = small.(size 1) in
  let small2 = small.(size 2) in
  let small3 = small.(size 3) in
  let is_zero = (small0 |. small1 |. small2 |. small3) in
  let is_zero = eq_mask is_zero (u64 0) in
  let is_p = (small0 ^. kPrime0) |. (small1 ^. kPrime1) |. (small2 ^. kPrime2) |. (small3 ^. kPrime3) in
  let is_p = eq_mask is_p (u64 0) in
  let is_zero = is_zero |. is_p in
  let result = (to_u128 is_zero |. (to_u128 is_zero <<. to_shiftval 64)) in
  pop_frame();
  result

val smallfelem_is_zero_int:
  small:smallfelem -> Stack uint32
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let smallfelem_is_zero_int small =
  let w = smallfelem_is_zero small in
  to_u32 (to_u64 (w &. (u128 1)))


val felem_inv_loop1_iter: tmp:longfelem -> ftmp:felem ->
  Stack unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))

let felem_inv_loop1_iter tmp ftmp =
  felem_square tmp ftmp;
  felem_reduce ftmp tmp

val felem_inv_loop1: n:size_t -> tmp:longfelem -> ftmp:felem ->
  Stack unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))
let felem_inv_loop1 n tmp ftmp =
  let h0 = ST.get () in
  loop_nospec #h0 n tmp
  (fun i -> felem_inv_loop1_iter tmp ftmp)


val felem_inv_loop2_iter: ftmp2:felem -> tmp:longfelem ->
  Stack unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))

let felem_inv_loop2_iter ftmp2 tmp =
  felem_square tmp ftmp2;
  felem_reduce ftmp2 tmp


val felem_inv_loop2: n:size_t -> ftmp:felem -> tmp:longfelem ->
  Stack unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))
let felem_inv_loop2 n ftmp tmp =
  let h0 = ST.get () in
  loop_nospec #h0 n tmp
  (fun i -> felem_inv_loop2_iter ftmp tmp)


val felem_inv:
  out:felem -> input:felem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let felem_inv out input =
  push_frame();
  let z = u128 0 in
  let ftmp = create (size 4) z in
  let ftmp2 = create (size 4) z in
  let e2 = create (size 4) z in
  let e4 = create (size 4) z in
  let e8 = create (size 4) z in
  let e16 = create (size 4) z in
  let e32 = create (size 4) z in
  let e64 = create (size 4) z in
  let tmp = create (size 4) z in
  felem_square tmp input;
  felem_reduce ftmp tmp;
  felem_mul tmp input ftmp;
  felem_reduce ftmp tmp;
  felem_assign e2 ftmp;
  felem_square tmp ftmp;
  felem_reduce ftmp tmp;
  felem_square tmp ftmp;
  felem_reduce ftmp tmp;
  felem_mul tmp ftmp e2;
  felem_reduce ftmp tmp;
  felem_assign e4 ftmp;
  felem_square tmp ftmp;
  felem_reduce ftmp tmp;
  felem_square tmp ftmp;
  felem_reduce ftmp tmp;
  felem_square tmp ftmp;
  felem_reduce ftmp tmp;
  felem_square tmp ftmp;
  felem_reduce ftmp tmp;
  felem_mul tmp ftmp e4;
  felem_reduce ftmp tmp;
  felem_assign e8 ftmp;
  felem_inv_loop1 (size 8) tmp ftmp;
  felem_mul tmp ftmp e8;
  felem_reduce ftmp tmp;
  felem_assign e16 ftmp;
  felem_inv_loop1 (size 16) tmp ftmp;
  felem_mul tmp ftmp e16;
  felem_reduce ftmp tmp;
  felem_assign e32 ftmp;
  felem_inv_loop1 (size 32) tmp ftmp;
  felem_assign e64 ftmp;
  felem_mul tmp ftmp input;
  felem_reduce ftmp tmp;
  felem_inv_loop1 (size 192) tmp ftmp;
  felem_mul tmp e64 e32;
  felem_reduce ftmp2 tmp;
  felem_inv_loop2 (size 16) ftmp tmp;
  felem_mul tmp ftmp2 e16;
  felem_reduce ftmp2 tmp;
  felem_inv_loop2 (size 8) ftmp tmp;
  felem_mul tmp ftmp2 e8;
  felem_reduce ftmp2 tmp;
  felem_inv_loop2 (size 4) ftmp tmp;
  felem_mul tmp ftmp2 e4;
  felem_reduce ftmp2 tmp;
  felem_square tmp ftmp2;
  felem_reduce ftmp2 tmp;
  felem_square tmp ftmp2;
  felem_reduce ftmp2 tmp;
  felem_mul tmp ftmp2 e2;
  felem_reduce ftmp2 tmp;
  felem_square tmp ftmp2;
  felem_reduce ftmp2 tmp;
  felem_square tmp ftmp2;
  felem_reduce ftmp2 tmp;
  felem_mul tmp ftmp2 input;
  felem_reduce ftmp2 tmp;

  felem_mul tmp ftmp2 ftmp;
  felem_reduce out tmp;
  pop_frame()

val smallfelem_inv_contract:
  out:smallfelem -> input:smallfelem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let smallfelem_inv_contract out input =
  push_frame();
  let tmp = create (size 4) (u128 0) in
  smallfelem_expand tmp input;
  felem_inv tmp tmp;
  felem_contract out tmp;
  pop_frame()


(* ******************************************************* *)
(*      END OF BIGNUM CODE / BEGINNING OF CURVE CODE       *)
(* ******************************************************* *)


val point_double:
  x_out:felem -> y_out:felem -> z_out:felem ->
  x_in:felem -> y_in:felem -> z_in:felem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let point_double x_out y_out z_out x_in y_in z_in =
  push_frame();
  let tmp = create (size 8) (u128 0) in
  let tmp2 = create (size 8) (u128 0) in
  let delta = create (size 4) (u128 0) in
  let gamma = create (size 4) (u128 0) in
  let beta = create (size 4) (u128 0) in
  let alpha = create (size 4) (u128 0) in
  let ftmp = create (size 4) (u128 0) in
  let ftmp2 = create (size 4) (u128 0) in
  let small1 = create (size 4) (u64 0) in
  let small2 = create (size 4) (u64 0) in

  felem_assign ftmp x_in;
  felem_assign ftmp2 x_in;

  felem_square tmp z_in;
  felem_reduce delta tmp;

  felem_square tmp y_in;
  felem_reduce gamma tmp;
  felem_shrink small1 gamma;

  felem_small_mul tmp small1 x_in;
  felem_reduce beta tmp;

  felem_diff ftmp delta;
  felem_sum ftmp2 delta;
  // TODO: check correctness
  felem_assign tmp ftmp2;
  felem_scalar ftmp2 (to_shiftval 1);
  felem_sum ftmp2 tmp;
  // END TODO
  felem_mul tmp ftmp ftmp2;
  felem_reduce alpha tmp;
  felem_shrink small2 alpha;

  smallfelem_square tmp small2;
  felem_reduce x_out tmp;
  felem_assign ftmp beta;
  felem_scalar ftmp (to_shiftval 3);
  felem_diff x_out ftmp;

  felem_sum delta gamma;
  felem_assign ftmp y_in;
  felem_sum ftmp z_in;
  felem_square tmp ftmp;
  felem_reduce z_out tmp;
  felem_diff z_out delta;

  felem_scalar beta (to_shiftval 2);
  felem_diff_zero107 beta x_out;
  felem_small_mul tmp small2 beta;
  smallfelem_square tmp2 small1;
  longfelem_scalar tmp2 (to_shiftval 3);
  longfelem_diff tmp tmp2;
  felem_reduce_zero105 y_out tmp;
  pop_frame()


val point_double_small:
  x_out:smallfelem -> y_out:smallfelem -> z_out:smallfelem ->
  x_in:smallfelem -> y_in:smallfelem -> z_in:smallfelem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let point_double_small x_out y_out z_out x_in y_in z_in =
  push_frame();
  let felem_x_out = create_felem () in
  let felem_y_out = create_felem () in
  let felem_z_out = create_felem () in
  let felem_x_in = create_felem () in
  let felem_y_in = create_felem () in
  let felem_z_in = create_felem () in
  point_double felem_x_out felem_y_out felem_z_out felem_x_in felem_y_in felem_z_in;
  felem_shrink x_out felem_x_out;
  felem_shrink y_out felem_y_out;
  felem_shrink z_out felem_z_out;
  pop_frame()


val copy_conditional_iter:
  out:felem -> input:felem -> mask:limb -> i:size_t -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let copy_conditional_iter out input mask i =
  let inputi = input.(i) in
  let outi = out.(i) in
  let tmp = mask &. (inputi ^. outi) in
      // let tmp = mask &. input.(FStar.UInt32.(nlimbs' -. 1ul -. i)) in
  out.(i) <- outi ^. tmp


val copy_conditional:
  out:felem -> input:felem -> mask:limb -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let copy_conditional out input mask =
  let h0 = ST.get () in
  loop_nospec #h0 (size nlimbs) out
  (fun i -> copy_conditional_iter out input mask i)


val copy_small_conditional_iter:
  out:felem -> input:smallfelem -> mask:limb -> i:size_t -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let copy_small_conditional_iter out input mask i =
  let mask64 = to_u64 mask in
  let inputi = input.(i) in
  let outi = out.(i) in
  let tmp = (to_u128 (inputi &. mask64) |. (outi &. lognot mask)) in
  out.(i) <- tmp


val copy_small_conditional:
  out:felem -> input:smallfelem -> mask:limb -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let copy_small_conditional out input mask =
  let h0 = ST.get () in
  loop_nospec #h0 (size nlimbs) out
  (fun i -> copy_small_conditional_iter out input mask i)


val point_add:
  x3:felem -> y3:felem -> z3:felem ->
  x1:felem -> y1:felem -> z1:felem ->
  mixed:FStar.UInt32.t -> x2:smallfelem -> y2:smallfelem -> z2:smallfelem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let point_add x3 y3 z3 x1 y1 z1 mixed x2 y2 z2 =
  push_frame();
  let ftmp = create_felem() in
  let ftmp2 = create_felem() in
  let ftmp3 = create_felem() in
  let ftmp4 = create_felem() in
  let ftmp5 = create_felem() in
  let ftmp6 = create_felem() in
  let x_out = create_felem() in
  let y_out = create_felem() in
  let z_out = create_felem() in
  let tmp   = create_longfelem() in
  let tmp2   = create_longfelem() in
  let small1 = create_smallfelem() in
  let small2 = create_smallfelem() in
  let small3 = create_smallfelem() in
  let small4 = create_smallfelem() in
  let small5 = create_smallfelem() in

  felem_shrink small3 z1;

  let z1_is_zero = smallfelem_is_zero small3 in
  let z2_is_zero = smallfelem_is_zero z2 in

  smallfelem_square tmp small3;
  felem_reduce ftmp tmp;
  felem_shrink small1 ftmp;

  if (mixed = 0ul) then
    begin
      smallfelem_square tmp z2;
      felem_reduce ftmp2 tmp;
      felem_shrink small2 ftmp2;

      felem_shrink small5 x1;

      smallfelem_mul tmp small5 small2;
      felem_reduce ftmp3 tmp;

      felem_assign ftmp5 z1;
      felem_small_sum ftmp5 z2;

      felem_square tmp ftmp5;
      felem_reduce ftmp5 tmp;
      felem_sum ftmp2 ftmp;
      felem_diff ftmp5 ftmp2;

      smallfelem_mul tmp small2 z2;
      felem_reduce ftmp2 tmp;

      felem_mul tmp y1 ftmp2;
      felem_reduce ftmp6 tmp
    end
  else
    begin
      felem_assign ftmp3 x1;

      felem_assign ftmp5 z1;
      felem_scalar ftmp5 (to_shiftval 1);

      felem_assign ftmp6 y1
    end;

  smallfelem_mul tmp x2 small1;
  felem_reduce ftmp4 tmp;

  felem_diff_zero107 ftmp4 ftmp3;
  felem_shrink small4 ftmp4;

  let x_equal = smallfelem_is_zero small4 in

  felem_small_mul tmp small4 ftmp5;
  felem_reduce z_out tmp;

  smallfelem_mul tmp small1 small3;
  felem_reduce ftmp tmp;

  felem_small_mul tmp y2 ftmp;
  felem_reduce ftmp5 tmp;

  felem_diff_zero107 ftmp5 ftmp6;
  felem_scalar ftmp5 (to_shiftval 1);
  felem_shrink small1 ftmp5;
  let y_equal = smallfelem_is_zero small1 in

  let zero = (u128 0) in
  if  ((x_equal <> zero) && (y_equal <> zero) && not(z1_is_zero <> zero) && not(z2_is_zero <> zero)) then
      begin
        point_double x3 y3 z3 x1 y1 z1
      end
  else
      begin
        felem_assign ftmp ftmp4;
        felem_scalar ftmp (to_shiftval 1);
        felem_square tmp ftmp;
        felem_reduce ftmp tmp;
        felem_mul tmp ftmp4 ftmp;
        felem_reduce ftmp2 tmp;
        felem_mul tmp ftmp3 ftmp;
        felem_reduce ftmp4 tmp;
        smallfelem_square tmp small1;
        felem_reduce x_out tmp;
        felem_assign ftmp3 ftmp4;
        felem_scalar ftmp4 (to_shiftval 1);
        felem_sum ftmp4 ftmp2;
        felem_diff x_out ftmp4;

        felem_diff_zero107 ftmp3 x_out;
        felem_small_mul tmp small1 ftmp3;
        felem_mul tmp2 ftmp6 ftmp2;
        longfelem_scalar tmp2 (to_shiftval 1);
        longfelem_diff tmp tmp2;
        felem_reduce_zero105 y_out tmp;

        copy_small_conditional x_out x2 z1_is_zero;
        copy_conditional x_out x1 z2_is_zero;
        copy_small_conditional y_out y2 z1_is_zero;
        copy_conditional y_out y1 z2_is_zero;
        copy_small_conditional z_out z2 z1_is_zero;
        copy_conditional z_out z1 z2_is_zero;
        felem_assign x3 x_out;
        felem_assign y3 y_out;
        felem_assign z3 z_out
      end;
  pop_frame()


val point_add_small:
  x3:smallfelem -> y3:smallfelem -> z3:smallfelem ->
  x1:smallfelem -> y1:smallfelem -> z1:smallfelem ->
  x2:smallfelem -> y2:smallfelem -> z2:smallfelem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let point_add_small x3 y3 z3 x1 y1 z1 x2 y2 z2 =
  push_frame();
  let felem_x3 = create_felem () in
  let felem_y3 = create_felem () in
  let felem_z3 = create_felem () in
  let felem_x1 = create_felem () in
  let felem_y1 = create_felem () in
  let felem_z1 = create_felem () in
  smallfelem_expand felem_x1 x1;
  smallfelem_expand felem_y1 y1;
  smallfelem_expand felem_z1 z1;
  point_add felem_x3 felem_y3 felem_z3 felem_x1 felem_y1 felem_z1 0ul x2 y2 z2;
  felem_shrink x3 felem_x3;
  felem_shrink y3 felem_y3;
  felem_shrink z3 felem_z3;
  pop_frame()

// ============================
// Taken from the ED25519 code
// ============================

type point = lbuffer limb 12

let get_x (p:point) = sub #limb #12 #4 p (size 0) (size 4)
let get_y (p:point) = sub #limb #12 #4 p (size 4) (size 4)
let get_z (p:point) = sub #limb #12 #4 p (size 8) (size 4)

// TODO: implement
let disjoint_p (p:point) (q:point) = True

private
val ith_bit:
  k:lbuffer uint8 32 ->
  i:size_t{size_v i < 256} ->
  Stack uint8
    (requires (fun h -> live h k))
    (ensures (fun h0 z h1 -> True))
      (* h0 == h1 /\ live h0 k /\ *)
      (* Hacl.UInt8.v z == Spec.Ed25519.ith_bit (// reveal_sbytes *)
      (* (as_seq h0 k)) (UInt32.v i) *)
      (* /\ (Hacl.UInt8.v z == 0 \/ Hacl.UInt8.v z == 1))) *)
let ith_bit k i =
  assert_norm(pow2 1 = 2);
  assert_norm(pow2 3 = 8);
  assert_norm(pow2 5 = 32);
  assert_norm(pow2 8 = 256);
  let open FStar.UInt32 in
  let q = i >>. (to_shiftval 3) in
//  assert(v q = v i / 8);
  let r :shiftval U8 = to_u32 (i &. (size 7)) in
//  UInt.logand_mask (v i) 3;
//  assert(v r = v i % 8);
//  Math.Lemmas.lemma_div_lt (v i) 8 3;
  let kq = k.(q) in
  let kq' = (kq >>. r) in
  let z = (kq' &. (u8 1)) in
  (* UInt.logand_mask (Hacl.UInt8.v kq') 1; *)
  (* assert(Hacl.UInt8.v z = (Hacl.UInt8.v kq / pow2 (v r)) % 2); *)
  z

private
inline_for_extraction let mk_mask (iswap:uint128{uint_v iswap = 0 \/ uint_v iswap = 1}) :
  Tot (z:uint128{if uint_v iswap = 1 then uint_v z = pow2 64 - 1 else uint_v z = 0})
  = let swap = ((u128 0) -. iswap) in
    assert_norm((0 - 1) % pow2 64 = pow2 64 - 1);
    assert_norm((0 - 0) % pow2 64 = 0);
    swap



val swap_cond_inplace_inner:
  p:point -> q:point{disjoint_p p q} -> iswap:limb{uint_v iswap = 0 \/ uint_v iswap = 1} -> i:size_t ->
  Stack unit
    (requires (fun h -> True))
    (ensures  (fun h0 _ h1 -> True))
let swap_cond_inplace_inner p q iswap i =
  let mask = mk_mask iswap in
  let pi = p.(i) in
  let qi = q.(i) in
  let x  = mask &. (pi ^. qi) in
  let pi' = pi ^. x in
  let qi' = qi ^. x in
  p.(i) <- pi';
  q.(i) <- qi'


private
val swap_cond_inplace:
  p:point -> q:point{disjoint_p p q} -> i:limb{uint_v i = 0 \/ uint_v i = 1} ->
  Stack unit
    (requires (fun h -> True))
  (*     live h p /\ live h q /\ *)
  (*     ( let x1 = as_seq h (get_x p) in *)
  (*       let y1 = as_seq h (get_y p) in *)
  (*       let z1 = as_seq h (get_z p) in *)
  (*       True) /\ *)
  (*       // red_513 x1 /\ red_513 y1 /\ red_513 z1) /\ *)
  (*     ( let x2 = as_seq h (get_x q) in *)
  (*       let y2 = as_seq h (get_y q) in *)
  (*       let z2 = as_seq h (get_z q) in *)
  (*       True *)
  (*       // red_513 x2 /\ red_513 y2 /\ red_513 z2 *)
  (* ) )) *)
    (ensures (fun h0 _ h1 -> True))
    (*   live h1 p /\ live h1 q /\ modifies_2 p q h0 h1 /\ live h0 p /\ live h0 q /\ *)
    (*   ( let x1 = as_seq h0 (get_x p) in *)
    (*     let y1 = as_seq h0 (get_y p) in *)
    (*     let z1 = as_seq h0 (get_z p) in *)
    (*     let x2 = as_seq h0 (get_x q) in *)
    (*     let y2 = as_seq h0 (get_y q) in *)
    (*     let z2 = as_seq h0 (get_z q) in *)
    (*     let x1' = as_seq h1 (get_x p) in *)
    (*     let y1' = as_seq h1 (get_y p) in *)
    (*     let z1' = as_seq h1 (get_z p) in *)
    (*     let x2' = as_seq h1 (get_x q) in *)
    (*     let y2' = as_seq h1 (get_y q) in *)
    (*     let z2' = as_seq h1 (get_z q) in *)
    (*     True /\ *)
    (*   (if UInt128.v i = 1 then (x1' == x2 /\ y1' == y2 /\ z1' == z2 /\ *)
    (*                                 x2' == x1 /\ y2' == y1 /\ z2' == z1) *)
    (*      else (x1' == x1 /\ y1' == y1 /\ z1' == z1 /\ *)
    (*            x2' == x2 /\ y2' == y2 /\ z2' == z2))) *)
    (* )) *)
let swap_cond_inplace p q iswap =
  let h0 = ST.get () in
  loop_nospec #h0 (size 12) p // and q (modifies2)
  (fun i -> swap_cond_inplace_inner p q iswap i)


val point_mul_loop_step:
  #klen:size_nat ->
  pp:point ->
  ppq:point ->
  p:point ->
  pq:point ->
  k:lbuffer uint8 klen ->
  i:size_t ->
  Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let point_mul_loop_step #klen pp ppq p pq k i =
  push_frame();
  let x = create (size 4) (u64 0) in
  let y = create (size 4) (u64 0) in
  let z = create (size 4) (u64 0) in
  // TODO: change the algorithm, this is an ugly workaround due to OpenSSL's 'point_add' function
  let ith_bit = ith_bit k i in
  let ith_bit = to_u128 ith_bit in
  swap_cond_inplace p pq ith_bit;
  felem_shrink x (get_x pq);
  felem_shrink y (get_y pq);
  felem_shrink z (get_z pq);
  point_double (get_x pp) (get_y pp) (get_z pp) (get_x p) (get_y p) (get_z p);
  point_add (get_x ppq) (get_y ppq) (get_z ppq)
            (get_x p) (get_y p) (get_z p)
            0ul
            x y z;
           // (get_x pq) (get_y pq) (get_z pq);
  // let x0 = x.(0ul) in
  // let x1 = x.(1ul) in
  // let x2 = x.(2ul) in
  // let x3 = x.(3ul) in
  // ppq.(0ul) <- UInt128.to_u128 x0;
  // ppq.(1ul) <- UInt128.to_u128 x1;
  // ppq.(2ul) <- UInt128.to_u128 x2;
  // ppq.(3ul) <- UInt128.to_u128 x3;
  swap_cond_inplace pp ppq ith_bit;
  pop_frame()


val point_mul_loop_inner:
  #klen:size_nat ->
  pp:point ->
  ppq:point ->
  p:point ->
  pq:point ->
  k:lbuffer uint8 klen ->
  i:size_t ->
  Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> live h0 k))
let point_mul_loop_inner #klen pp ppq p pq k i =
  point_mul_loop_step pp ppq p pq k ((size 256) -. ((size 2) *. i) -. (size 1));
  point_mul_loop_step p pq pp ppq k ((size 256) -. ((size 2) *. i) -. (size 2))


val point_mul_:
  #klen:size_nat ->
  pp:point ->
  ppq:point ->
  p:point ->
  pq:point ->
  k:lbuffer uint8 klen ->
  Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> live h0 k))
let point_mul_ #klen pp ppq p pq k =
  let h0 = ST.get() in
  loop_nospec #h0 (size 128) p // this is certainly wrong
  (fun i -> point_mul_loop_inner #klen pp ppq p pq k i)


val p256:
  outx:lbuffer uint8 32 ->
  outy:lbuffer uint8 32 ->
  inx:lbuffer uint8 32 ->
  iny:lbuffer uint8 32 ->
  key:lbuffer uint8 32 ->
  Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let p256 outx outy inx iny key =
  push_frame();
  // Initial point
  let q = create (size 12) (u128 0) in
  let qx = get_x q in
  let qy = get_y q in
  let qz = get_z q in
  let qx3 = BB.uint_from_bytes_be (sub inx (size 0) (size 8)) in
  let qx2 = BB.uint_from_bytes_be (sub inx (size 8) (size 8)) in
  let qx1 = BB.uint_from_bytes_be (sub inx (size 16) (size 8)) in
  let qx0 = BB.uint_from_bytes_be (sub inx (size 24) (size 8)) in
  let qy3 = BB.uint_from_bytes_be (sub iny (size 0) (size 8)) in
  let qy2 = BB.uint_from_bytes_be (sub iny (size 8) (size 8)) in
  let qy1 = BB.uint_from_bytes_be (sub iny (size 16) (size 8)) in
  let qy0 = BB.uint_from_bytes_be (sub iny (size 24) (size 8)) in
  qx.(size 0) <- to_u128 #U64 qx0;
  qx.(size 1) <- to_u128 #U64 qx1;
  qx.(size 2) <- to_u128 #U64 qx2;
  qx.(size 3) <- to_u128 #U64 qx3;
  qy.(size 0) <- to_u128 #U64 qy0;
  qy.(size 1) <- to_u128 #U64 qy1;
  qy.(size 2) <- to_u128 #U64 qy2;
  qy.(size 3) <- to_u128 #U64 qy3;
  qz.(size 0) <- u128 1;
  // Create point at infinity
  let p = create (size 12) (u128 0) in
  let px = get_x p in
  let py = get_y p in
  px.(size 0) <- u128 1;
  py.(size 0) <- u128 1;
  let pp = create (size 12) (u128 0) in
  let ppq = create (size 12) (u128 0) in
  point_mul_ pp ppq p q key;

  let x = create (size 4) (u64 0) in
  let y = create (size 4) (u64 0) in

  let tmp = create (size 8) (u128 0) in
  let z2 = create (size 4) (u128 0) in
  let z3 = create (size 4) (u128 0) in
  let z2_inv = create (size 4) (u128 0) in
  let z3_inv = create (size 4) (u128 0) in
  let big_x = create (size 4) (u128 0) in
  let big_y = create (size 4) (u128 0) in

  felem_square tmp (get_z p);
  felem_reduce z2 tmp;
  felem_inv z2_inv z2;
  felem_mul tmp (get_x p) z2_inv;
  felem_reduce big_x tmp;
  felem_contract x big_x;

  felem_mul tmp z2 (get_z p);
  felem_reduce z3 tmp;
  felem_inv z3_inv z3;
  felem_mul tmp (get_y p) z3_inv;
  felem_reduce big_y tmp;
  felem_contract y big_y;

  let x0 = x.(size 0) in
  let x1 = x.(size 1) in
  let x2 = x.(size 2) in
  let x3 = x.(size 3) in
  let y0 = y.(size 0) in
  let y1 = y.(size 1) in
  let y2 = y.(size 2) in
  let y3 = y.(size 3) in
  BB.uint_to_bytes_be (sub outx (size 0) (size 8)) x3;
  BB.uint_to_bytes_be (sub outx (size 8) (size 8)) x2;
  BB.uint_to_bytes_be (sub outx (size 16) (size 8)) x1;
  BB.uint_to_bytes_be (sub outx (size 24) (size 8)) x0;
  BB.uint_to_bytes_be (sub outy (size 0) (size 8)) y3;
  BB.uint_to_bytes_be (sub outy (size 8) (size 8)) y2;
  BB.uint_to_bytes_be (sub outy (size 16) (size 8)) y1;
  BB.uint_to_bytes_be (sub outy (size 24) (size 8)) y0;
  pop_frame()

