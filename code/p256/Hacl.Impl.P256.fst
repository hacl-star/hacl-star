module Hacl.Impl.P256

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All


open FStar.Mul
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer
open FStar.Endianness
open FStar.Int.Cast

open Hacl.Endianness
open C.Loops

(* Taken straight from the OpenSSL github code *)

(* Constants *)
let nlimbs = 4
let nlimbs' = 4ul

(* Type aliases *)
type u64 = UInt64.t
type limb = UInt128.t
type felem = b:buffer limb{length b = nlimbs}
type longfelem = b:buffer limb{length b = 2 * nlimbs}
type smallfelem = b:buffer u64{length b = nlimbs}

val create_felem:
  unit -> StackInline felem
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let create_felem () =
  create (UInt128.uint64_to_uint128 0uL) 4ul


val create_longfelem:
  unit -> StackInline longfelem
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let create_longfelem () =
  create (UInt128.uint64_to_uint128 0uL) 8ul

val create_smallfelem:
  unit -> StackInline smallfelem
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let create_smallfelem () =
  create 0uL 4ul

val kPrime: unit -> 
  StackInline smallfelem
    (requires (fun h -> True))
    (ensures (fun h0 b h1 -> True))
let kPrime () =
  let b = createL [0xffffffffffffffffuL; 0xffffffffuL; 0uL; 0xffffffff00000001uL] in
  b

val bin32_to_felem:
  output:felem -> input:buffer UInt8.t{length input = 32} ->
  Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let bin32_to_felem output input =
  let in0 = Buffer.sub input 0ul  8ul in
  let in1 = Buffer.sub input 8ul  8ul in
  let in2 = Buffer.sub input 16ul 8ul in
  let in3 = Buffer.sub input 24ul 8ul in
  let o0 = load64_le in0 in
  let o1 = load64_le in1 in
  let o2 = load64_le in2 in
  let o3 = load64_le in3 in
  output.(0ul) <- UInt128.uint64_to_uint128 o0;
  output.(1ul) <- UInt128.uint64_to_uint128 o1;
  output.(2ul) <- UInt128.uint64_to_uint128 o2;
  output.(3ul) <- UInt128.uint64_to_uint128 o3


val smallfelem_to_bin32:
  output:buffer UInt8.t{length output = 32} -> input:smallfelem ->
  Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let smallfelem_to_bin32 output input =
  let o0 = Buffer.sub output 0ul  8ul in
  let o1 = Buffer.sub output 8ul  8ul in
  let o2 = Buffer.sub output 16ul 8ul in
  let o3 = Buffer.sub output 24ul 8ul in
  let in0 = input.(0ul) in
  let in1 = input.(1ul) in
  let in2 = input.(2ul) in
  let in3 = input.(3ul) in
  store64_le o0 in0;
  store64_le o1 in1;
  store64_le o2 in2;
  store64_le o3 in3


val flip_endian:
  output:buffer UInt8.t{length output = 32} -> input:buffer UInt8.t{length input = 32} -> len:UInt32.t ->
  Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let flip_endian output input len =
  let inv (h1:mem) (i:nat) = True in
  let f (i:UInt32.t) : Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
    = let inputim1 = input.(FStar.UInt32.(len -^ 1ul -^ i)) in
      output.(i) <- inputim1 in
  for 0ul len inv f

(* Field operations *)

val smallfelem_one: out:smallfelem ->
  Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let smallfelem_one out =
  out.(0ul) <- 1uL;
  out.(1ul) <- 0uL;
  out.(2ul) <- 0uL;
  out.(3ul) <- 0uL

val smallfelem_assign: out:smallfelem -> input:smallfelem ->
  Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let smallfelem_assign out input =
  let in0 = input.(0ul) in
  let in1 = input.(1ul) in
  let in2 = input.(2ul) in
  let in3 = input.(3ul) in
  out.(0ul) <- in0;
  out.(1ul) <- in1;
  out.(2ul) <- in2;
  out.(3ul) <- in3

val felem_assign: out:felem -> input:felem ->
  Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let felem_assign out input =
  let in0 = input.(0ul) in
  let in1 = input.(1ul) in
  let in2 = input.(2ul) in
  let in3 = input.(3ul) in
  out.(0ul) <- in0;
  out.(1ul) <- in1;
  out.(2ul) <- in2;
  out.(3ul) <- in3

val felem_sum: out:felem -> input:felem ->
  Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let felem_sum out input =
  let in0 = input.(0ul) in
  let in1 = input.(1ul) in
  let in2 = input.(2ul) in
  let in3 = input.(3ul) in
  let o0 = out.(0ul) in
  let o1 = out.(1ul) in
  let o2 = out.(2ul) in
  let o3 = out.(3ul) in
  let open FStar.UInt128 in
  out.(0ul) <- o0 +^ in0;
  out.(1ul) <- o1 +^ in1;
  out.(2ul) <- o2 +^ in2;
  out.(3ul) <- o3 +^ in3


val felem_small_sum: out:felem -> input:smallfelem ->
  Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let felem_small_sum out input =
  let in0 = input.(0ul) in
  let in1 = input.(1ul) in
  let in2 = input.(2ul) in
  let in3 = input.(3ul) in
  let o0 = out.(0ul) in
  let o1 = out.(1ul) in
  let o2 = out.(2ul) in
  let o3 = out.(3ul) in
  let open FStar.UInt128 in
  out.(0ul) <- o0 +^ uint64_to_uint128 in0;
  out.(1ul) <- o1 +^ uint64_to_uint128 in1;
  out.(2ul) <- o2 +^ uint64_to_uint128 in2;
  out.(3ul) <- o3 +^ uint64_to_uint128 in3


// TODO: check that the downcast to u64 is indeed correct, otherwise this
// requires a special implementation of the multiplication
val felem_scalar: out:felem -> scalar:u32 ->
  Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let felem_scalar out scalar =
  let open FStar.UInt128 in
  let o0 = out.(0ul) in
  let o1 = out.(1ul) in
  let o2 = out.(2ul) in
  let o3 = out.(3ul) in
  // let o0 = uint128_to_uint64 o0 in
  // let o1 = uint128_to_uint64 o1 in
  // let o2 = uint128_to_uint64 o2 in
  // let o3 = uint128_to_uint64 o3 in
  let scalar = scalar in
  out.(0ul) <- shift_left o0 scalar;
  out.(1ul) <- shift_left o1 scalar;
  out.(2ul) <- shift_left o2 scalar;
  out.(3ul) <- shift_left o3 scalar


// TODO: check that the downcast to u64 is indeed correct, otherwise this
// requires a special implementation of the multiplication
val longfelem_scalar: out:longfelem -> scalar:u64 ->
  Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let longfelem_scalar out scalar =
  let open FStar.UInt128 in
  let o0 = out.(0ul) in
  let o1 = out.(1ul) in
  let o2 = out.(2ul) in
  let o3 = out.(3ul) in
  let o4 = out.(4ul) in
  let o5 = out.(5ul) in
  let o6 = out.(6ul) in
  let o7 = out.(7ul) in
  let o0 = uint128_to_uint64 o0 in
  let o1 = uint128_to_uint64 o1 in
  let o2 = uint128_to_uint64 o2 in
  let o3 = uint128_to_uint64 o3 in
  let o4 = uint128_to_uint64 o4 in
  let o5 = uint128_to_uint64 o5 in
  let o6 = uint128_to_uint64 o6 in
  let o7 = uint128_to_uint64 o7 in
  let scalar = scalar in
  out.(0ul) <- mul_wide o0 scalar;
  out.(1ul) <- mul_wide o1 scalar;
  out.(2ul) <- mul_wide o2 scalar;
  out.(3ul) <- mul_wide o3 scalar;
  out.(4ul) <- mul_wide o4 scalar;
  out.(5ul) <- mul_wide o5 scalar;
  out.(6ul) <- mul_wide o6 scalar;
  out.(7ul) <- mul_wide o7 scalar

inline_for_extraction
val load128: high:UInt64.t -> low:UInt64.t -> Tot (z:UInt128.t{UInt128.v z = pow2 64 * UInt64.v high
  + UInt64.v low})
let load128 h l =
  let open FStar.UInt128 in
  let hs = uint64_to_uint128 h <<^ 64ul in
  let ls = uint64_to_uint128 l in
  Math.Lemmas.modulo_lemma (UInt64.v h * pow2 64) (pow2 128);
  UInt.logor_disjoint #128 (v hs) (v ls) 64;
  hs |^ ls


(* Put in uint128 form*)
let two105m41m9 = load128 0x1ffffffffffuL 0xfffffdfffffffe00uL
let two105      = load128 0x30000000000uL 0x0uL
let two105m41p9 = load128 0x1ffffffffffuL 0xfffffe0000000200uL

let two107m43m11 = load128 0x7ffffffffffuL 0xfffff7fffffff800uL
let two107       = load128 0x80000000000uL 0x0uL
let two107m43p11 = load128 0x7ffffffffffuL 0xfffff80000000800uL

let two64m0     = UInt128.uint64_to_uint128 0xffffffffffffffffuL
let two110p32m0 = load128 0x400000000000uL 0x00000000ffffffffuL
let two64m46    = UInt128.uint64_to_uint128 0xffffc00000000000uL
let two64m32    = UInt128.uint64_to_uint128 0xffffffff00000000uL

let two70m8p6     = load128 0x3fuL 0xffffffffffffff40uL
let two70p40      = load128 0x40uL 0x0000010000000000uL
let two70         = load128  0x40uL 0x0000010000000000uL
let two70m40m38p6 = load128 0x3fuL 0xfffffec000000040uL
let two70m6       = load128 0x3fuL 0xffffffffffffffc0uL

let two100m36m4 = load128 0xfffffffffuL 0xffffffeffffffff0uL
let two100      = load128 0x1000000000uL 0x0uL
let two100m36p4 = load128 0xfffffffffuL 0xfffffff000000010uL


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
  push_frame();
  let zero105 = zero105 () in
  let open FStar.UInt128 in
  let small0 = small.(0ul) in
  let small1 = small.(1ul) in
  let small2 = small.(2ul) in
  let small3 = small.(3ul) in
  let zero0  = zero105.(0ul) in
  let zero1  = zero105.(1ul) in
  let zero2  = zero105.(2ul) in
  let zero3  = zero105.(3ul) in
  out.(0ul) <- zero0 -^ uint64_to_uint128 small0;
  out.(1ul) <- zero1 -^ uint64_to_uint128 small1;
  out.(2ul) <- zero2 -^ uint64_to_uint128 small2;
  out.(3ul) <- zero3 -^ uint64_to_uint128 small3;
  pop_frame()

val felem_diff:
  out:felem -> input:felem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let felem_diff out input =
  push_frame();
  let zero105 = zero105 () in
  let open FStar.UInt128 in
  let input0 = input.(0ul) in
  let input1 = input.(1ul) in
  let input2 = input.(2ul) in
  let input3 = input.(3ul) in
  let out0 = out.(0ul) in
  let out1 = out.(1ul) in
  let out2 = out.(2ul) in
  let out3 = out.(3ul) in
  let zero0  = zero105.(0ul) in
  let zero1  = zero105.(1ul) in
  let zero2  = zero105.(2ul) in
  let zero3  = zero105.(3ul) in
  let out0 = zero0 +^ out0 in
  let out1 = zero1 +^ out1 in
  let out2 = zero2 +^ out2 in
  let out3 = zero3 +^ out3 in
  out.(0ul) <- out0 -^ input0;
  out.(1ul) <- out1 -^ input1;
  out.(2ul) <- out2 -^ input2;
  out.(3ul) <- out3 -^ input3;
  pop_frame()


val felem_diff_zero107:
  out:felem -> input:felem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let felem_diff_zero107 out input =
  push_frame();
  let zero107 = zero107 () in
  let open FStar.UInt128 in
  let input0 = input.(0ul) in
  let input1 = input.(1ul) in
  let input2 = input.(2ul) in
  let input3 = input.(3ul) in
  let out0 = out.(0ul) in
  let out1 = out.(1ul) in
  let out2 = out.(2ul) in
  let out3 = out.(3ul) in
  let zero0  = zero107.(0ul) in
  let zero1  = zero107.(1ul) in
  let zero2  = zero107.(2ul) in
  let zero3  = zero107.(3ul) in
  let out0 = zero0 +^ out0 in
  let out1 = zero1 +^ out1 in
  let out2 = zero2 +^ out2 in
  let out3 = zero3 +^ out3 in
  out.(0ul) <- out0 -^ input0;
  out.(1ul) <- out1 -^ input1;
  out.(2ul) <- out2 -^ input2;
  out.(3ul) <- out3 -^ input3;
  pop_frame()


val longfelem_diff:
  out:longfelem -> input:longfelem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let longfelem_diff out input =
  push_frame();
  let open FStar.UInt128 in
  let input0 = input.(0ul) in
  let input1 = input.(1ul) in
  let input2 = input.(2ul) in
  let input3 = input.(3ul) in
  let input4 = input.(4ul) in
  let input5 = input.(5ul) in
  let input6 = input.(6ul) in
  let input7 = input.(7ul) in
  let out0 = out.(0ul) in
  let out1 = out.(1ul) in
  let out2 = out.(2ul) in
  let out3 = out.(3ul) in
  let out4 = out.(4ul) in
  let out5 = out.(5ul) in
  let out6 = out.(6ul) in
  let out7 = out.(7ul) in
  let out0 =  two70m8p6 +^ out0 in
  let out1 = two70p40 +^ out1 in
  let out2 = two70 +^ out2 in
  let out3 = two70m40m38p6 +^ out3 in
  let out4 = two70m6 +^ out4 in
  let out5 = two70m6 +^ out5 in
  let out6 = two70m6 +^ out6 in
  let out7 = two70m6 +^ out7 in
  out.(0ul) <- out0 -^ input0;
  out.(1ul) <- out1 -^ input1;
  out.(2ul) <- out2 -^ input2;
  out.(3ul) <- out3 -^ input3;
  out.(4ul) <- out4 -^ input4;
  out.(5ul) <- out5 -^ input5;
  out.(6ul) <- out6 -^ input6;
  out.(7ul) <- out7 -^ input7;
  pop_frame()

val felem_shrink:
  out:smallfelem -> input:felem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let felem_shrink out input =
  push_frame();
  let tmp = create (FStar.UInt128.uint64_to_uint128 0uL) 4ul in
  let zero110 = zero110 () in
  let kPrime  = kPrime () in
  let kPrime3Test = 0x7fffffff00000001uL in
  let input0 = input.(0ul) in
  let input1 = input.(1ul) in
  let input2 = input.(2ul) in
  let input3 = input.(3ul) in
  let zero0  = zero110.(0ul) in
  let zero1  = zero110.(1ul) in
  let zero2  = zero110.(2ul) in
  let zero3  = zero110.(3ul) in
  let kPrime0 = kPrime.(0ul) in
  let kPrime1 = kPrime.(1ul) in
  let kPrime2 = kPrime.(2ul) in
  let kPrime3 = kPrime.(3ul) in
  let open FStar.UInt128 in
  // TODO: replace with a primitive to call the high word only
  tmp.(3ul) <- zero3 +^ input3 +^ (input2 >>^ 64ul);
  tmp.(2ul) <- zero2 +^ (uint64_to_uint128 (uint128_to_uint64 input2));
  tmp.(0ul) <- zero0 +^ input0;
  tmp.(1ul) <- zero1 +^ input1;

  let tmp2 = tmp.(2ul) in
  let tmp3 = tmp.(3ul) in
  let a = tmp3 >>^ 64ul in
  let tmp3 = uint64_to_uint128 (uint128_to_uint64 tmp3) in
  let tmp3 = tmp3 -^ a in
  let tmp3 = tmp3 +^ (a <<^ 32ul) in

  let b = a in
  let a = tmp3 >>^ 64ul in
  let b = b +^ a in
  let tmp3 = uint64_to_uint128 (uint128_to_uint64 tmp3) in
  let tmp3 = tmp3 -^ a in
  let tmp3 = tmp3 +^ (a <<^ 32ul) in

  let tmp0 = tmp.(0ul) in
  let tmp0 = tmp0 +^ b in
  let tmp1 = tmp.(1ul) in
  let tmp1 = tmp1 -^ (b <<^ 32ul) in

  // TODO: better implementation
  let high = tmp3 >>^ 64ul in
  let high = uint128_to_uint64 (eq_mask tmp3 (load128 0x0uL 0x1uL)) in

  // TODO: better implementation
  let low = uint128_to_uint64 tmp3 in
  let mask = UInt64.gte_mask low 0x8000000000000000uL in

  let low = UInt64.gte_mask kPrime3Test low in
  let low = UInt64.lognot low in

  let mask = FStar.UInt64.((mask &^ low) |^ high) in

  let tmp0 = tmp0 -^ uint64_to_uint128 FStar.UInt64.(mask &^ kPrime0) in
  let tmp1 = tmp1 -^ uint64_to_uint128 FStar.UInt64.(mask &^ kPrime1) in
  let tmp3 = tmp3 -^ uint64_to_uint128 FStar.UInt64.(mask &^ kPrime3) in

  let tmp1 = tmp1 +^ (tmp0 >>^ 64ul) in
  let tmp0 = uint128_to_uint64 tmp0 in
  let tmp2 = tmp2 +^ (tmp1 >>^ 64ul) in
  let tmp1 = uint128_to_uint64 tmp1 in
  let tmp3 = tmp3 +^ (tmp2 >>^ 64ul) in
  let tmp2 = uint128_to_uint64 tmp2 in

  out.(0ul) <- tmp0;
  out.(1ul) <- tmp1;
  out.(2ul) <- tmp2;
  out.(3ul) <- uint128_to_uint64 tmp3;
  pop_frame ()


val smallfelem_expand:
  out:felem -> input:smallfelem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let smallfelem_expand out input =
  let input0 = input.(0ul) in
  let input1 = input.(1ul) in
  let input2 = input.(2ul) in
  let input3 = input.(3ul) in
  let open FStar.UInt128 in
  out.(0ul) <- uint64_to_uint128 input0;
  out.(1ul) <- uint64_to_uint128 input1;
  out.(2ul) <- uint64_to_uint128 input2;
  out.(3ul) <- uint64_to_uint128 input3

val smallfelem_square:
  out:longfelem -> small:smallfelem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let smallfelem_square out small =
  let open FStar.UInt128 in
  let small0 = small.(0ul) in
  let small1 = small.(1ul) in
  let small2 = small.(2ul) in
  let small3 = small.(3ul) in
  let a = mul_wide small0 small0 in
  let low = a in
  let high = a >>^ 64ul in

  let out0 = low in
  let out1 = high in

  let a = mul_wide small0 small1 in
  let low = a in
  let high = a >>^ 64ul in
  let out1 = out1 +^ low in
  let out1 = out1 +^ low in
  let out2 = high in

  let a = mul_wide small0 small2 in
  let low = a in
  let high = a >>^ 64ul in
  let out2 = out2 +^ low in
  let out2 = out2 <<^ 1ul in
  let out3 = high in

  let a = mul_wide small0 small3 in
  let low = a in
  let high = a >>^ 64ul in
  let out3 = out3 +^ low in
  let out4 = high in

  let a = mul_wide small1 small2 in
  let low = a in
  let high = a >>^ 64ul in
  let out3 = out3 +^ low in
  let out3 = out3 <<^ 1ul in
  let out4 = out4 +^ high in

  let a = mul_wide small1 small1 in
  let low = a in
  let high = a >>^ 64ul in
  let out2 = out2 +^ low in
  let out3 = out3 +^ high in

  let a = mul_wide small1 small3 in
  let low = a in
  let high = a >>^ 64ul in
  let out4 = out4 +^ low in
  let out4 = out4 <<^ 1ul in
  let out5 = high in

  let a = mul_wide small2 small3 in
  let low = a in
  let high = a >>^ 64ul in
  let out5 = out5 +^ low in
  let out5 = out5 <<^ 1ul in
  let out6 = high in
  let out6 = out6 +^ high in

  let a = mul_wide small2 small2 in
  let low = a in
  let high = a >>^ 64ul in
  let out4 = out4 +^ low in
  let out5 = out5 +^ high in

  let a = mul_wide small3 small3 in
  let low = a in
  let high = a >>^ 64ul in
  let out6 = out6 +^ low in
  let out7 = high in

  out.(0ul) <- out0;
  out.(1ul) <- out1;
  out.(2ul) <- out2;
  out.(3ul) <- out3;
  out.(4ul) <- out4;
  out.(5ul) <- out5;
  out.(6ul) <- out6;
  out.(7ul) <- out7


val felem_square:
  out:longfelem -> input:felem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let felem_square out input =
  push_frame();
  let small = create 0uL 4ul in
  felem_shrink small input;
  smallfelem_square out small;
  pop_frame()


val smallfelem_mul:
  out:longfelem -> small1:smallfelem -> small2:smallfelem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let smallfelem_mul out small1 small2 =
  let small10 = small1.(0ul) in
  let small11 = small1.(1ul) in
  let small12 = small1.(2ul) in
  let small13 = small1.(3ul) in
  let small20 = small2.(0ul) in
  let small21 = small2.(1ul) in
  let small22 = small2.(2ul) in
  let small23 = small2.(3ul) in

  let open FStar.UInt128 in
  let a = mul_wide small10 small20 in
  let low = a in
  let high = a >>^ 64ul in
  let out0 = low in
  let out1 = high in

  let a = mul_wide small10 small21 in
  let low = a in
  let high = a >>^ 64ul in
  let out1 = out1 +^ low in
  let out2 = high in

  let a = mul_wide small11 small20 in
  let low = a in
  let high = a >>^ 64ul in
  let out1 = out1 +^ low in
  let out2 = out2 +^ high in

  let a = mul_wide small10 small22 in
  let low = a in
  let high = a >>^ 64ul in
  let out2 = out2 +^ low in
  let out3 = high in

  let a = mul_wide small11 small21 in
  let low = a in
  let high = a >>^ 64ul in
  let out2 = out2 +^ low in
  let out3 = out3 +^ high in

  let a = mul_wide small12 small20 in
  let low = a in
  let high = a >>^ 64ul in
  let out2 = out2 +^ low in
  let out3 = out3 +^ high in

  let a = mul_wide small10 small23 in
  let low = a in
  let high = a >>^ 64ul in
  let out3 = out3 +^ low in
  let out4 = high in

  let a = mul_wide small11 small22 in
  let low = a in
  let high = a >>^ 64ul in
  let out3 = out3 +^ low in
  let out4 = out4 +^ high in

  let a = mul_wide small12 small21 in
  let low = a in
  let high = a >>^ 64ul in
  let out3 = out3 +^ low in
  let out4 = out4 +^ high in

  let a = mul_wide small13 small20 in
  let low = a in
  let high = a >>^ 64ul in
  let out3 = out3 +^ low in
  let out4 = out4 +^ high in

  let a = mul_wide small11 small23 in
  let low = a in
  let high = a >>^ 64ul in
  let out4 = out4 +^ low in
  let out5 = high in

  let a = mul_wide small12 small22 in
  let low = a in
  let high = a >>^ 64ul in
  let out4 = out4 +^ low in
  let out5 = out5 +^ high in

  let a = mul_wide small13 small21 in
  let low = a in
  let high = a >>^ 64ul in
  let out4 = out4 +^ low in
  let out5 = out5 +^ high in

  let a = mul_wide small12 small23 in
  let low = a in
  let high = a >>^ 64ul in
  let out5 = out5 +^ low in
  let out6 = high in

  let a = mul_wide small13 small22 in
  let low = a in
  let high = a >>^ 64ul in
  let out5 = out5 +^ low in
  let out6 = out6 +^ high in

  let a = mul_wide small13 small23 in
  let low = a in
  let high = a >>^ 64ul in
  let out6 = out6 +^ low in
  let out7 = high in

  out.(0ul) <- out0;
  out.(1ul) <- out1;
  out.(2ul) <- out2;
  out.(3ul) <- out3;
  out.(4ul) <- out4;
  out.(5ul) <- out5;
  out.(6ul) <- out6;
  out.(7ul) <- out7

val felem_mul:
  out:longfelem -> in1:felem -> in2:felem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let felem_mul out in1 in2 =
  push_frame();
  let small1 = create 0uL 4ul in
  let small2 = create 0uL 4ul in
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
  let small2 = create 0uL 4ul in
  felem_shrink small2 in2;
  smallfelem_mul out small1 small2;
  pop_frame()

val felem_reduce_:
  out:felem -> input:longfelem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let felem_reduce_ out input =
  let out0 = out.(0ul) in
  let out1 = out.(1ul) in
  let out2 = out.(2ul) in
  let out3 = out.(3ul) in
  let input0 = input.(0ul) in
  let input1 = input.(1ul) in
  let input2 = input.(2ul) in
  let input3 = input.(3ul) in
  let input4 = input.(4ul) in
  let input5 = input.(5ul) in
  let input6 = input.(6ul) in
  let input7 = input.(7ul) in
  let open FStar.UInt128 in
  let c = input4 +^ (input5 <<^ 32ul) in
  let out0 = out0 +^ c in
  let out3 = out3 -^ c in
  let c = input5 -^ input7 in
  let out1 = out1 +^ c in
  let out2 = out2 -^ c in
  let out1 = out1 -^ (input4 <<^ 32ul) in
  let out3 = out1 +^ (input4 <<^ 32ul) in
  let out2 = out2 -^ (input5 <<^ 32ul) in
  let out0 = out0 -^ input6 in
  let out0 = out0 -^ (input6 <<^ 32ul) in
  let out1 = out1 +^ (input6 <<^ 33ul) in
  let out2 = out2 +^ (input6 <<^ 1ul)  in
  let out3 = out3 -^ (input6 <<^ 32ul) in
  let out0 = out0 -^ input7 in
  let out0 = out0 -^ (input7 <<^ 32ul) in
  let out2 = out2 +^ (input7 <<^ 33ul) in
  let out3 = out3 +^ ((input7 <<^ 1ul) +^ input7) in
  out.(0ul) <- out0;
  out.(1ul) <- out1;
  out.(2ul) <- out2;
  out.(3ul) <- out3
  
val felem_reduce:
  out:felem -> input:longfelem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let felem_reduce out input =
  let open FStar.UInt128 in
  push_frame();
  let zero100 = zero100() in
  let zero0 = zero100.(0ul) in
  let zero1 = zero100.(1ul) in
  let zero2 = zero100.(2ul) in
  let zero3 = zero100.(3ul) in
  let input0 = input.(0ul) in
  let input1 = input.(1ul) in
  let input2 = input.(2ul) in
  let input3 = input.(3ul) in
  out.(0ul) <- input0 +^ zero0;
  out.(1ul) <- input0 +^ zero1;
  out.(2ul) <- input0 +^ zero2;
  out.(3ul) <- input0 +^ zero3;
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
  let zero0 = zero105.(0ul) in
  let zero1 = zero105.(1ul) in
  let zero2 = zero105.(2ul) in
  let zero3 = zero105.(3ul) in
  let input0 = input.(0ul) in
  let input1 = input.(1ul) in
  let input2 = input.(2ul) in
  let input3 = input.(3ul) in
  out.(0ul) <- input0 +^ zero0;
  out.(1ul) <- input0 +^ zero1;
  out.(2ul) <- input0 +^ zero2;
  out.(3ul) <- input0 +^ zero3;
  felem_reduce_ out input;
  pop_frame()

val subtract_u64:
  result:u64 -> v:u64 -> Tot (tuple2 u64 u64)
let subtract_u64 result v' =
  let r = UInt128.uint64_to_uint128 result in
  let r = FStar.UInt128.(r -%^ uint64_to_uint128 v') in  
  let open FStar.UInt64 in
  let carry = FStar.UInt128.(uint128_to_uint64 (r >>^ 64ul)) &^ 1uL in
  let result = UInt128.uint128_to_uint64 r in
  result, carry

val felem_contract:
  out:smallfelem -> input:felem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let felem_contract out input =
  push_frame();
  let all_equal_so_far = 0uL in
  let result = 0uL in
  felem_shrink out input;
  let all_equal_so_far = FStar.UInt64.(all_equal_so_far -%^ 1uL) in

  let open FStar.UInt128 in
  let kPrime = kPrime() in
  let kPrime0 = kPrime.(0ul) in
  let kPrime1 = kPrime.(1ul) in
  let kPrime2 = kPrime.(2ul) in
  let kPrime3 = kPrime.(3ul) in
  let out0 = out.(0ul) in
  let out1 = out.(1ul) in
  let out2 = out.(2ul) in
  let out3 = out.(3ul) in
  let a = uint64_to_uint128 kPrime0 -^ uint64_to_uint128 out0 in
  let result = FStar.UInt64.(result |^ (all_equal_so_far &^ FStar.UInt128.(uint128_to_uint64 (a >>^ 64ul)))) in

  let open FStar.UInt64 in
  let equal = kPrime3 ^^ out3 in
  let equal = equal -^ 1uL in
  let equal = equal &^ (equal <<^ 32ul) in
  let equal = equal &^ (equal <<^ 16ul) in
  let equal = equal &^ (equal <<^ 8ul) in
  let equal = equal &^ (equal <<^ 4ul) in
  let equal = equal &^ (equal <<^ 2ul) in
  let equal = equal &^ (equal <<^ 1ul) in
  let equal = gte_mask equal 0x1000000000000000uL in
  let all_equal_so_far = all_equal_so_far &^ equal in


  let equal = kPrime2 ^^ out2 in
  let equal = equal -^ 1uL in
  let equal = equal &^ (equal <<^ 32ul) in
  let equal = equal &^ (equal <<^ 16ul) in
  let equal = equal &^ (equal <<^ 8ul) in
  let equal = equal &^ (equal <<^ 4ul) in
  let equal = equal &^ (equal <<^ 2ul) in
  let equal = equal &^ (equal <<^ 1ul) in
  let equal = gte_mask equal 0x1000000000000000uL in
  let all_equal_so_far = all_equal_so_far &^ equal in

  let equal = kPrime1 ^^ out1 in
  let equal = equal -^ 1uL in
  let equal = equal &^ (equal <<^ 32ul) in
  let equal = equal &^ (equal <<^ 16ul) in
  let equal = equal &^ (equal <<^ 8ul) in
  let equal = equal &^ (equal <<^ 4ul) in
  let equal = equal &^ (equal <<^ 2ul) in
  let equal = equal &^ (equal <<^ 1ul) in
  let equal = gte_mask equal 0x1000000000000000uL in
  let all_equal_so_far = all_equal_so_far &^ equal in

  let equal = kPrime0 ^^ out0 in
  let equal = equal -^ 1uL in
  let equal = equal &^ (equal <<^ 32ul) in
  let equal = equal &^ (equal <<^ 16ul) in
  let equal = equal &^ (equal <<^ 8ul) in
  let equal = equal &^ (equal <<^ 4ul) in
  let equal = equal &^ (equal <<^ 2ul) in
  let equal = equal &^ (equal <<^ 1ul) in
  let equal = gte_mask equal 0x1000000000000000uL in
  let all_equal_so_far = all_equal_so_far &^ equal in

  let result = result |^ all_equal_so_far in

  let out0, carry = subtract_u64 out0 (result &^ kPrime0) in
  let out1, carry = subtract_u64 out1 carry in
  let out2, carry = subtract_u64 out2 carry in
  let out3, carry = subtract_u64 out3 carry in

  let out1, carry = subtract_u64 out1 (result &^ kPrime1) in
  let out2, carry = subtract_u64 out2 carry in
  let out3, carry = subtract_u64 out3 carry in

  let out2, carry = subtract_u64 out2 (result &^ kPrime2) in
  let out3, carry = subtract_u64 out3 carry in

  let out3, carry = subtract_u64 out3 (result &^ kPrime3) in
  pop_frame()

val smallfelem_mul_contract:
  out:smallfelem -> in1:smallfelem -> in2:smallfelem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let smallfelem_mul_contract out in1 in2 =
  push_frame();
  let longtmp = create (UInt128.uint64_to_uint128 0uL) 8ul in
  let tmp     = create (UInt128.uint64_to_uint128 0uL) 4ul in
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
  let kPrime0 = kPrime.(0ul) in
  let kPrime1 = kPrime.(1ul) in
  let kPrime2 = kPrime.(2ul) in
  let kPrime3 = kPrime.(3ul) in
  let small0 = small.(0ul) in
  let small1 = small.(1ul) in
  let small2 = small.(2ul) in
  let small3 = small.(3ul) in
  let open FStar.UInt64 in
  let is_zero = FStar.UInt64.(small0 |^ small1 |^ small2 |^ small3) in
  let is_zero = eq_mask is_zero 0uL in
  let is_p = (small0 ^^ kPrime0) |^ (small1 ^^ kPrime1) |^ (small2 ^^ kPrime2) |^ (small3 ^^ kPrime3) in
  let is_p = eq_mask is_p 0uL in
  let is_zero = is_zero |^ is_p in
  let result = FStar.UInt128.(uint64_to_uint128 is_zero |^ (uint64_to_uint128 is_zero <<^ 64ul)) in
  pop_frame();
  result

val smallfelem_is_zero_int:
  small:smallfelem -> Stack FStar.UInt32.t
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let smallfelem_is_zero_int small =
  let w = smallfelem_is_zero small in
  FStar.UInt128.(uint64_to_uint32 (uint128_to_uint64 (w &^ uint64_to_uint128 1uL)))

val felem_inv:
  out:felem -> input:felem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let felem_inv out input =
  push_frame();
  let z = FStar.UInt128.uint64_to_uint128 0uL in
  let ftmp = create z 4ul in
  let ftmp2 = create z 4ul in
  let e2 = create z 4ul in
  let e4 = create z 4ul in
  let e8 = create z 4ul in
  let e16 = create z 4ul in
  let e32 = create z 4ul in
  let e64 = create z 4ul in
  let tmp = create z 8ul in
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
  let inv (h1:mem) (i:nat) = True in
  let f (i:UInt32.t) : Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
    = felem_square tmp ftmp;
      felem_reduce ftmp tmp in
  let f' (i:UInt32.t) : Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
    = felem_square tmp ftmp2;
      felem_reduce ftmp2 tmp in
  for 0ul 8ul inv f;
  felem_mul tmp ftmp e8;
  felem_reduce ftmp tmp;
  felem_assign e16 ftmp;
  for 0ul 16ul inv f;
  felem_mul tmp ftmp e16;
  felem_reduce ftmp tmp;
  felem_assign e32 ftmp;
  for 0ul 32ul inv f;
  felem_assign e64 ftmp;
  felem_mul tmp ftmp input;
  felem_reduce ftmp tmp;
  for 0ul 192ul inv f;
  felem_mul tmp e64 e32;
  felem_reduce ftmp2 tmp;
  for 0ul 16ul inv f';
  felem_mul tmp ftmp2 e16;
  felem_reduce ftmp2 tmp;
  for 0ul 8ul inv f';
  felem_mul tmp ftmp2 e8;
  felem_reduce ftmp2 tmp;
  for 0ul 4ul inv f';
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
  let tmp = create (UInt128.uint64_to_uint128 0uL) 4ul in
  smallfelem_expand tmp input;
  felem_inv tmp tmp;
  felem_contract out tmp;
  pop_frame()

val point_double:
  x_out:felem -> y_out:felem -> z_out:felem ->
  x_in:felem -> y_in:felem -> z_in:felem -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let point_double x_out y_out z_out x_in y_in z_in =
  let tmp = create (UInt128.uint64_to_uint128 0uL) 8ul in
  let tmp2 = create (UInt128.uint64_to_uint128 0uL) 8ul in
  let delta = create (UInt128.uint64_to_uint128 0uL) 4ul in
  let gamma = create (UInt128.uint64_to_uint128 0uL) 4ul in
  let beta = create (UInt128.uint64_to_uint128 0uL) 4ul in
  let alpha = create (UInt128.uint64_to_uint128 0uL) 4ul in
  let ftmp = create (UInt128.uint64_to_uint128 0uL) 4ul in
  let ftmp2 = create (UInt128.uint64_to_uint128 0uL) 4ul in
  let small1 = create 0uL 4ul in
  let small2 = create 0uL 4ul in

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
  felem_scalar ftmp2 1ul;
  felem_sum ftmp2 tmp;
  // END TODO
  felem_mul tmp ftmp ftmp2;
  felem_reduce alpha tmp;
  felem_shrink small2 alpha;

  smallfelem_square tmp small2;
  felem_reduce x_out tmp;
  felem_assign ftmp beta;
  felem_scalar ftmp 3ul;
  felem_diff x_out ftmp;

  felem_sum delta gamma;
  felem_assign ftmp y_in;
  felem_sum ftmp z_in;
  felem_square tmp ftmp;
  felem_reduce z_out tmp;
  felem_diff z_out delta;

  felem_scalar beta 2ul;
  felem_diff_zero107 beta x_out;
  felem_small_mul tmp small2 beta;
  smallfelem_square tmp2 small1;
  longfelem_scalar tmp2 8uL;
  longfelem_diff tmp tmp2;
  felem_reduce_zero105 y_out tmp

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


val copy_conditional:
  out:felem -> input:felem -> mask:limb -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let copy_conditional out input mask =
  let open FStar.UInt128 in
  let inv (h1:mem) (i:nat) = True in
  let f (i:UInt32.t) : Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
    = let inputi = input.(i) in
      let outi = out.(i) in
      let tmp = mask &^ input.(FStar.UInt32.(nlimbs' -^ 1ul -^ i)) in
      out.(i) <- tmp in
  for 0ul nlimbs' inv f

val copy_small_conditional:
  out:felem -> input:smallfelem -> mask:limb -> Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let copy_small_conditional out input mask =
  let open FStar.UInt128 in
  let mask64 = uint128_to_uint64 mask in
  let inv (h1:mem) (i:nat) = True in
  let f (i:UInt32.t) : Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
    = let inputi = input.(i) in
      let outi = out.(i) in
      let tmp = (uint64_to_uint128 FStar.UInt64.(inputi &^ mask64) |^ (outi &^ lognot mask)) in
      out.(i) <- tmp in
  for 0ul nlimbs' inv f


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

  if (mixed <> 0ul) then
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
      felem_scalar ftmp5 1ul;

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
  felem_scalar ftmp5 1ul;
  felem_shrink small1 ftmp5;
  let y_equal = smallfelem_is_zero small1 in

  let zero = UInt128.uint64_to_uint128 0uL in
  if  ((x_equal <> zero) && (y_equal <> zero) && not(z1_is_zero <> zero) && not(z2_is_zero <> zero)) then
      begin
        point_double x3 y3 z3 x1 y1 z1
      end
  else
      begin
        felem_assign ftmp ftmp4;
        felem_scalar ftmp 1ul;
        felem_square tmp ftmp;
        felem_reduce ftmp tmp;
        felem_mul tmp ftmp4 ftmp;
        felem_reduce ftmp2 tmp;
        felem_mul tmp ftmp3 ftmp;
        felem_reduce ftmp4 tmp;
        smallfelem_square tmp small1;
        felem_reduce x_out tmp;
        felem_assign ftmp3 ftmp4;
        felem_scalar ftmp4 1ul;
        felem_sum ftmp4 ftmp2;
        felem_diff x_out ftmp4;

        felem_diff_zero107 ftmp3 x_out;
        felem_small_mul tmp small1 ftmp3;
        felem_mul tmp2 ftmp6 ftmp2;
        longfelem_scalar tmp2 2uL;
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

type point = b:buffer limb{length b = 12}

let get_x (p:point) = Buffer.sub p 0ul 4ul
let get_y (p:point) = Buffer.sub p 4ul 4ul
let get_z (p:point) = Buffer.sub p 8ul 4ul

// TODO: implement
let disjoint_p (p:point) (q:point) = True

private
val ith_bit:
  k:buffer Hacl.UInt8.t{length k = 32} ->
  i:UInt32.t{UInt32.v i < 256} ->
  Stack Hacl.UInt8.t
    (requires (fun h -> live h k))
    (ensures (fun h0 z h1 -> h0 == h1 /\ live h0 k /\
      Hacl.UInt8.v z == Spec.Ed25519.ith_bit (// reveal_sbytes
  (as_seq h0 k)) (UInt32.v i)
      /\ (Hacl.UInt8.v z == 0 \/ Hacl.UInt8.v z == 1)))
let ith_bit k i =
  assert_norm(pow2 1 = 2);
  assert_norm(pow2 3 = 8);
  assert_norm(pow2 5 = 32);
  assert_norm(pow2 8 = 256);
  let open FStar.UInt32 in
  let q = i >>^ 3ul in
  assert(v q = v i / 8);
  let r = i &^ 7ul in
  UInt.logand_mask (v i) 3;
  assert(v r = v i % 8);
  Math.Lemmas.lemma_div_lt (v i) 8 3;
  let kq = k.(q) in
  let kq' = Hacl.UInt8.(kq >>^ r) in
  let z = Hacl.UInt8.(kq' &^ Hacl.Cast.uint8_to_sint8 1uy) in
  UInt.logand_mask (Hacl.UInt8.v kq') 1;
  assert(Hacl.UInt8.v z = (Hacl.UInt8.v kq / pow2 (v r)) % 2);
  z

private
inline_for_extraction let mk_mask (iswap:UInt128.t{UInt128.v iswap = 0 \/ UInt128.v iswap = 1}) :
  Tot (z:UInt128.t{if UInt128.v iswap = 1 then UInt128.v z = pow2 64 - 1 else UInt128.v z = 0})
  = let swap = FStar.UInt128.(uint64_to_uint128 0uL -%^ iswap) in
    assert_norm((0 - 1) % pow2 64 = pow2 64 - 1);
    assert_norm((0 - 0) % pow2 64 = 0);
    swap

private
val swap_cond_inplace:
  p:point -> q:point{disjoint_p p q} -> i:limb{UInt128.v i = 0 \/ UInt128.v i = 1} ->
  Stack unit
    (requires (fun h -> live h p /\ live h q /\
      ( let x1 = as_seq h (get_x p) in
        let y1 = as_seq h (get_y p) in
        let z1 = as_seq h (get_z p) in
        True) /\
        // red_513 x1 /\ red_513 y1 /\ red_513 z1) /\
      ( let x2 = as_seq h (get_x q) in
        let y2 = as_seq h (get_y q) in
        let z2 = as_seq h (get_z q) in
        True
        // red_513 x2 /\ red_513 y2 /\ red_513 z2
  ) ))
    (ensures (fun h0 _ h1 -> live h1 p /\ live h1 q /\ modifies_2 p q h0 h1 /\ live h0 p /\ live h0 q /\
      ( let x1 = as_seq h0 (get_x p) in
        let y1 = as_seq h0 (get_y p) in
        let z1 = as_seq h0 (get_z p) in
        let x2 = as_seq h0 (get_x q) in
        let y2 = as_seq h0 (get_y q) in
        let z2 = as_seq h0 (get_z q) in
        let x1' = as_seq h1 (get_x p) in
        let y1' = as_seq h1 (get_y p) in
        let z1' = as_seq h1 (get_z p) in
        let x2' = as_seq h1 (get_x q) in
        let y2' = as_seq h1 (get_y q) in
        let z2' = as_seq h1 (get_z q) in
        // red_513 x1 /\ red_513 y1 /\ red_513 z1 /\
        // red_513 x2 /\ red_513 y2 /\ red_513 z2 /\
        // red_513 x1' /\ red_513 y1' /\ red_513 z1' /\
        // red_513 x2' /\ red_513 y2' /\ red_513 z2' /\
        True /\
      (if UInt128.v i = 1 then (x1' == x2 /\ y1' == y2 /\ z1' == z2 /\
                                    x2' == x1 /\ y2' == y1 /\ z2' == z1)
         else (x1' == x1 /\ y1' == y1 /\ z1' == z1 /\
               x2' == x2 /\ y2' == y2 /\ z2' == z2)))
    ))
let swap_cond_inplace p q iswap =
  let mask = mk_mask iswap in
  let inv (h1:mem) (i:nat) = True in
  let f (i:UInt32.t) : Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
    = let open FStar.UInt128 in
      let pi = p.(i) in
      let qi = q.(i) in
      let x  = mask &^ (pi ^^ qi) in
      let pi' = pi &^ x in
      let qi' = qi &^ x in
      p.(i) <- pi';
      q.(i) <- qi'
      in
  for 0ul 12ul inv f

  // Hacl.Impl.Ed25519.SwapConditional.swap_conditional_inplace p q iswap

val loop_step:
  pp:point ->
  ppq:point ->
  p:point ->
  pq:point ->
  k:buffer UInt8.t ->
  i:UInt32.t ->
  Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let loop_step pp ppq p pq k i =
  push_frame();
  let x = create 0uL 4ul in
  let y = create 0uL 4ul in
  let z = create 0uL 4ul in
  // TODO: change the algorithm, this is an ugly workaround due to OpenSSL's 'point_add' function
  felem_shrink x (get_x pq);
  felem_shrink y (get_y pq);
  felem_shrink z (get_z pq);
  let ith_bit = ith_bit k i in
  let ith_bit = uint8_to_uint128 ith_bit in
  swap_cond_inplace p pq ith_bit;
  point_double (get_x pp) (get_y pp) (get_z pp) (get_x p) (get_y p) (get_z p);
  point_add (get_x pp) (get_y pp) (get_z pp)
            (get_x p) (get_y p) (get_z p)
            0ul
            x y z;
            // (get_x pq) (get_y pq) (get_z pq);
  swap_cond_inplace pp ppq ith_bit;
  pop_frame()


val point_mul_:
  // b:buffer UInt64.t{length b = 80} ->
  pp:point ->
  ppq:point ->
  p:point ->
  pq:point ->
  k:buffer UInt8.t ->
  Stack unit
    (requires (fun h -> Buffer.live h k /\ True))
      // (let nq   = Buffer.sub b 0ul 20ul in
      //  let nqpq = Buffer.sub b 20ul 20ul in
      //  point_inv h nq /\ point_inv h nqpq) ))
    (ensures (fun h0 _ h1 -> Buffer.live h0 k // /\ live h0 b /\ live h1 b /\ modifies_1 b h0 h1
  ))
let point_mul_ pp ppq p pq k =
  let h0 = ST.get() in
  let inv (h1: HyperStack.mem) (i: nat): Type0 = True
  in
  let f' (i:UInt32.t{ FStar.UInt32.( 0 <= v i /\ v i < 256) }): Stack unit
    (requires (fun h -> inv h (UInt32.v i)))
    (ensures (fun h_1 _ h_2 -> FStar.UInt32.(inv h_2 (v i + 1))))
  =
    // let nq   = Buffer.sub b  0ul 20ul in
    // let nqpq = Buffer.sub b 20ul 20ul in
    // let h  = ST.get() in
    loop_step pp ppq p pq k FStar.UInt32.(256ul -^ i -^ 1ul)
    // let h' = ST.get() in
    // lemma_montgomery_ladder_def_1 (as_point h0 nq) (as_point h0 nqpq) (reveal_sbytes (as_seq h0 k)) (UInt32.v i + 1)
  in
  // let nq   = Buffer.sub b  0ul 20ul in
  // let nqpq = Buffer.sub b 20ul 20ul in
  // lemma_montgomery_ladder_def_0 (as_point h0 nq) (as_point h0 nqpq) (reveal_sbytes (as_seq h0 k));
  C.Loops.for 0ul 256ul inv f'


val p256:
  outx:buffer UInt8.t{length outx = 32} ->
  outy:buffer UInt8.t{length outy = 32} ->
  inx:buffer UInt8.t{length inx = 32} ->
  iny:buffer UInt8.t{length iny = 32} ->
  key:buffer UInt8.t{length key = 32} ->
  Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let p256 outx outy inx iny key =
  push_frame();
  // Initial point
  let q = create (UInt128.uint64_to_uint128 0uL) 12ul in
  let qx = get_x q in
  let qy = get_y q in
  let qz = get_z q in
  let qx0 = load64_le (Buffer.sub inx 0ul 8ul) in
  let qx1 = load64_le (Buffer.sub inx 8ul 8ul) in
  let qx2 = load64_le (Buffer.sub inx 16ul 8ul) in
  let qx3 = load64_le (Buffer.sub inx 24ul 8ul) in
  let qy0 = load64_le (Buffer.sub iny 0ul 8ul) in
  let qy1 = load64_le (Buffer.sub iny 8ul 8ul) in
  let qy2 = load64_le (Buffer.sub iny 16ul 8ul) in
  let qy3 = load64_le (Buffer.sub iny 24ul 8ul) in
  qx.(0ul) <- UInt128.uint64_to_uint128 qx0;
  qx.(1ul) <- UInt128.uint64_to_uint128 qx1;
  qx.(2ul) <- UInt128.uint64_to_uint128 qx2;
  qx.(3ul) <- UInt128.uint64_to_uint128 qx3;
  qy.(0ul) <- UInt128.uint64_to_uint128 qy0;
  qy.(1ul) <- UInt128.uint64_to_uint128 qy1;
  qy.(2ul) <- UInt128.uint64_to_uint128 qy2;
  qy.(3ul) <- UInt128.uint64_to_uint128 qy3;
  qz.(0ul) <- UInt128.uint64_to_uint128 1uL;
  // Create point at infinity
  let p = create (UInt128.uint64_to_uint128 0uL) 12ul in
  let px = get_x p in
  let py = get_y p in
  px.(0ul) <- UInt128.uint64_to_uint128 1uL;
  py.(0ul) <- UInt128.uint64_to_uint128 1uL;
  // Copy initial point into pq (P == point at infinity + Q == initial_point)
  let pq = create (UInt128.uint64_to_uint128 0uL) 12ul in
  Buffer.blit q 0ul pq 0ul 12ul;
  // Storage buffers
  let pp = create (UInt128.uint64_to_uint128 0uL) 12ul in
  let ppq = create (UInt128.uint64_to_uint128 0uL) 12ul in
  point_mul_ pp ppq p pq key;
  let x = create 0uL 4ul in
  let y = create 0uL 4ul in
  felem_contract x (get_x pp);
  felem_contract y (get_y pp);
  let x0 = x.(0ul) in
  let x1 = x.(1ul) in
  let x2 = x.(2ul) in
  let x3 = x.(3ul) in
  let y0 = y.(0ul) in
  let y1 = y.(1ul) in
  let y2 = y.(2ul) in
  let y3 = y.(3ul) in
  store64_le (Buffer.sub outx 0ul 8ul) x0;
  store64_le (Buffer.sub outx 8ul 8ul) x1;
  store64_le (Buffer.sub outx 16ul 8ul) x2;
  store64_le (Buffer.sub outx 24ul 8ul) x3;
  store64_le (Buffer.sub outy 0ul 8ul) y0;
  store64_le (Buffer.sub outy 8ul 8ul) y1;
  store64_le (Buffer.sub outy 16ul 8ul) y2;
  store64_le (Buffer.sub outy 24ul 8ul) y3;
  pop_frame()
