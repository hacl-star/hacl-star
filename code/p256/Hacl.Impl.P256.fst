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

(* Type aliases *)
type u64 = UInt64.t
type limb = UInt128.t
type felem = b:buffer limb{length b = nlimbs}
type longfelem = b:buffer limb{length b = 2 * nlimbs}
type smallfelem = b:buffer u64{length b = nlimbs}

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
val felem_scalar: out:felem -> scalar:u64 ->
  Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let felem_sum out scalar =
  let open FStar.UInt128 in
  let o0 = out.(0ul) in
  let o1 = out.(1ul) in
  let o2 = out.(2ul) in
  let o3 = out.(3ul) in
  let o0 = uint128_to_uint64 o0 in
  let o1 = uint128_to_uint64 o1 in
  let o2 = uint128_to_uint64 o2 in
  let o3 = uint128_to_uint64 o3 in
  let scalar = scalar in
  out.(0ul) <- mul_wide o0 scalar;
  out.(1ul) <- mul_wide o1 scalar;
  out.(2ul) <- mul_wide o2 scalar;
  out.(3ul) <- mul_wide o3 scalar


// TODO: check that the downcast to u64 is indeed correct, otherwise this
// requires a special implementation of the multiplication
val longfelem_scalar: out:longfelem -> scalar:u64 ->
  Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let longfelem_sum out scalar =
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
  let tmp = create 4ul 0uL in
  let zero110 = zero110 () in
  let kPrime3Test = 0x7fffffff00000001uL in
  let input0 = input.(0ul) in
  let input1 = input.(1ul) in
  let input2 = input.(2ul) in
  let input3 = input.(3ul) in
  let zero0  = zero110.(0ul) in
  let zero1  = zero110.(1ul) in
  let zero2  = zero110.(2ul) in
  let zero3  = zero110.(3ul) in
  let open FStar.UInt128 in
  // TODO: replace with a primitive to call the high word only
  tmp.(3ul) <- zero3 +^ input3 +^ (input2 >>^ 64ul);
  tmp.(2ul) <- zero2 +^ (uint64_to_uint128 (uint128_to_uint64 input2));
  tmp.(0ul) <- zero0 +^ input0;
  tmp.(1ul) <- zero1 +^ input1;

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
  let low = UInt64.gte_mask low 0x8000000000000000uL in

  let low = UInt64.gte_mask kPrime3Test low in
  let low = UInt64.lognot low in

  let mask = FStar.UInt64.((mask &^ low) |^ high) in
  ()
