module Hacl.Impl.Curve25519.Field26

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.Sequence
open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST

#reset-options "--z3rlimit 20"

let felem = lbuffer uint64 10ul
let felem2 = lbuffer uint64 20ul
let felem_wide = lbuffer uint64 10ul
let felem10 = uint64 & uint64 & uint64 & uint64 & uint64 & uint64 & uint64 & uint64 & uint64 & uint64 

noextract
val as_nat: h:mem -> e:felem -> GTot nat
let as_nat h e = 
  let f = as_seq h e in
  let f0 = v f.[0] in
  let f1 = v f.[1] in
  let f2 = v f.[2] in
  let f3 = v f.[3] in
  let f4 = v f.[4] in
  let f5 = v f.[5] in
  let f6 = v f.[6] in
  let f7 = v f.[7] in
  let f8 = v f.[8] in
  let f9 = v f.[9] in
  let x1 = pow2 26 in
  let x2 = x1 * pow2 26 in
  let x3 = x2 * pow2 26 in
  let x4 = x3 * pow2 26 in
  let x5 = x4 * pow2 26 in
  let x6 = x5 * pow2 26 in
  let x7 = x6 * pow2 26 in
  let x8 = x7 * pow2 26 in
  let x9 = x8 * pow2 26 in
  f0 + f1 * x1 + f2 * x2 +  f3 * x3 + f4 * x4 +
  f5 * x5 + f6 * x6 + f7 * x7 +  f8 * x8 + f9 * x9 

noextract
val wide_as_nat: h:mem -> e:felem_wide -> GTot nat
let wide_as_nat h e = admit()

inline_for_extraction
val create_felem:
  unit -> StackInline felem
  (requires fun _ -> True)
  (ensures  fun h0 f h1 ->
    stack_allocated f h0 h1 (Seq.create 10 (u64 0)) /\
    as_nat h1 f == 0)
let create_felem () = create 10ul (u64 0)

inline_for_extraction
val set_zero:
  f:felem -> Stack unit
  (requires fun h -> live h f)
  (ensures  fun h0 _ h1 ->
    modifies (loc f) h0 h1 /\
    as_nat h1 f == 0)
let set_zero f =
  f.(0ul) <- u64 0;
  f.(1ul) <- u64 0;
  f.(2ul) <- u64 0;
  f.(3ul) <- u64 0;
  f.(4ul) <- u64 0;
  f.(5ul) <- u64 0;
  f.(6ul) <- u64 0;
  f.(7ul) <- u64 0;
  f.(8ul) <- u64 0;
  f.(9ul) <- u64 0

inline_for_extraction
val set_one:
  f:felem -> Stack unit
  (requires fun h -> live h f)
  (ensures  fun h0 _ h1 ->
    modifies (loc f) h0 h1 /\
    as_nat h1 f == 1)
let set_one f =
  f.(0ul) <- u64 1;
  f.(1ul) <- u64 0;
  f.(2ul) <- u64 0;
  f.(3ul) <- u64 0;
  f.(4ul) <- u64 0;
  f.(5ul) <- u64 0;
  f.(6ul) <- u64 0;
  f.(7ul) <- u64 0;
  f.(8ul) <- u64 0;
  f.(9ul) <- u64 0

inline_for_extraction
val copy_felem:
    f1:felem
  -> f2:felem
  -> Stack unit
    (requires fun h ->
      live h f1 /\ live h f2 /\ disjoint f1 f2)
    (ensures  fun h0 _ h1 ->
      modifies (loc f1) h0 h1 /\
      as_nat h1 f1 = as_nat h0 f2)
let copy_felem f1 f2 =
  f1.(size 0) <- f2.(size 0);
  f1.(size 1) <- f2.(size 1);
  f1.(size 2) <- f2.(size 2);
  f1.(size 3) <- f2.(size 3);
  f1.(size 4) <- f2.(size 4);
  f1.(size 5) <- f2.(size 5);
  f1.(size 6) <- f2.(size 6);
  f1.(size 7) <- f2.(size 7);
  f1.(size 8) <- f2.(size 8);
  f1.(size 9) <- f2.(size 9)

#set-options "--max_fuel 0 --max_ifuel 0"

val fadd:
    out:felem
  -> f1:felem
  -> f2:felem
  -> Stack unit
    (requires fun h ->
      live h f1 /\ live h f2 /\ live h out)
    (ensures fun h0 _ h1 ->
      modifies (loc out) h0 h1)
[@ CInline]
let fadd out f1 f2 =
  out.(0ul) <- f1.(0ul) +. f2.(0ul);
  out.(1ul) <- f1.(1ul) +. f2.(1ul);
  out.(2ul) <- f1.(2ul) +. f2.(2ul);
  out.(3ul) <- f1.(3ul) +. f2.(3ul);
  out.(4ul) <- f1.(4ul) +. f2.(4ul);
  out.(5ul) <- f1.(5ul) +. f2.(5ul);
  out.(6ul) <- f1.(6ul) +. f2.(6ul);
  out.(7ul) <- f1.(7ul) +. f2.(7ul);
  out.(8ul) <- f1.(8ul) +. f2.(8ul);
  out.(9ul) <- f1.(9ul) +. f2.(9ul)


val fsub:
    out:felem
  -> f1:felem
  -> f2:felem
  -> Stack unit
    (requires fun h ->
      live h f1 /\ live h f2 /\ live h out)
    (ensures fun h0 _ h1 ->
      modifies (loc out) h0 h1)
[@ CInline]
let fsub out f1 f2 =
  out.(0ul) <- f1.(0ul) +. u64 0x3ffff68 -. f2.(0ul);
  out.(1ul) <- f1.(1ul) +. u64 0x3ffffff -. f2.(1ul);
  out.(2ul) <- f1.(2ul) +. u64 0x3ffffff -. f2.(2ul);
  out.(3ul) <- f1.(3ul) +. u64 0x3ffffff -. f2.(3ul);
  out.(4ul) <- f1.(4ul) +. u64 0x3ffffff -. f2.(4ul);
  out.(5ul) <- f1.(5ul) +. u64 0x3ffffff -. f2.(5ul);
  out.(6ul) <- f1.(6ul) +. u64 0x3ffffff -. f2.(6ul);
  out.(7ul) <- f1.(7ul) +. u64 0x3ffffff -. f2.(7ul);
  out.(8ul) <- f1.(8ul) +. u64 0x3ffffff -. f2.(8ul);
  out.(9ul) <- f1.(9ul) +. u64 0x1fffff -. f2.(9ul)

inline_for_extraction
let smul10 u1 (f2 : felem10) = 
  let (f20,f21,f22,f23,f24,f25,f26,f27,f28,f29) = f2 in
  (u1 *. f20,
   u1 *. f21,
   u1 *. f22,
   u1 *. f23,
   u1 *. f24,
   u1 *. f25,
   u1 *. f26,
   u1 *. f27,
   u1 *. f28,
   u1 *. f29)

inline_for_extraction
let smul_add10 u0 (f1:felem10) (f2 : felem10) = 
  let (f10,f11,f12,f13,f14,f15,f16,f17,f18,f19) = f1 in
  let (f20,f21,f22,f23,f24,f25,f26,f27,f28,f29) = f2 in
  (u0 *. f10 +. f20,
   u0 *. f11 +. f21,
   u0 *. f12 +. f22,
   u0 *. f13 +. f23,
   u0 *. f14 +. f24,
   u0 *. f15 +. f25,
   u0 *. f16 +. f26,
   u0 *. f17 +. f27,
   u0 *. f18 +. f28,
   u0 *. f19 +. f29)


inline_for_extraction
let mul10 (f1:felem10) (f2 : felem10) = 
  let (f10,f11,f12,f13,f14,f15,f16,f17,f18,f19) = f1 in
  let (f20,f21,f22,f23,f24,f25,f26,f27,f28,f29) = f2 in
  let u19_32 = u64 19 <<. 5ul in
  let f2_19 = smul10 u19_32 f2 in
  let (p20,p21,p22,p23,p24,p25,p26,p27,p28,p29) = f2_19 in
  let acc = smul10 f10 f2 in
  let f2_1 = (p29,f20,f21,f22,f23,f24,f25,f26,f27,f28) in
  let acc = smul_add10 f11 f2_1 acc in
  let f2_2 = (p28,p29,f20,f21,f22,f23,f24,f25,f26,f27) in
  let acc = smul_add10 f12 f2_2 acc in
  let f2_3 = (p27,p28,p29,f20,f21,f22,f23,f24,f25,f26) in
  let acc = smul_add10 f13 f2_3 acc in
  let f2_4 = (p26,p27,p28,p29,f20,f21,f22,f23,f24,f25) in
  let acc = smul_add10 f14 f2_4 acc in
  let f2_5 = (p25,p26,p27,p28,p29,f20,f21,f22,f23,f24) in
  let acc = smul_add10 f15 f2_5 acc in
  let f2_6 = (p24,p25,p26,p27,p28,p29,f20,f21,f22,f23) in
  let acc = smul_add10 f16 f2_6 acc in
  let f2_7 = (p23,p24,p25,p26,p27,p28,p29,f20,f21,f22) in
  let acc = smul_add10 f17 f2_7 acc in
  let f2_8 = (p22,p23,p24,p25,p26,p27,p28,p29,f20,f21) in
  let acc = smul_add10 f18 f2_8 acc in
  let f2_9 = (p21,p22,p23,p24,p25,p26,p27,p28,p29,f20) in
  let acc = smul_add10 f19 f2_9 acc in
  acc  

inline_for_extraction
let carry26 (l:uint64) (cin:uint64) =
  let l' = l +. cin in
  [@inline_let]
  let l0 = l' &. u64 0x3ffffff in
  [@inline_let]
  let l1 = l' >>. 26ul in
  (l0, l1)

inline_for_extraction
let carry21 (l:uint64) (cin:uint64) =
  let l' = l +. cin in
  [@inline_let]
  let l0 = l' &. u64 0x1fffff in
  [@inline_let]
  let l1 = l' >>. 21ul in
  (l0, l1)

inline_for_extraction
let carry_felem10 (f:felem10) = 
  let (f0,f1,f2,f3,f4,f5,f6,f7,f8,f9) = f in
  let tmp0, c = carry26 f0 (u64 0) in
  let tmp1, c = carry26 f1 c in
  let tmp2, c = carry26 f2 c in
  let tmp3, c = carry26 f3 c in
  let tmp4, c = carry26 f4 c in
  let tmp5, c = carry26 f5 c in
  let tmp6, c = carry26 f6 c in
  let tmp7, c = carry26 f7 c in
  let tmp8, c = carry26 f8 c in
  let tmp9, c = carry21 f9 c in
  let tmp0, c = carry26 tmp0 (c *. u64 19) in
  let tmp1 = tmp1 +. c in
  (tmp0, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9)

inline_for_extraction
let fmul10 (f1:felem10) (f2:felem10) =
  let tmp = mul10 f1 f2 in
  carry_felem10 tmp

[@CInline]
val fmul:
    out:felem
  -> f1:felem
  -> f2:felem
  -> Stack unit
    (requires fun h ->
      live h out /\ live h f1 /\ live h f2)
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1)
[@ CInline]
let fmul out f1 f2 =
  let f10 = f1.(size 0) in
  let f11 = f1.(size 1) in
  let f12 = f1.(size 2) in
  let f13 = f1.(size 3) in
  let f14 = f1.(size 4) in
  let f15 = f1.(size 5) in
  let f16 = f1.(size 6) in
  let f17 = f1.(size 7) in
  let f18 = f1.(size 8) in
  let f19 = f1.(size 9) in

  let f20 = f2.(size 0) in
  let f21 = f2.(size 1) in
  let f22 = f2.(size 2) in
  let f23 = f2.(size 3) in
  let f24 = f2.(size 4) in
  let f25 = f2.(size 5) in
  let f26 = f2.(size 6) in
  let f27 = f2.(size 7) in
  let f28 = f2.(size 8) in
  let f29 = f2.(size 9) in

  let (o0,o1,o2,o3,o4,o5,o6,o7,o8,o9) = 
      fmul10 (f10,f11,f12,f13,f14,f15,f16,f17,f18,f19)
	    (f20,f21,f22,f23,f24,f25,f26,f27,f28,f29) in
  out.(size 0) <- o0;
  out.(size 1) <- o1;
  out.(size 2) <- o2;
  out.(size 3) <- o3;
  out.(size 4) <- o4;
  out.(size 5) <- o5;
  out.(size 6) <- o6;
  out.(size 7) <- o7;
  out.(size 8) <- o8;
  out.(size 9) <- o9

[@ CInline]
val fmul2:
    out:felem2
  -> f1:felem2
  -> f2:felem2
  -> Stack unit
    (requires fun h ->
      live h out /\ live h f1 /\ live h f2)
    (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1)
[@ CInline]
let fmul2 out f1 f2 =
  fmul (sub out 0ul 10ul) (sub f1 0ul 10ul) (sub f2 0ul 10ul);
  fmul (sub out 10ul 10ul) (sub f1 10ul 10ul) (sub f2 10ul 10ul)


[@ CInline]
val fmul1:
    out:felem
  -> f1:felem
  -> f2:uint64
  -> Stack unit
    (requires fun h ->
      live h out /\ live h f1)
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1)
[@ CInline]
let fmul1 out f1 f2 =
  let f10 = f1.(size 0) in
  let f11 = f1.(size 1) in
  let f12 = f1.(size 2) in
  let f13 = f1.(size 3) in
  let f14 = f1.(size 4) in
  let f15 = f1.(size 5) in
  let f16 = f1.(size 6) in
  let f17 = f1.(size 7) in
  let f18 = f1.(size 8) in
  let f19 = f1.(size 9) in
  let o = smul10 f2 (f10,f11,f12,f13,f14,f15,f16,f17,f18,f19) in
  let (o0,o1,o2,o3,o4,o5,o6,o7,o8,o9) = carry_felem10 o in
  out.(size 0) <- o0;
  out.(size 1) <- o1;
  out.(size 2) <- o2;
  out.(size 3) <- o3;
  out.(size 4) <- o4;
  out.(size 5) <- o5;
  out.(size 6) <- o6;
  out.(size 7) <- o7;
  out.(size 8) <- o8;
  out.(size 9) <- o9


[@ CInline]
val fsqr:
     out:felem
  -> f:felem
  -> Stack unit
    (requires fun h ->
      live h out /\ live h f)
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1)
[@ CInline]
let fsqr out f =
  fmul out f f

[@ CInline]
val fsqr2:
    out:felem2
  -> f:felem2
  -> Stack unit
    (requires fun h ->
      live h out /\ live h f )
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1)
[@ CInline]
let fsqr2 out f =
  fsqr (sub out 0ul 10ul) (sub f 0ul 10ul);
  fsqr (sub out 10ul 10ul) (sub f 10ul 10ul)

inline_for_extraction
val load_felem:
    f:felem
  -> u64s:lbuffer uint64 4ul
  -> Stack unit
    (requires fun h -> live h u64s /\ live h f)
    (ensures  fun h0 _ h1 -> modifies (loc f) h0 h1)
let load_felem f u64s =
  let f0 = u64s.(0ul) &. u64 0x3ffffff in
  let f0h = u64s.(0ul) >>. 26ul in
  let f1 = f0h &. u64 0x3ffffff in
  let f1h = f0h >>. 26ul in
  let f2 = f1h ^. ((u64s.(1ul) &. u64 0x3fff) <<. 12ul) in
  let f2h = u64s.(1ul) >>. 14ul in
  let f3 = f2h &. u64 0x3ffffff in
  let f3h = f2h >>. 26ul in
  let f4 = f3h ^. ((u64s.(2ul) &. u64 3) <<. 24ul) in
  let f4h = u64s.(2ul) >>. 2ul in
  let f5 = f4h &. u64 0x3ffffff in
  let f5h = f4h >>. 26ul in
  let f6 = f5h &. u64 0x3ffffff in
  let f6h = f5h >>. 26ul in
  let f7 = f6h ^. ((u64s.(3ul) &. u64 0xffff) <<. 10ul) in
  let f7h = u64s.(3ul) >>. 16ul in
  let f8 = f7h &. u64 0x3ffffff in
  let f9 = f7h >>. 26ul in
  f.(size 0) <- f0;
  f.(size 1) <- f1;
  f.(size 2) <- f2;
  f.(size 3) <- f3;
  f.(size 4) <- f4;
  f.(size 5) <- f5;
  f.(size 6) <- f6;
  f.(size 7) <- f7;
  f.(size 8) <- f8;
  f.(size 9) <- f9


let uint64_eq_mask (a:uint64) (b:uint64) : uint64 =
  let x = a ^. b in
  let minus_x = (lognot x) +. (u64 1) in
  let x_or_minus_x = x |. minus_x in
  let xnx = x_or_minus_x >>. 63ul in
  let c = xnx -. (u64 1) in
  c

let uint64_gte_mask (a:uint64) (b:uint64) : uint64 =
  let x = a in
  let y = b in
  let x_xor_y = logxor x y in
  let x_sub_y = x -. y in
  let x_sub_y_xor_y = x_sub_y ^. y in
  let q = logor x_xor_y x_sub_y_xor_y in
  let x_xor_q = logxor x q in
  let x_xor_q_ = shift_right x_xor_q 63ul in
  let c = sub_mod x_xor_q_ (u64 1) in
  c

val store_felem:
    u64s:lbuffer uint64 4ul
  -> f:felem
  -> Stack unit
    (requires fun h -> live h f /\ live h u64s)
    (ensures  fun h0 _ h1 -> modifies (loc u64s) h0 h1)
let store_felem u64s f =
  let f0 = f.(size 0) in
  let f1 = f.(size 1) in
  let f2 = f.(size 2) in
  let f3 = f.(size 3) in
  let f4 = f.(size 4) in
  let f5 = f.(size 5) in
  let f6 = f.(size 6) in
  let f7 = f.(size 7) in
  let f8 = f.(size 8) in
  let f9 = f.(size 9) in
  let (f0,f1,f2,f3,f4,f5,f6,f7,f8,f9) = carry_felem10 (f0,f1,f2,f3,f4,f5,f6,f7,f8,f9) in
  let (f0,f1,f2,f3,f4,f5,f6,f7,f8,f9) = carry_felem10 (f0,f1,f2,f3,f4,f5,f6,f7,f8,f9) in

  let mask = uint64_gte_mask f0 (u64 0x3ffffed) in
  let mask = mask &. uint64_eq_mask f1 (u64 0x3ffffff) in
  let mask = mask &. uint64_eq_mask f2 (u64 0x3ffffff) in
  let mask = mask &. uint64_eq_mask f3 (u64 0x3ffffff) in 
  let mask = mask &. uint64_eq_mask f4 (u64 0x3ffffff) in
  let mask = mask &. uint64_eq_mask f5 (u64 0x3ffffff) in
  let mask = mask &. uint64_eq_mask f6 (u64 0x3ffffff) in
  let mask = mask &. uint64_eq_mask f7 (u64 0x3ffffff) in
  let mask = mask &. uint64_eq_mask f8 (u64 0x3ffffff) in
  let mask = mask &. uint64_eq_mask f9 (u64 0x1fffff) in
  let f0 = f0 -. (mask &. u64 0x3ffffed) in
  let f1 = f1 -. (mask &. u64 0x3ffffff) in
  let f2 = f2 -. (mask &. u64 0x3ffffff) in
  let f3 = f3 -. (mask &. u64 0x3ffffff) in
  let f4 = f4 -. (mask &. u64 0x3ffffff) in
  let f5 = f5 -. (mask &. u64 0x3ffffff) in
  let f6 = f6 -. (mask &. u64 0x3ffffff) in
  let f7 = f7 -. (mask &. u64 0x3ffffff) in
  let f8 = f8 -. (mask &. u64 0x3ffffff) in
  let f9 = f9 -. (mask &. u64 0x1fffff) in

  let o0 = f0 ^. (f1 <<. 26ul) ^. (f2 <<. 52ul) in
  let o1 = (f2 >>. 12ul) ^. (f3 <<. 14ul) ^. (f4 <<. 40ul) in
  let o2 = (f4 >>. 24ul) ^. (f5 <<. 2ul) ^. (f6 <<. 28ul) ^. (f7 <<. 54ul) in
  let o3 = (f7 >>. 10ul) ^. (f8 <<. 14ul) ^. (f9 <<. 40ul) in
  u64s.(0ul) <- o0;
  u64s.(1ul) <- o1;
  u64s.(2ul) <- o2;
  u64s.(3ul) <- o3
