module Hacl.Spec.BignumQ.Mul

open FStar.Mul
open Lib.IntTypes

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let qelem5 = (uint64 & uint64 & uint64 & uint64 & uint64)
let qelem_wide5 = (uint64 & uint64 & uint64 & uint64 & uint64 & uint64 & uint64 & uint64 & uint64 & uint64)
let qelem_after_mul5 = (uint128 & uint128 & uint128 & uint128 & uint128 & uint128 & uint128 & uint128 & uint128)


inline_for_extraction noextract
val make_m: unit -> m:qelem5
let make_m () =
  let m0 = u64 0x12631a5cf5d3ed in
  let m1 = u64 0xf9dea2f79cd658 in
  let m2 = u64 0x000000000014de in
  let m3 = u64 0x00000000000000 in
  let m4 = u64 0x00000010000000 in
  (m0, m1, m2, m3, m4)


inline_for_extraction noextract
val make_mu: unit -> m:qelem5
let make_mu m =
  let m0 = u64 0x9ce5a30a2c131b in
  let m1 = u64 0x215d086329a7ed in
  let m2 = u64 0xffffffffeb2106 in
  let m3 = u64 0xffffffffffffff in
  let m4 = u64 0x00000fffffffff in
  (m0, m1, m2, m3, m4)


inline_for_extraction noextract
val choose: b:uint64{v b == 0 \/ v b == 1} -> x:qelem5 -> y:qelem5 -> z:qelem5
let choose b (x0, x1, x2, x3, x4) (y0, y1, y2, y3, y4) =
  let mask = b -. u64 1 in
  let z0 = ((y0 ^. x0) &. mask) ^. x0 in
  let z1 = ((y1 ^. x1) &. mask) ^. x1 in
  let z2 = ((y2 ^. x2) &. mask) ^. x2 in
  let z3 = ((y3 ^. x3) &. mask) ^. x3 in
  let z4 = ((y4 ^. x4) &. mask) ^. x4 in
  (z0, z1, z2, z3, z4)


inline_for_extraction noextract
val subm_step: x:uint64 -> y:uint64 -> uint64 & uint64
let subm_step x y =
  let b = (x -. y) >>. 63ul in
  let t = (b <<. 56ul) +. x -. y in
  b, t


inline_for_extraction noextract
val subm_last_step: x:uint64 -> y:uint64 -> uint64 & uint64
let subm_last_step x y =
  let b = (x -. y) >>. 63ul in
  let t = (b <<. 40ul) +. x -. y in
  b, t


inline_for_extraction noextract
val sub_mod_264: x:qelem5 -> y:qelem5 -> z:qelem5
let sub_mod_264 (x0, x1, x2, x3, x4) (y0, y1, y2, y3, y4) =
  let (c1, t0) = subm_step x0 y0 in
  let (c2, t1) = subm_step x1 (y1 +. c1) in
  let (c3, t2) = subm_step x2 (y2 +. c2) in
  let (c4, t3) = subm_step x3 (y3 +. c3) in
  let (c5, t4) = subm_last_step x4 (y4 +. c4) in
  (t0, t1, t2, t3, t4)


inline_for_extraction noextract
val subm_conditional: x:qelem5 -> z:qelem5
let subm_conditional (x0, x1, x2, x3, x4) =
  let (y0, y1, y2, y3, y4) = make_m () in
  let (b, t0) = subm_step x0 y0 in
  let (b, t1) = subm_step x1 (y1 +. b) in
  let (b, t2) = subm_step x2 (y2 +. b) in
  let (b, t3) = subm_step x3 (y3 +. b) in
  let (b, t4) = subm_step x4 (y4 +. b) in
  let (z0, z1, z2, z3, z4) = choose b (x0, x1, x2, x3, x4) (t0, t1, t2, t3, t4) in
  (z0, z1, z2, z3, z4)


inline_for_extraction noextract
val carry56: x:uint64 -> uint64 & uint64
let carry56 x =
  let carry = x >>. 56ul in
  let t     = to_u64 x &. u64 0xffffffffffffff in
  carry, t


inline_for_extraction noextract
val carry56_wide: x:uint128 -> uint128 & uint64
let carry56_wide x =
  let carry = x >>. 56ul in
  let t     = to_u64 x &. u64 0xffffffffffffff in
  carry, t


inline_for_extraction noextract
val low_mul_5: x:qelem5 -> y:qelem5 -> z:qelem5
let low_mul_5 (x0, x1, x2, x3, x4) (y0, y1, y2, y3, y4) =
  let xy00 = mul64_wide x0 y0 in
  let xy01 = mul64_wide x0 y1 in
  let xy02 = mul64_wide x0 y2 in
  let xy03 = mul64_wide x0 y3 in
  let xy04 = mul64_wide x0 y4 in
  let xy10 = mul64_wide x1 y0 in
  let xy11 = mul64_wide x1 y1 in
  let xy12 = mul64_wide x1 y2 in
  let xy13 = mul64_wide x1 y3 in
  let xy20 = mul64_wide x2 y0 in
  let xy21 = mul64_wide x2 y1 in
  let xy22 = mul64_wide x2 y2 in
  let xy30 = mul64_wide x3 y0 in
  let xy31 = mul64_wide x3 y1 in
  let xy40 = mul64_wide x4 y0 in


  let (carry, t0) = carry56_wide xy00 in
  let (carry, t1) = carry56_wide (xy01 +. xy10 +. carry) in
  let (carry, t2) = carry56_wide (xy02 +. xy11 +. xy20 +. carry) in
  let (carry, t3) = carry56_wide (xy03 +. xy12 +. xy21 +. xy30 +. carry) in
  let t4 = to_u64 (xy04 +. xy13 +. xy22 +. xy31 +. xy40 +. carry) &. u64 0xffffffffff in //mod40
  (t0, t1, t2, t3, t4)


inline_for_extraction noextract
val mul_5: x:qelem5 -> y:qelem5 -> z:qelem_after_mul5
let mul_5 (x0, x1, x2, x3, x4) (y0, y1, y2, y3, y4) =
  let xy00 = mul64_wide x0 y0 in
  let xy01 = mul64_wide x0 y1 in
  let xy02 = mul64_wide x0 y2 in
  let xy03 = mul64_wide x0 y3 in
  let xy04 = mul64_wide x0 y4 in
  let xy10 = mul64_wide x1 y0 in
  let xy11 = mul64_wide x1 y1 in
  let xy12 = mul64_wide x1 y2 in
  let xy13 = mul64_wide x1 y3 in
  let xy14 = mul64_wide x1 y4 in
  let xy20 = mul64_wide x2 y0 in
  let xy21 = mul64_wide x2 y1 in
  let xy22 = mul64_wide x2 y2 in
  let xy23 = mul64_wide x2 y3 in
  let xy24 = mul64_wide x2 y4 in
  let xy30 = mul64_wide x3 y0 in
  let xy31 = mul64_wide x3 y1 in
  let xy32 = mul64_wide x3 y2 in
  let xy33 = mul64_wide x3 y3 in
  let xy34 = mul64_wide x3 y4 in
  let xy40 = mul64_wide x4 y0 in
  let xy41 = mul64_wide x4 y1 in
  let xy42 = mul64_wide x4 y2 in
  let xy43 = mul64_wide x4 y3 in
  let xy44 = mul64_wide x4 y4 in
  let z0 = xy00 in
  let z1 = xy01 +. xy10 in
  let z2 = xy02 +. xy11 +. xy20 in
  let z3 = xy03 +. xy12 +. xy21 +. xy30 in
  let z4 = xy04 +. xy13 +. xy22 +. xy31 +. xy40 in
  let z5 =         xy14 +. xy23 +. xy32 +. xy41 in
  let z6 =                 xy24 +. xy33 +. xy42 in
  let z7 =                         xy34 +. xy43 in
  let z8 =                                 xy44 in
  (z0, z1, z2, z3, z4, z5, z6, z7, z8)


inline_for_extraction noextract
val carry: qelem_after_mul5 -> qelem_wide5
let carry (z0, z1, z2, z3, z4, z5, z6, z7, z8) =
  let (carry, x0) = carry56_wide z0 in
  let (carry, x1) = carry56_wide (z1 +. carry) in
  let (carry, x2) = carry56_wide (z2 +. carry) in
  let (carry, x3) = carry56_wide (z3 +. carry) in
  let (carry, x4) = carry56_wide (z4 +. carry) in
  let (carry, x5) = carry56_wide (z5 +. carry) in
  let (carry, x6) = carry56_wide (z6 +. carry) in
  let (carry, x7) = carry56_wide (z7 +. carry) in
  let (carry, x8) = carry56_wide (z8 +. carry) in
  let x9 = to_u64 carry in
  (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9)

inline_for_extraction noextract
val mul_carry5: qelem5 -> qelem5 -> qelem_wide5
let mul_carry5 (x0, x1, x2, x3, x4) (y0, y1, y2, y3, y4) =
  let (z0, z1, z2, z3, z4, z5, z6, z7, z8) = mul_5 (x0, x1, x2, x3, x4) (y0, y1, y2, y3, y4) in
  let (r0, r1, r2, r3, r4, r5, r6, r7, r8, r9) = carry (z0, z1, z2, z3, z4, z5, z6, z7, z8) in
  (r0, r1, r2, r3, r4, r5, r6, r7, r8, r9)


inline_for_extraction noextract
val mod_264: qelem_wide5 -> qelem5
let mod_264 (t0, t1, t2, t3, t4, t5, t6, t7, t8, t9) =
  (t0, t1, t2, t3, t4 &. u64 0xffffffffff)


inline_for_extraction noextract
val div_2_24_step: x:uint64 -> y:uint64 -> uint64
let div_2_24_step x y =
  let y' = (y &. u64 0xffffff) <<. 32ul in
  let x' = x >>. 24ul in
  let z = y' |. x' in
  z


inline_for_extraction noextract
val div_248: qelem_wide5 -> qelem5
let div_248 (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) =
  let z0 = div_2_24_step x4 x5 in
  let z1 = div_2_24_step x5 x6 in
  let z2 = div_2_24_step x6 x7 in
  let z3 = div_2_24_step x7 x8 in
  let z4 = div_2_24_step x8 x9 in
  (z0, z1, z2, z3, z4)


inline_for_extraction noextract
val div_2_40_step: x:uint64 -> y:uint64 -> uint64
let div_2_40_step x y =
  let y' = (y &. u64 0xffffffffff) <<. 16ul in
  let x' = x >>. 40ul in
  let z = y' |. x' in
  z


inline_for_extraction noextract
val div_264: qelem_wide5 -> qelem5
let div_264 (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) =
  let z0 = div_2_40_step x4 x5 in
  let z1 = div_2_40_step x5 x6 in
  let z2 = div_2_40_step x6 x7 in
  let z3 = div_2_40_step x7 x8 in
  let z4 = div_2_40_step x8 x9 in
  (z0, z1, z2, z3, z4)


// A = t, L = make_m()
// b = 2^8, k = 32, mu = b^{2*k} / L = make_mu()
inline_for_extraction noextract
val barrett_reduction5: t:qelem_wide5 -> z:qelem5
let barrett_reduction5 (t0, t1, t2, t3, t4, t5, t6, t7, t8, t9) =
  let (m0, m1, m2, m3, m4) = make_m () in
  let (mu0, mu1, mu2, mu3, mu4) = make_mu () in

  let (q0, q1, q2, q3, q4) = div_248 (t0, t1, t2, t3, t4, t5, t6, t7, t8, t9) in
  let (qmu0', qmu1', qmu2', qmu3', qmu4', qmu5', qmu6', qmu7', qmu8', qmu9') = mul_carry5 (q0, q1, q2, q3, q4) (mu0, mu1, mu2, mu3, mu4) in
  let (qdiv0, qdiv1, qdiv2, qdiv3, qdiv4) = div_264 (qmu0', qmu1', qmu2', qmu3', qmu4', qmu5', qmu6', qmu7', qmu8', qmu9') in
  //u = qdiv == (A / b^{k-1}) * mu / b^{k+1} == ((A / 2^248) * mu) / 2^264

  let (r0, r1, r2, r3, r4) = mod_264 (t0, t1, t2, t3, t4, t5, t6, t7, t8, t9) in
  //r == A mod b^{k+1} == A mod 2^264

  let (qmul0, qmul1, qmul2, qmul3, qmul4) = low_mul_5 (qdiv0, qdiv1, qdiv2, qdiv3, qdiv4) (m0, m1, m2, m3, m4) in
  //v == qmul == u * L mod b^{k+1} == u * L mod 2^264

  let (s0, s1, s2, s3, s4) = sub_mod_264 (r0, r1, r2, r3, r4) (qmul0, qmul1, qmul2, qmul3, qmul4) in
  //u == s == (r - v) mod b^{k+1} == (r - v) mod 2^264

  let (o0, o1, o2, o3, o4) = subm_conditional (s0, s1, s2, s3, s4) in
  (o0, o1, o2, o3, o4)


inline_for_extraction noextract
val mul_modq5: qelem5 -> qelem5 -> qelem5
let mul_modq5 (x0, x1, x2, x3, x4) (y0, y1, y2, y3, y4) =
  let (r0, r1, r2, r3, r4, r5, r6, r7, r8, r9) = mul_carry5 (x0, x1, x2, x3, x4) (y0, y1, y2, y3, y4) in
  let (o0, o1, o2, o3, o4) = barrett_reduction5 (r0, r1, r2, r3, r4, r5, r6, r7, r8, r9) in
  (o0, o1, o2, o3, o4)


inline_for_extraction noextract
val add_modq5: x:qelem5 -> y:qelem5 -> z:qelem5
let add_modq5 (x0, x1, x2, x3, x4) (y0, y1, y2, y3, y4) =
  let (carry, x0) = carry56 (x0 +. y0) in
  let (carry, x1) = carry56 (x1 +. y1 +. carry) in
  let (carry, x2) = carry56 (x2 +. y2 +. carry) in
  let (carry, x3) = carry56 (x3 +. y3 +. carry) in
  let x4 = x4 +. y4 +. carry in
  let (o0, o1, o2, o3, o4) = subm_conditional (x0, x1, x2, x3, x4) in
  (o0, o1, o2, o3, o4)
