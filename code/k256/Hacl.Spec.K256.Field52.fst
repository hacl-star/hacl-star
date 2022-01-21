module Hacl.Spec.K256.Field52

open FStar.Mul
open Lib.IntTypes

module S = Spec.K256

include Hacl.Spec.K256.Field52.Definitions

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let load_felem5 ((s0,s1,s2,s3): felem4) : felem5 =
  let f0 = s0 &. mask52 in
  let f1 = (s0 >>. 52ul) |. ((s1 &. u64 0xffffffffff) <<. 12ul) in
  let f2 = (s1 >>. 40ul) |. ((s2 &. u64 0xfffffff) <<. 24ul) in
  let f3 = (s2 >>. 28ul) |. ((s3 &. u64 0xffff) <<. 36ul) in
  let f4 = s3 >>. 16ul in
  (f0,f1,f2,f3,f4)


inline_for_extraction noextract
let store_felem5 ((f0,f1,f2,f3,f4): felem5) : felem4 =
  let o0 = f0 |. (f1 <<. 52ul) in
  let o1 = (f1 >>. 12ul) |. (f2 <<. 40ul) in
  let o2 = (f2 >>. 24ul) |. (f3 <<. 28ul) in
  let o3 = (f3 >>. 36ul) |. (f4 <<. 16ul) in
  (o0,o1,o2,o3)


inline_for_extraction noextract
let add5 ((a0,a1,a2,a3,a4): felem5) ((b0,b1,b2,b3,b4): felem5) : felem5 =
  let o0 = a0 +. b0 in
  let o1 = a1 +. b1 in
  let o2 = a2 +. b2 in
  let o3 = a3 +. b3 in
  let o4 = a4 +. b4 in
  (o0,o1,o2,o3,o4)


inline_for_extraction noextract
let mul15 ((f0,f1,f2,f3,f4): felem5) (c:uint64) : felem5 =
  let o0 = f0 *. c in
  let o1 = f1 *. c in
  let o2 = f2 *. c in
  let o3 = f3 *. c in
  let o4 = f4 *. c in
  (o0,o1,o2,o3,o4)


inline_for_extraction noextract
let is_felem_zero_vartime5 ((f0,f1,f2,f3,f4): felem5) : bool =
  let open Lib.RawIntTypes in
  u64_to_UInt64 f0 =. 0uL &&
  u64_to_UInt64 f1 =. 0uL &&
  u64_to_UInt64 f2 =. 0uL &&
  u64_to_UInt64 f3 =. 0uL &&
  u64_to_UInt64 f4 =. 0uL


inline_for_extraction noextract
let is_felem_ge_prime_vartime5 ((f0,f1,f2,f3,f4): felem5) : bool =
  let open Lib.RawIntTypes in
  u64_to_UInt64 f0 >=. 0xffffefffffc2fuL &&
  u64_to_UInt64 f1 =. 0xfffffffffffffuL &&
  u64_to_UInt64 f2 =. 0xfffffffffffffuL &&
  u64_to_UInt64 f3 =. 0xfffffffffffffuL &&
  u64_to_UInt64 f4 =. 0xffffffffffffuL


inline_for_extraction noextract
let is_felem_ge_prime5 ((t0,t1,t2,t3,t4): felem5) : uint64 =
  let m4 = eq_mask t4 mask48 in
  let m3 = eq_mask t3 mask52 in
  let m2 = eq_mask t2 mask52 in
  let m1 = eq_mask t1 mask52 in
  let m0 = gte_mask t0 (u64 0xffffefffffc2f) in
  let m = m0 &. m1 &. m2 &. m3 &. m4 in
  m


inline_for_extraction noextract
let is_felem_lt_vartime5 ((a0,a1,a2,a3,a4): felem5) ((b0,b1,b2,b3,b4): felem5) : bool =
  let open Lib.RawIntTypes in
  if u64_to_UInt64 a4 <. u64_to_UInt64 b4 then true
  else begin
    if u64_to_UInt64 a4 >. u64_to_UInt64 b4 then false
    else begin
      if u64_to_UInt64 a3 <. u64_to_UInt64 b3 then true
      else begin
        if u64_to_UInt64 a3 >. u64_to_UInt64 b3 then false
        else begin
          if u64_to_UInt64 a2 <. u64_to_UInt64 b2 then true
          else begin
            if u64_to_UInt64 a2 >. u64_to_UInt64 b2 then false
            else begin
              if u64_to_UInt64 a1 <. u64_to_UInt64 b1 then true
              else begin
                if u64_to_UInt64 a1 >. u64_to_UInt64 b1 then false
                else u64_to_UInt64 a0 <. u64_to_UInt64 b0
              end
            end
          end
        end
      end
    end
  end


inline_for_extraction noextract
let is_felem_lt_prime_minus_order_vartime5 ((f0,f1,f2,f3,f4): felem5) : bool =
  let open Lib.RawIntTypes in
  if u64_to_UInt64 f4 >. 0uL then false
  else begin
    if u64_to_UInt64 f3 >. 0uL then false
    else begin
      if u64_to_UInt64 f2 <. 0x1455123uL then true
      else begin
        if u64_to_UInt64 f2 >. 0x1455123uL then false
        else begin
          if u64_to_UInt64 f1 <. 0x1950b75fc4402uL then true
          else begin
            if u64_to_UInt64 f1 >. 0x1950b75fc4402uL then false
            else u64_to_UInt64 f0 <. 0xda1722fc9baeeuL
          end
        end
      end
    end
  end


inline_for_extraction noextract
let is_felem_eq_vartime5 ((a0,a1,a2,a3,a4): felem5) ((b0,b1,b2,b3,b4): felem5) : bool =
  let open Lib.RawIntTypes in
  u64_to_UInt64 a0 =. u64_to_UInt64 b0 &&
  u64_to_UInt64 a1 =. u64_to_UInt64 b1 &&
  u64_to_UInt64 a2 =. u64_to_UInt64 b2 &&
  u64_to_UInt64 a3 =. u64_to_UInt64 b3 &&
  u64_to_UInt64 a4 =. u64_to_UInt64 b4


inline_for_extraction noextract
let minus_x_mul_pow2_256 ((t0,t1,t2,t3,t4):felem5) : uint64 & felem5 =
  let x = t4 >>. 48ul in let t4 = t4 &. mask48 in
  x, (t0,t1,t2,t3,t4)


inline_for_extraction noextract
let carry_round5 ((t0,t1,t2,t3,t4):felem5) : felem5 =
  let t1 = t1 +. (t0 >>. 52ul) in let t0 = t0 &. mask52 in
  let t2 = t2 +. (t1 >>. 52ul) in let t1 = t1 &. mask52 in
  let t3 = t3 +. (t2 >>. 52ul) in let t2 = t2 &. mask52 in
  let t4 = t4 +. (t3 >>. 52ul) in let t3 = t3 &. mask52 in
  (t0,t1,t2,t3,t4)


inline_for_extraction noextract
let plus_x_mul_pow2_256_minus_prime (x:uint64) ((t0,t1,t2,t3,t4):felem5) : felem5 =
  let t0 = t0 +. x *. u64 0x1000003D1 in
  carry_round5 (t0,t1,t2,t3,t4)


inline_for_extraction noextract
let normalize_weak5 ((t0,t1,t2,t3,t4):felem5) : felem5 =
  let x, (t0,t1,t2,t3,t4) = minus_x_mul_pow2_256 (t0,t1,t2,t3,t4) in
  plus_x_mul_pow2_256_minus_prime x (t0,t1,t2,t3,t4)


inline_for_extraction noextract
let normalize5 ((f0,f1,f2,f3,f4):felem5) : felem5 =
  let (t0,t1,t2,t3,t4) = normalize_weak5 (f0,f1,f2,f3,f4) in
  let x, (r0,r1,r2,r3,r4) = minus_x_mul_pow2_256 (t0,t1,t2,t3,t4) in
  let is_ge_p_m = is_felem_ge_prime5 (r0,r1,r2,r3,r4) in // as_nat r >= S.prime
  let m_to_one = is_ge_p_m &. u64 1 in
  let x1 = m_to_one |. x in
  let (s0,s1,s2,s3,s4) = plus_x_mul_pow2_256_minus_prime x1 (r0,r1,r2,r3,r4) in
  let x2, (k0,k1,k2,k3,k4) = minus_x_mul_pow2_256 (s0,s1,s2,s3,s4) in
  (k0,k1,k2,k3,k4)


inline_for_extraction noextract
let fmul5 ((a0,a1,a2,a3,a4):felem5) ((b0,b1,b2,b3,b4):felem5) : felem5 =
  let r = u64 0x1000003D10 in

  let d0 = mul64_wide a0 b3
       +. mul64_wide a1 b2
       +. mul64_wide a2 b1
       +. mul64_wide a3 b0 in

  let c0 = mul64_wide a4 b4 in
  let d1 = d0 +. mul64_wide r (to_u64 c0) in let c1 = to_u64 (c0 >>. 64ul) in
  let t3 = to_u64 d1 &. mask52 in let d2 = d1 >>. 52ul in

  let d3 = d2
       +. mul64_wide a0 b4
       +. mul64_wide a1 b3
       +. mul64_wide a2 b2
       +. mul64_wide a3 b1
       +. mul64_wide a4 b0 in

  let d4 = d3 +. mul64_wide (r <<. 12ul) c1 in
  let t4 = to_u64 d4 &. mask52 in let d5 = d4 >>. 52ul in
  let tx = t4 >>. 48ul in let t4' = t4 &. mask48 in

  let c2 = mul64_wide a0 b0 in

  let d6 = d5
       +. mul64_wide a1 b4
       +. mul64_wide a2 b3
       +. mul64_wide a3 b2
       +. mul64_wide a4 b1 in

  let u0 = to_u64 d6 &. mask52 in let d7 = d6 >>. 52ul in
  let u0' = tx |. (u0 <<. 4ul) in
  let c3 = c2 +. mul64_wide u0' (r >>. 4ul) in
  let r0 = to_u64 c3 &. mask52 in let c4 = c3 >>. 52ul in

  let c5 = c4
       +. mul64_wide a0 b1
       +. mul64_wide a1 b0 in

  let d8 = d7
       +. mul64_wide a2 b4
       +. mul64_wide a3 b3
       +. mul64_wide a4 b2 in

  let c6 = c5 +. mul64_wide (to_u64 d8 &. mask52) r in let d9 = d8 >>. 52ul in
  let r1 = to_u64 c6 &. mask52 in let c7 = c6 >>. 52ul in

  let c8 = c7
       +. mul64_wide a0 b2
       +. mul64_wide a1 b1
       +. mul64_wide a2 b0 in

  let d10 = d9
       +. mul64_wide a3 b4
       +. mul64_wide a4 b3 in

  let c9 = c8 +. mul64_wide r (to_u64 d10) in let d11 = to_u64 (d10 >>. 64ul) in
  let r2 = to_u64 c9 &. mask52 in let c10 = c9 >>. 52ul in
  let c11 = c10 +. mul64_wide (r <<. 12ul) d11 +. to_u128 t3 in
  let r3 = to_u64 c11 &. mask52 in let c12 = to_u64 (c11 >>. 52ul) in
  let r4 = c12 +. t4' in
  (r0,r1,r2,r3,r4)


inline_for_extraction noextract
let fsqr5 ((a0,a1,a2,a3,a4):felem5) : felem5 =
  let r = u64 0x1000003D10 in

  let d0 = mul64_wide (a0 *. u64 2) a3 +. mul64_wide (a1 *. u64 2) a2 in
  let c0 = mul64_wide a4 a4 in
  let d1 = d0 +. mul64_wide r (to_u64 c0) in let c1 = to_u64 (c0 >>. 64ul) in
  let t3 = to_u64 d1 &. mask52 in let d2 = d1 >>. 52ul in
  let a4 = a4 *. u64 2 in
  let d3 = d2 +. mul64_wide a0 a4 +. mul64_wide (a1 *. u64 2) a3 +. mul64_wide a2 a2 in
  let d4 = d3 +. mul64_wide (r <<. 12ul) c1 in
  let t4 = to_u64 d4 &. mask52 in let d5 = d4 >>. 52ul in
  let tx = t4 >>. 48ul in let t4' = t4 &. mask48 in
  let c2 = mul64_wide a0 a0 in
  let d6 = d5 +. mul64_wide a1 a4 +. mul64_wide (a2 *. u64 2) a3 in
  let u0 = to_u64 d6 &. mask52 in let d7 = d6 >>. 52ul in
  let u0' = tx |. (u0 <<. 4ul) in
  let c3 = c2 +. mul64_wide u0' (r >>. 4ul) in
  let r0 = to_u64 c3 &. mask52 in let c4 = c3 >>. 52ul in
  let a0 = a0 *. u64 2 in
  let c5 = c4 +. mul64_wide a0 a1 in
  let d8 = d7 +. mul64_wide a2 a4 +. mul64_wide a3 a3 in
  let c6 = c5 +. mul64_wide (to_u64 d8 &. mask52) r in let d9 = d8 >>. 52ul in
  let r1 = to_u64 c6 &. mask52 in let c7 = c6 >>. 52ul in
  let c8 = c7 +. mul64_wide a0 a2 +. mul64_wide a1 a1 in
  let d10 = d9 +. mul64_wide a3 a4 in
  let c9 = c8 +. mul64_wide r (to_u64 d10) in let d11 = to_u64 (d10 >>. 64ul) in
  let r2 = to_u64 c9 &. mask52 in let c10 = c9 >>. 52ul in
  let c11 = c10 +. mul64_wide (r <<. 12ul) d11 +. to_u128 t3 in
  let r3 = to_u64 c11 &. mask52 in let c12 = to_u64 (c11 >>. 52ul) in
  let r4 = c12 +. t4' in
  (r0,r1,r2,r3,r4)


inline_for_extraction noextract
let fnegate5 ((a0,a1,a2,a3,a4):felem5) (m:uint64) : felem5 =
  let r0 = u64 0xffffefffffc2f *. u64 2 *. m -. a0 in
  let r1 = u64 0xfffffffffffff *. u64 2 *. m -. a1 in
  let r2 = u64 0xfffffffffffff *. u64 2 *. m -. a2 in
  let r3 = u64 0xfffffffffffff *. u64 2 *. m -. a3 in
  let r4 = u64 0xffffffffffff *. u64 2 *. m -. a4 in
  (r0,r1,r2,r3,r4)


// inline_for_extraction noextract
// let fadd_x_primes ((a0,a1,a2,a3,a4):felem5) (x:uint64) : felem5 =
//   let r0 = u64 0xffffefffffc2f *. x +. a0 in
//   let r1 = u64 0xfffffffffffff *. x +. a1 in
//   let r2 = u64 0xfffffffffffff *. x +. a2 in
//   let r3 = u64 0xfffffffffffff *. x +. a3 in
//   let r4 = u64 0xffffffffffff *. x +. a4 in
//   (r0,r1,r2,r3,r4)


// inline_for_extraction noextract
// let fsub5 ((a0,a1,a2,a3,a4):felem5) ((b0,b1,b2,b3,b4):felem5) (x:uint64) : felem5 =
//   let (r0,r1,r2,r3,r4) = fadd_x_primes (a0,a1,a2,a3,a4) x in
//   let o0 = r0 -. b0 in
//   let o1 = r1 -. b1 in
//   let o2 = r2 -. b2 in
//   let o3 = r3 -. b3 in
//   let o4 = r4 -. b4 in
//   (o0,o1,o2,o3,o4)
