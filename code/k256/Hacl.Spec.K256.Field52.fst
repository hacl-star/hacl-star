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
let normalize5 (f0,f1,f2,f3,f4) : felem5 =
  let (t0,t1,t2,t3,t4) = normalize_weak5 (f0,f1,f2,f3,f4) in
  let x, (r0,r1,r2,r3,r4) = minus_x_mul_pow2_256 (t0,t1,t2,t3,t4) in
  let is_ge_p_m = is_felem_ge_prime5 (r0,r1,r2,r3,r4) in // as_nat r >= S.prime
  let m_to_one = is_ge_p_m &. u64 1 in
  let x1 = m_to_one |. x in
  let (s0,s1,s2,s3,s4) = plus_x_mul_pow2_256_minus_prime x1 (r0,r1,r2,r3,r4) in
  let x2, (k0,k1,k2,k3,k4) = minus_x_mul_pow2_256 (s0,s1,s2,s3,s4) in
  (k0,k1,k2,k3,k4)


// TODO
// fsub5
// fmul5
// fsqr5
