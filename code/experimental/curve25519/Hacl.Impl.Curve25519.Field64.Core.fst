module Hacl.Impl.Curve25519.Field64.Core

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.Sequence
open Lib.IntTypes
open Lib.Buffer
open FStar.Mul
module B = Lib.Buffer

inline_for_extraction
let uint64_eq_mask (a:uint64) (b:uint64) : uint64
  = let x = a ^. b in
    let minus_x = (lognot x) +. (u64 1) in
    let x_or_minus_x = x |. minus_x in
    let xnx = x_or_minus_x >>. 63ul in
    let c = xnx -. (u64 1) in
    c

inline_for_extraction
let uint64_gte_mask (a:uint64) (b:uint64) : uint64
  = let x = a in
    let y = b in
    let x_xor_y = logxor x y in
    let x_sub_y = x -. y in
    let x_sub_y_xor_y = x_sub_y ^. y in
    let q = logor x_xor_y x_sub_y_xor_y in
    let x_xor_q = logxor x q in
    let x_xor_q_ = shift_right x_xor_q 63ul in
    let c = sub_mod x_xor_q_ (u64 1) in
    c


[@CInline]
let addcarry (x:uint64) (y:uint64) (cin:uint64) =
  let res1 = x +. cin in
  let mask = lognot (uint64_gte_mask res1 x) in
  let res2 = res1 +. y in
  let mask = mask |. lognot (uint64_gte_mask res2 res1) in
  let carry = u64 1 &. mask in
  res2, carry

[@CInline]
let subborrow (x:uint64) (y:uint64) (cin:uint64) =
  let res1 = x -. cin in
  let mask = lognot (uint64_gte_mask x res1) in
  let res2 = res1 -. y in
  let mask = mask |. lognot (uint64_gte_mask res1 res2) in
  let carry = u64 1 &. mask in
  res2, carry


inline_for_extraction
let mul64 (x:uint64) (y:uint64) =
  let res = mul64_wide x y in
  (to_u64 res, to_u64 (res >>. 64ul))

[@ CInline]
let add out f1 f2 = 
  let f10 = f1.(0ul) in
  let f20 = f2.(0ul) in
  let f11 = f1.(1ul) in
  let f21 = f2.(1ul) in
  let f12 = f1.(2ul) in
  let f22 = f2.(2ul) in
  let f13 = f1.(3ul) in
  let f23 = f2.(3ul) in
  let (o0,carry) = addcarry f10 f20 (u64 0) in
  let (o1,carry) = addcarry f11 f21 carry in
  let (o2,carry) = addcarry f12 f22 carry in
  let (o3,carry) = addcarry f13 f23 carry in
  out.(0ul) <- o0;
  out.(1ul) <- o1;
  out.(2ul) <- o2;
  out.(3ul) <- o3;
  carry
  

[@ CInline]
let add1 out f1 f2 = 
  let f10 = f1.(0ul) in
  let f11 = f1.(1ul) in
  let f12 = f1.(2ul) in
  let f13 = f1.(3ul) in
  let (o0,carry) = addcarry f10 f2 (u64 0) in
  let (o1,carry) = addcarry f11 (u64 0) carry in
  let (o2,carry) = addcarry f12 (u64 0) carry in
  let (o3,carry) = addcarry f13 (u64 0) carry in
  out.(0ul) <- o0;
  out.(1ul) <- o1;
  out.(2ul) <- o2;
  out.(3ul) <- o3;
  carry


[@ CInline]
let sub out f1 f2 = 
  let f10 = f1.(0ul) in
  let f20 = f2.(0ul) in
  let f11 = f1.(1ul) in
  let f21 = f2.(1ul) in
  let f12 = f1.(2ul) in
  let f22 = f2.(2ul) in
  let f13 = f1.(3ul) in
  let f23 = f2.(3ul) in
  let (o0,carry) = subborrow f10 f20 (u64 0) in
  let (o1,carry) = subborrow f11 f21 carry in
  let (o2,carry) = subborrow f12 f22 carry in
  let (o3,carry) = subborrow f13 f23 carry in
  out.(0ul) <- o0;
  out.(1ul) <- o1;
  out.(2ul) <- o2;
  out.(3ul) <- o3;
  carry


[@ CInline]
let sub1 out f1 f2 = 
  let f10 = f1.(0ul) in
  let f11 = f1.(1ul) in
  let f12 = f1.(2ul) in
  let f13 = f1.(3ul) in
  let (o0,carry) = subborrow f10 f2 (u64 0) in
  let (o1,carry) = subborrow f11 (u64 0) carry in
  let (o2,carry) = subborrow f12 (u64 0) carry in
  let (o3,carry) = subborrow f13 (u64 0) carry in
  out.(0ul) <- o0;
  out.(1ul) <- o1;
  out.(2ul) <- o2;
  out.(3ul) <- o3;
  carry


[@ CInline]
let mul1 out f1 u2 = 
  let f20 = f1.(size 0) in
  let f21 = f1.(size 1) in
  let f22 = f1.(size 2) in
  let f23 = f1.(size 3) in
  let l0,h0 = mul64 u2 f20 in
  let l1,h1 = mul64 u2 f21 in
  let l2,h2 = mul64 u2 f22 in
  let l3,h3 = mul64 u2 f23 in
  let o0 = l0 in
  let o1,carry = addcarry l1 h0 (u64 0) in
  let o2,carry = addcarry l2 h1 carry in
  let o3,carry = addcarry l3 h2 carry in
  let carry = h3 +. carry in
  out.(size 0) <- o0;
  out.(size 1) <- o1;
  out.(size 2) <- o2;
  out.(size 3) <- o3;
  carry

[@ CInline]
let mul1_add out f1 u2 = 
  let o0 = out.(0ul) in
  let o1 = out.(1ul) in
  let o2 = out.(2ul) in
  let o3 = out.(3ul) in
  let o4 = mul1 out f1 u2 in
  let o0,carry = addcarry out.(0ul) o0 (u64 0) in
  let o1,carry = addcarry out.(1ul) o1 carry in
  let o2,carry = addcarry out.(2ul) o2 carry in
  let o3,carry = addcarry out.(3ul) o3 carry in
  out.(size 0) <- o0;
  out.(size 1) <- o1;
  out.(size 2) <- o2;
  out.(size 3) <- o3;
  o4 +. carry

[@ CInline]
let mul out f1 r = 
  let s4 = mul1 (B.sub out 0ul 4ul) r f1.(size 0) in
  out.(4ul) <- s4;
  let s5 = mul1_add (B.sub out 1ul 4ul) r f1.(size 1)  in
  out.(5ul) <- s5;
  let s6 = mul1_add (B.sub out 2ul 4ul) r f1.(size 2) in
  out.(6ul) <- s6;
  let s7 = mul1_add (B.sub out 3ul 4ul) r f1.(size 3) in
  out.(7ul) <- s7

[@ CInline]
let mul2 out f1 f2 = 
  let out1 = B.sub out 0ul 8ul in
  let out2 = B.sub out 8ul 8ul in
  let f10 = B.sub f1 0ul 4ul in
  let f20 = B.sub f2 0ul 4ul in
  let f11 = B.sub f1 4ul 4ul in
  let f21 = B.sub f2 4ul 4ul in
  mul out1 f10 f20;
  mul out2 f11 f21


[@ CInline]
let sqr out f = mul out f f 

[@ CInline]
let sqr2 out f = 
  let out1 = B.sub out 0ul 8ul in
  let out2 = B.sub out 8ul 8ul in
  let f0 = B.sub f 0ul 4ul in
  let f1 = B.sub f 4ul 4ul in
  sqr out1 f0;
  sqr out2 f1
