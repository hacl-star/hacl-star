module Hacl.Spec.Bignum.AddAndMultiply

open FStar.Mul


#set-options "--initial_fuel 0 --max_fuel 0"

inline_for_extraction let p42 : p:pos{p = 0x40000000000} = assert_norm (pow2 42 = 0x40000000000);
  pow2 42
inline_for_extraction let p43 : p:pos{p = 0x80000000000} = assert_norm (pow2 43 = 0x80000000000);
  pow2 43
inline_for_extraction let p44 : p:pos{p = 0x100000000000} = assert_norm (pow2 44 = 0x100000000000);
  pow2 44
inline_for_extraction let p45 : p:pos{p = 0x200000000000} = assert_norm (pow2 45 = 0x200000000000);
  pow2 45
inline_for_extraction let p46 : p:pos{p = 0x400000000000} = assert_norm (pow2 46 = 0x400000000000);
  pow2 46

let red_44 (s:Seq.seq Hacl.UInt64.t{Seq.length s = 3}) =
  Hacl.UInt64.v (Seq.index s 0) < p44 /\ Hacl.UInt64.v (Seq.index s 1) < p44 /\ Hacl.UInt64.v (Seq.index s 2) < p44
let red_45 (s:Seq.seq Hacl.UInt64.t{Seq.length s = 3}) =
  Hacl.UInt64.v (Seq.index s 0) < p45 /\ Hacl.UInt64.v (Seq.index s 1) < p45 /\ Hacl.UInt64.v (Seq.index s 2) < p45
let red_46 (s:Seq.seq Hacl.UInt64.t{Seq.length s = 3}) =
  Hacl.UInt64.v (Seq.index s 0) < p46 /\ Hacl.UInt64.v (Seq.index s 1) < p46 /\ Hacl.UInt64.v (Seq.index s 2) < p46
