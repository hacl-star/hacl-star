module Vale.Def.Words_s
open FStar.Mul

(*
Various representations of words with 2^n bits.

For example, a byte might be represented as a record of 8 bools, a sequence of 8 bools,
or a natural number 0 <= n < 256.  Sequences might be little endian or big endian.
A 32-bit word could be four bytes, 32 bools, or a natural number 0 <= n < 0x100000000.

This library defines various representations and conversions between them.
*)

// Records with up to eight fields, listed in order from least significant to most significant.
// (More than eight fields can be built hierarchically, as in four (four nat8))
type two (a:Type) : Type = { lo:a; hi:a; }
type four (a:Type) : Type = { lo0:a; lo1:a; hi2:a; hi3:a; }
type eight (a:Type) : Type = { lo_0:a; lo_1:a; lo_2:a; lo_3:a; hi_4:a; hi_5:a; hi_6:a; hi_7:a }

unfold let pow2_norm (n:nat) = normalize_term (pow2 n)

unfold let pow2_1 = 0x2
unfold let pow2_2 = 0x4
unfold let pow2_4 = 0x10
unfold let pow2_8 = 0x100
unfold let pow2_16 = 0x10000
unfold let pow2_32 = 0x100000000
unfold let pow2_64 = 0x10000000000000000
unfold let pow2_128 = 0x100000000000000000000000000000000

let natN (n:nat) = x:nat{x < n}
let nat1 = natN pow2_1
let nat2 = natN pow2_2
let nat4 = natN pow2_4
let nat8 = natN pow2_8
let nat16 = natN pow2_16
let nat32 = natN pow2_32
let nat64 = natN pow2_64
let nat128 = natN pow2_128

// conversion from int to natN, uninterpreted outside 0 <= i < n
val int_to_natN (n:pos) (i:int) : j:natN n{0 <= i /\ i < n ==> i == j}
