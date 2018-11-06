module FastMul_defs

open Words_s
open Types_s
open FStar.Mul

unfold let pow2_192 = 0x1000000000000000000000000000000000000000000000000
let _ = assert_norm (pow2 192 = pow2_192)
unfold let pow2_256 = 0x10000000000000000000000000000000000000000000000000000000000000000
let _ = assert_norm (pow2 256 = pow2_256)
unfold let pow2_320 = 0x100000000000000000000000000000000000000000000000000000000000000000000000000000000
let _ = assert_norm (pow2 320 = pow2_320)
unfold let pow2_384 = 0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
let _ = assert_norm (pow2 384 = pow2_384)
unfold let pow2_448 = 0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
let _ = assert_norm (pow2 448 = pow2_448)
unfold let pow2_512 = 0x100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
let _ = assert_norm (pow2 512 = pow2_512)

let pow2_two (c0 c1:nat) : nat = c0 + pow2_64 * c1
let pow2_three (c0 c1 c2:nat) : nat = pow2_two c0 c1 + pow2_128 * c2
let pow2_four (c0 c1 c2 c3:nat) : nat = pow2_three c0 c1 c2 + pow2_192 * c3
let pow2_five (c0 c1 c2 c3 c4:nat) : nat = pow2_four c0 c1 c2 c3 + pow2_256 * c4
let pow2_six (c0 c1 c2 c3 c4 c5:nat) : nat = pow2_five c0 c1 c2 c3 c4 + pow2_320 * c5
let pow2_seven (c0 c1 c2 c3 c4 c5 c6:nat) : nat = pow2_six c0 c1 c2 c3 c4 c5 + pow2_384 * c6
let pow2_eight (c0 c1 c2 c3 c4 c5 c6 c7:nat) : nat = pow2_seven c0 c1 c2 c3 c4 c5 c6 + pow2_448 * c7
let pow2_nine (c0 c1 c2 c3 c4 c5 c6 c7 c8:nat) : nat = pow2_eight c0 c1 c2 c3 c4 c5 c6 c7 + pow2_512 * c8
