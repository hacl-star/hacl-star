module FastMul_helpers

open Words_s
open Types_s
open FStar.Mul
open FStar.Tactics
open CanonCommSemiring

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

let int_canon = fun _ -> canon_semiring int_cr

//let my_bool_to_nat (b:bool) : nat = if b then 1 else 0

//unfold let assert_by_tactic = assert_by_tactic

let simple_helper (a0 b0 b1 a0b0_lo a0b0_hi a0b1_lo a0b1_hi sum:nat64) (overflow:bool) : Lemma
  (requires pow2_64 * a0b0_hi + a0b0_lo == a0 * b0 /\
            pow2_64 * a0b1_hi + a0b1_lo == a0 * b1 /\
            sum == add_wrap (add_wrap a0b1_lo a0b0_hi) 0 /\
            overflow == (a0b1_lo + a0b0_hi >= pow2_64))
  (ensures (let b = b0 + pow2_64 * b1 in
            let overflow_v = if overflow then 1 else 0 in
            a0 * b == a0b0_lo + pow2_64 * sum + pow2_128 * (a0b1_hi + overflow_v)))
  =
  let b = b0 + pow2_64 * b1 in
  let overflow_v = if overflow then 1 else 0 in
  let lhs = a0 * b in
  let rhs = a0b0_lo + pow2_64 * sum + pow2_128 * (a0b1_hi + overflow_v) in
  assert_by_tactic (lhs == rhs)
    int_canon;
  ()

